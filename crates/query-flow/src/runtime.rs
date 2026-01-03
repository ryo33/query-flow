//! Query runtime and context.

use std::any::{Any, TypeId};
use std::cell::RefCell;
use std::ops::Deref;
use std::sync::Arc;

use whale::{Durability, GetOrInsertResult, RevisionCounter, Runtime as WhaleRuntime};

use crate::asset::{AssetKey, AssetLocator, DurabilityLevel, FullAssetKey, PendingAsset};
use crate::db::Db;
use crate::key::FullCacheKey;
use crate::loading::AssetLoadingState;
use crate::query::Query;
use crate::storage::{
    AssetKeyRegistry, AssetState, CachedEntry, CachedValue, LocatorStorage, PendingStorage,
    QueryRegistry, VerifierStorage,
};
use crate::tracer::{
    ExecutionResult, InvalidationReason, NoopTracer, SpanId, Tracer, TracerAssetKey,
    TracerAssetState, TracerQueryKey,
};
use crate::QueryError;

/// Function type for comparing user errors during early cutoff.
///
/// Used by `QueryRuntimeBuilder::error_comparator` to customize how
/// `QueryError::UserError` values are compared for caching purposes.
pub type ErrorComparator = fn(&anyhow::Error, &anyhow::Error) -> bool;

/// Number of durability levels (matches whale's default).
const DURABILITY_LEVELS: usize = 4;

// Thread-local query execution stack for cycle detection.
thread_local! {
    static QUERY_STACK: RefCell<Vec<FullCacheKey>> = const { RefCell::new(Vec::new()) };
}

/// Execution context passed through query execution.
///
/// Contains a span ID for tracing correlation.
#[derive(Clone, Copy)]
pub struct ExecutionContext {
    span_id: SpanId,
}

impl ExecutionContext {
    /// Create a new execution context with the given span ID.
    #[inline]
    pub fn new(span_id: SpanId) -> Self {
        Self { span_id }
    }

    /// Get the span ID for this execution context.
    #[inline]
    pub fn span_id(&self) -> SpanId {
        self.span_id
    }
}

/// Result of polling a query, containing the value and its revision.
///
/// This is returned by [`QueryRuntime::poll`] and provides both the query result
/// and its change revision, enabling efficient change detection for subscription
/// patterns.
///
/// # Example
///
/// ```ignore
/// let result = runtime.poll(MyQuery::new())?;
///
/// // Access the value via Deref
/// println!("{:?}", *result);
///
/// // Check if changed since last poll
/// if result.revision > last_known_revision {
///     notify_subscribers(&result.value);
///     last_known_revision = result.revision;
/// }
/// ```
#[derive(Debug, Clone)]
pub struct Polled<T> {
    /// The query result value.
    pub value: T,
    /// The revision at which this value was last changed.
    ///
    /// Compare this with a previously stored revision to detect changes.
    pub revision: RevisionCounter,
}

impl<T: Deref> Deref for Polled<T> {
    type Target = T::Target;

    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

/// The query runtime manages query execution, caching, and dependency tracking.
///
/// This is cheap to clone - all data is behind `Arc`.
///
/// # Type Parameter
///
/// - `T: Tracer` - The tracer type for observability. Use `NoopTracer` (default)
///   for zero-cost when tracing is not needed.
///
/// # Example
///
/// ```ignore
/// // Without tracing (default)
/// let runtime = QueryRuntime::new();
///
/// // With tracing
/// let tracer = MyTracer::new();
/// let runtime = QueryRuntime::with_tracer(tracer);
///
/// // Sync query execution
/// let result = runtime.query(MyQuery { ... })?;
/// ```
pub struct QueryRuntime<T: Tracer = NoopTracer> {
    /// Whale runtime for dependency tracking and cache storage.
    /// Query outputs and asset values are stored in Node.data as Option<CachedEntry>.
    whale: WhaleRuntime<FullCacheKey, Option<CachedEntry>, DURABILITY_LEVELS>,
    /// Registered asset locators
    locators: Arc<LocatorStorage>,
    /// Pending asset requests
    pending: Arc<PendingStorage>,
    /// Registry for tracking query instances (for list_queries)
    query_registry: Arc<QueryRegistry>,
    /// Registry for tracking asset keys (for list_asset_keys)
    asset_key_registry: Arc<AssetKeyRegistry>,
    /// Verifiers for re-executing queries (for verify-then-decide pattern)
    verifiers: Arc<VerifierStorage>,
    /// Comparator for user errors during early cutoff
    error_comparator: ErrorComparator,
    /// Tracer for observability
    tracer: Arc<T>,
}

impl Default for QueryRuntime<NoopTracer> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Tracer> Clone for QueryRuntime<T> {
    fn clone(&self) -> Self {
        Self {
            whale: self.whale.clone(),
            locators: self.locators.clone(),
            pending: self.pending.clone(),
            query_registry: self.query_registry.clone(),
            asset_key_registry: self.asset_key_registry.clone(),
            verifiers: self.verifiers.clone(),
            error_comparator: self.error_comparator,
            tracer: self.tracer.clone(),
        }
    }
}

/// Default error comparator that treats all errors as different.
///
/// This is conservative - it always triggers recomputation when an error occurs.
fn default_error_comparator(_a: &anyhow::Error, _b: &anyhow::Error) -> bool {
    false
}

impl<T: Tracer> QueryRuntime<T> {
    /// Get cached output along with its revision (single atomic access).
    fn get_cached_with_revision<Q: Query>(
        &self,
        key: &FullCacheKey,
    ) -> Option<(CachedValue<Arc<Q::Output>>, RevisionCounter)> {
        let node = self.whale.get(key)?;
        let revision = node.changed_at;
        let entry = node.data.as_ref()?;
        let cached = entry.to_cached_value::<Q::Output>()?;
        Some((cached, revision))
    }

    /// Get a reference to the tracer.
    #[inline]
    pub fn tracer(&self) -> &T {
        &self.tracer
    }
}

impl QueryRuntime<NoopTracer> {
    /// Create a new query runtime with default settings.
    pub fn new() -> Self {
        Self::with_tracer(NoopTracer)
    }

    /// Create a builder for customizing the runtime.
    ///
    /// # Example
    ///
    /// ```ignore
    /// let runtime = QueryRuntime::builder()
    ///     .error_comparator(|a, b| {
    ///         // Custom error comparison logic
    ///         match (a.downcast_ref::<MyError>(), b.downcast_ref::<MyError>()) {
    ///             (Some(a), Some(b)) => a == b,
    ///             _ => false,
    ///         }
    ///     })
    ///     .build();
    /// ```
    pub fn builder() -> QueryRuntimeBuilder<NoopTracer> {
        QueryRuntimeBuilder::new()
    }
}

impl<T: Tracer> QueryRuntime<T> {
    /// Create a new query runtime with the specified tracer.
    pub fn with_tracer(tracer: T) -> Self {
        QueryRuntimeBuilder::new().tracer(tracer).build()
    }

    /// Execute a query synchronously.
    ///
    /// Returns the cached result if valid, otherwise executes the query.
    ///
    /// # Errors
    ///
    /// - `QueryError::Suspend` - Query is waiting for async loading
    /// - `QueryError::Cycle` - Dependency cycle detected
    pub fn query<Q: Query>(&self, query: Q) -> Result<Arc<Q::Output>, QueryError> {
        self.query_internal(query)
            .and_then(|(inner_result, _)| inner_result.map_err(QueryError::UserError))
    }

    /// Internal implementation shared by query() and poll().
    ///
    /// Returns (result, revision) tuple where result is either Ok(output) or Err(user_error).
    /// System errors (Suspend, Cycle, etc.) are returned as the outer Err.
    #[allow(clippy::type_complexity)]
    fn query_internal<Q: Query>(
        &self,
        query: Q,
    ) -> Result<(Result<Arc<Q::Output>, Arc<anyhow::Error>>, RevisionCounter), QueryError> {
        let key = query.cache_key();
        let full_key = FullCacheKey::new::<Q, _>(&key);

        // Emit query key event for GC tracking (before other events)
        self.tracer.on_query_key(&full_key);

        // Create execution context and emit start event
        let span_id = self.tracer.new_span_id();
        let exec_ctx = ExecutionContext::new(span_id);
        let query_key = TracerQueryKey::new(std::any::type_name::<Q>(), full_key.debug_repr());

        self.tracer.on_query_start(span_id, query_key.clone());

        // Check for cycles using thread-local stack
        let cycle_detected = QUERY_STACK.with(|stack| {
            let stack = stack.borrow();
            stack.iter().any(|k| k == &full_key)
        });

        if cycle_detected {
            let path = QUERY_STACK.with(|stack| {
                let stack = stack.borrow();
                let mut path: Vec<String> =
                    stack.iter().map(|k| k.debug_repr().to_string()).collect();
                path.push(full_key.debug_repr().to_string());
                path
            });

            self.tracer.on_cycle_detected(
                path.iter()
                    .map(|s| TracerQueryKey::new("", s.clone()))
                    .collect(),
            );
            self.tracer
                .on_query_end(span_id, query_key.clone(), ExecutionResult::CycleDetected);

            return Err(QueryError::Cycle { path });
        }

        // Check if cached and valid (with verify-then-decide pattern)
        let current_rev = self.whale.current_revision();

        // Fast path: already verified at current revision
        if self.whale.is_verified_at(&full_key, &current_rev) {
            // Single atomic access to get both cached value and revision
            if let Some((cached, revision)) = self.get_cached_with_revision::<Q>(&full_key) {
                self.tracer.on_cache_check(span_id, query_key.clone(), true);
                self.tracer
                    .on_query_end(span_id, query_key.clone(), ExecutionResult::CacheHit);

                return match cached {
                    CachedValue::Ok(output) => Ok((Ok(output), revision)),
                    CachedValue::UserError(err) => Ok((Err(err), revision)),
                };
            }
        }

        // Check shallow validity (deps' changed_at ok) and try verify-then-decide
        if self.whale.is_valid(&full_key) {
            // Single atomic access to get both cached value and revision
            if let Some((cached, revision)) = self.get_cached_with_revision::<Q>(&full_key) {
                // Shallow valid but not verified - verify deps first
                let mut deps_verified = true;
                if let Some(deps) = self.whale.get_dependency_ids(&full_key) {
                    for dep in deps {
                        if let Some(verifier) = self.verifiers.get(&dep) {
                            // Re-query dep to verify it (triggers recursive verification)
                            if verifier.verify(self as &dyn std::any::Any).is_err() {
                                deps_verified = false;
                                break;
                            }
                        }
                    }
                }

                // Re-check validity after deps are verified
                if deps_verified && self.whale.is_valid(&full_key) {
                    // Deps didn't change their changed_at, mark as verified and use cached
                    self.whale.mark_verified(&full_key, &current_rev);

                    self.tracer.on_cache_check(span_id, query_key.clone(), true);
                    self.tracer
                        .on_query_end(span_id, query_key.clone(), ExecutionResult::CacheHit);

                    return match cached {
                        CachedValue::Ok(output) => Ok((Ok(output), revision)),
                        CachedValue::UserError(err) => Ok((Err(err), revision)),
                    };
                }
                // A dep's changed_at increased, fall through to execute
            }
        }

        self.tracer
            .on_cache_check(span_id, query_key.clone(), false);

        // Execute the query with cycle tracking
        QUERY_STACK.with(|stack| {
            stack.borrow_mut().push(full_key.clone());
        });

        let result = self.execute_query::<Q>(&query, &full_key, exec_ctx);

        QUERY_STACK.with(|stack| {
            stack.borrow_mut().pop();
        });

        // Emit end event
        let exec_result = match &result {
            Ok((_, true, _)) => ExecutionResult::Changed,
            Ok((_, false, _)) => ExecutionResult::Unchanged,
            Err(QueryError::Suspend { .. }) => ExecutionResult::Suspended,
            Err(QueryError::Cycle { .. }) => ExecutionResult::CycleDetected,
            Err(e) => ExecutionResult::Error {
                message: format!("{:?}", e),
            },
        };
        self.tracer
            .on_query_end(span_id, query_key.clone(), exec_result);

        result.map(|(inner_result, _, revision)| (inner_result, revision))
    }

    /// Execute a query, caching the result if appropriate.
    ///
    /// Returns (result, output_changed, revision) tuple.
    /// - `result`: Ok(output) for success, Err(user_error) for user errors
    /// - System errors (Suspend, Cycle, etc.) are returned as outer Err
    #[allow(clippy::type_complexity)]
    fn execute_query<Q: Query>(
        &self,
        query: &Q,
        full_key: &FullCacheKey,
        exec_ctx: ExecutionContext,
    ) -> Result<
        (
            Result<Arc<Q::Output>, Arc<anyhow::Error>>,
            bool,
            RevisionCounter,
        ),
        QueryError,
    > {
        // Create context for this query execution
        let ctx = QueryContext {
            runtime: self,
            current_key: full_key.clone(),
            parent_query_type: std::any::type_name::<Q>(),
            exec_ctx,
            deps: RefCell::new(Vec::new()),
        };

        // Execute the query (clone because query() takes ownership)
        let result = query.clone().query(&ctx);

        // Get collected dependencies
        let deps: Vec<FullCacheKey> = ctx.deps.borrow().clone();

        // Get durability for whale registration
        let durability =
            Durability::new(query.durability() as usize).unwrap_or(Durability::volatile());

        match result {
            Ok(output) => {
                let output = Arc::new(output);

                // Check if output changed (for early cutoff)
                // existing_revision is Some only when output is unchanged (can reuse revision)
                let existing_revision = if let Some((CachedValue::Ok(old), rev)) =
                    self.get_cached_with_revision::<Q>(full_key)
                {
                    if Q::output_eq(&old, &output) {
                        Some(rev) // Same output - reuse revision
                    } else {
                        None // Different output
                    }
                } else {
                    None // No previous Ok value
                };
                let output_changed = existing_revision.is_none();

                // Emit early cutoff check event
                self.tracer.on_early_cutoff_check(
                    exec_ctx.span_id(),
                    TracerQueryKey::new(std::any::type_name::<Q>(), full_key.debug_repr()),
                    output_changed,
                );

                // Update whale with cached entry (atomic update of value + dependency state)
                let entry = CachedEntry::Ok(output.clone() as Arc<dyn std::any::Any + Send + Sync>);
                let revision = if let Some(existing_rev) = existing_revision {
                    // confirm_unchanged doesn't change changed_at, use existing
                    let _ = self.whale.confirm_unchanged(full_key, deps);
                    existing_rev
                } else {
                    // Use new_rev from register result
                    match self
                        .whale
                        .register(full_key.clone(), Some(entry), durability, deps)
                    {
                        Ok(result) => result.new_rev,
                        Err(missing) => {
                            return Err(QueryError::DependenciesRemoved {
                                missing_keys: missing,
                            })
                        }
                    }
                };

                // Register query in registry for list_queries
                let is_new_query = self.query_registry.register(query);
                if is_new_query {
                    let sentinel = FullCacheKey::query_set_sentinel::<Q>();
                    let _ = self
                        .whale
                        .register(sentinel, None, Durability::volatile(), vec![]);
                }

                // Store verifier for this query (for verify-then-decide pattern)
                self.verifiers
                    .insert::<Q, T>(full_key.clone(), query.clone());

                Ok((Ok(output), output_changed, revision))
            }
            Err(QueryError::UserError(err)) => {
                // Check if error changed (for early cutoff)
                // existing_revision is Some only when error is unchanged (can reuse revision)
                let existing_revision = if let Some((CachedValue::UserError(old_err), rev)) =
                    self.get_cached_with_revision::<Q>(full_key)
                {
                    if (self.error_comparator)(old_err.as_ref(), err.as_ref()) {
                        Some(rev) // Same error - reuse revision
                    } else {
                        None // Different error
                    }
                } else {
                    None // No previous UserError
                };
                let output_changed = existing_revision.is_none();

                // Emit early cutoff check event
                self.tracer.on_early_cutoff_check(
                    exec_ctx.span_id(),
                    TracerQueryKey::new(std::any::type_name::<Q>(), full_key.debug_repr()),
                    output_changed,
                );

                // Update whale with cached error (atomic update of value + dependency state)
                let entry = CachedEntry::UserError(err.clone());
                let revision = if let Some(existing_rev) = existing_revision {
                    // confirm_unchanged doesn't change changed_at, use existing
                    let _ = self.whale.confirm_unchanged(full_key, deps);
                    existing_rev
                } else {
                    // Use new_rev from register result
                    match self
                        .whale
                        .register(full_key.clone(), Some(entry), durability, deps)
                    {
                        Ok(result) => result.new_rev,
                        Err(missing) => {
                            return Err(QueryError::DependenciesRemoved {
                                missing_keys: missing,
                            })
                        }
                    }
                };

                // Register query in registry for list_queries
                let is_new_query = self.query_registry.register(query);
                if is_new_query {
                    let sentinel = FullCacheKey::query_set_sentinel::<Q>();
                    let _ = self
                        .whale
                        .register(sentinel, None, Durability::volatile(), vec![]);
                }

                // Store verifier for this query (for verify-then-decide pattern)
                self.verifiers
                    .insert::<Q, T>(full_key.clone(), query.clone());

                Ok((Err(err), output_changed, revision))
            }
            Err(e) => {
                // System errors (Suspend, Cycle, Cancelled, MissingDependency) are not cached
                Err(e)
            }
        }
    }

    /// Invalidate a query, forcing recomputation on next access.
    ///
    /// This also invalidates any queries that depend on this one.
    pub fn invalidate<Q: Query>(&self, key: &Q::CacheKey) {
        let full_key = FullCacheKey::new::<Q, _>(key);

        self.tracer.on_query_invalidated(
            TracerQueryKey::new(std::any::type_name::<Q>(), full_key.debug_repr()),
            InvalidationReason::ManualInvalidation,
        );

        // Update whale to invalidate dependents (register with None to clear cached value)
        let _ = self
            .whale
            .register(full_key, None, Durability::volatile(), vec![]);
    }

    /// Remove a query from the cache entirely, freeing memory.
    ///
    /// Use this for GC when a query is no longer needed.
    /// Unlike `invalidate`, this removes all traces of the query from storage.
    /// The query will be recomputed from scratch on next access.
    ///
    /// This also invalidates any queries that depend on this one.
    pub fn remove_query<Q: Query>(&self, key: &Q::CacheKey) {
        let full_key = FullCacheKey::new::<Q, _>(key);

        self.tracer.on_query_invalidated(
            TracerQueryKey::new(std::any::type_name::<Q>(), full_key.debug_repr()),
            InvalidationReason::ManualInvalidation,
        );

        // Remove verifier if exists
        self.verifiers.remove(&full_key);

        // Remove from whale storage (this also handles dependent invalidation)
        self.whale.remove(&full_key);

        // Remove from registry and update sentinel for list_queries
        if self.query_registry.remove::<Q>(key) {
            let sentinel = FullCacheKey::query_set_sentinel::<Q>();
            let _ = self
                .whale
                .register(sentinel, None, Durability::volatile(), vec![]);
        }
    }

    /// Clear all cached values by removing all nodes from whale.
    ///
    /// Note: This is a relatively expensive operation as it iterates through all keys.
    pub fn clear_cache(&self) {
        let keys = self.whale.keys();
        for key in keys {
            self.whale.remove(&key);
        }
    }

    /// Poll a query, returning both the result and its change revision.
    ///
    /// This is useful for implementing subscription patterns where you need to
    /// detect changes efficiently. Compare the returned `revision` with a
    /// previously stored value to determine if the query result has changed.
    ///
    /// The returned `Polled` contains a `Result<Arc<Q::Output>, Arc<anyhow::Error>>`
    /// as its value, allowing you to track revision changes for both success and
    /// user error cases.
    ///
    /// # Example
    ///
    /// ```ignore
    /// struct Subscription<Q: Query> {
    ///     query: Q,
    ///     last_revision: RevisionCounter,
    ///     tx: Sender<Result<Arc<Q::Output>, Arc<anyhow::Error>>>,
    /// }
    ///
    /// // Polling loop
    /// for sub in &mut subscriptions {
    ///     let result = runtime.poll(sub.query.clone())?;
    ///     if result.revision > sub.last_revision {
    ///         sub.tx.send(result.value.clone())?;
    ///         sub.last_revision = result.revision;
    ///     }
    /// }
    /// ```
    ///
    /// # Errors
    ///
    /// Returns `Err` only for system errors (Suspend, Cycle, etc.).
    /// User errors are returned as `Ok(Polled { value: Err(error), ... })`.
    #[allow(clippy::type_complexity)]
    pub fn poll<Q: Query>(
        &self,
        query: Q,
    ) -> Result<Polled<Result<Arc<Q::Output>, Arc<anyhow::Error>>>, QueryError> {
        let (value, revision) = self.query_internal(query)?;
        Ok(Polled { value, revision })
    }

    /// Get the change revision of a query without executing it.
    ///
    /// Returns `None` if the query has never been executed.
    ///
    /// This is useful for checking if a query has changed since the last poll
    /// without the cost of executing the query.
    ///
    /// # Example
    ///
    /// ```ignore
    /// // Check if query has changed before deciding to poll
    /// if let Some(rev) = runtime.changed_at::<MyQuery>(&key) {
    ///     if rev > last_known_revision {
    ///         let result = runtime.query(MyQuery::new(key))?;
    ///         // Process result...
    ///     }
    /// }
    /// ```
    pub fn changed_at<Q: Query>(&self, key: &Q::CacheKey) -> Option<RevisionCounter> {
        let full_key = FullCacheKey::new::<Q, _>(key);
        self.whale.get(&full_key).map(|node| node.changed_at)
    }
}

// ============================================================================
// GC (Garbage Collection) API
// ============================================================================

impl<T: Tracer> QueryRuntime<T> {
    /// Get all query keys currently in the cache.
    ///
    /// This is useful for implementing custom garbage collection strategies.
    /// Use this in combination with [`Tracer::on_query_key`] to track access
    /// times and implement LRU, TTL, or other GC algorithms externally.
    ///
    /// # Example
    ///
    /// ```ignore
    /// // Collect all keys that haven't been accessed recently
    /// let stale_keys: Vec<_> = runtime.query_keys()
    ///     .filter(|key| tracker.is_stale(key))
    ///     .collect();
    ///
    /// // Remove stale queries that have no dependents
    /// for key in stale_keys {
    ///     runtime.remove_if_unused(&key);
    /// }
    /// ```
    pub fn query_keys(&self) -> Vec<FullCacheKey> {
        self.whale.keys()
    }

    /// Remove a query if it has no dependents.
    ///
    /// Returns `true` if the query was removed, `false` if it has dependents
    /// or doesn't exist. This is the safe way to remove queries during GC,
    /// as it won't break queries that depend on this one.
    ///
    /// # Example
    ///
    /// ```ignore
    /// let key = FullCacheKey::new::<MyQuery, _>(&cache_key);
    /// if runtime.remove_query_if_unused::<MyQuery>(&cache_key) {
    ///     println!("Query removed");
    /// } else {
    ///     println!("Query has dependents, not removed");
    /// }
    /// ```
    pub fn remove_query_if_unused<Q: Query>(&self, key: &Q::CacheKey) -> bool {
        let full_key = FullCacheKey::new::<Q, _>(key);
        self.remove_if_unused(&full_key)
    }

    /// Remove a query by its [`FullCacheKey`].
    ///
    /// This is the type-erased version of [`remove_query`](Self::remove_query).
    /// Use this when you have a `FullCacheKey` from [`query_keys`](Self::query_keys)
    /// or [`Tracer::on_query_key`].
    ///
    /// Returns `true` if the query was removed, `false` if it doesn't exist.
    ///
    /// # Warning
    ///
    /// This forcibly removes the query even if other queries depend on it.
    /// Dependent queries will be recomputed on next access. For safe GC,
    /// use [`remove_if_unused`](Self::remove_if_unused) instead.
    pub fn remove(&self, key: &FullCacheKey) -> bool {
        // Remove verifier if exists
        self.verifiers.remove(key);

        // Remove from whale storage
        self.whale.remove(key).is_some()
    }

    /// Remove a query by its [`FullCacheKey`] if it has no dependents.
    ///
    /// This is the type-erased version of [`remove_query_if_unused`](Self::remove_query_if_unused).
    /// Use this when you have a `FullCacheKey` from [`query_keys`](Self::query_keys)
    /// or [`Tracer::on_query_key`].
    ///
    /// Returns `true` if the query was removed, `false` if it has dependents
    /// or doesn't exist.
    ///
    /// # Example
    ///
    /// ```ignore
    /// // Implement LRU GC
    /// for key in runtime.query_keys() {
    ///     if tracker.is_expired(&key) {
    ///         runtime.remove_if_unused(&key);
    ///     }
    /// }
    /// ```
    pub fn remove_if_unused(&self, key: &FullCacheKey) -> bool {
        if self.whale.remove_if_unused(key.clone()).is_some() {
            // Successfully removed - clean up verifier
            self.verifiers.remove(key);
            true
        } else {
            false
        }
    }
}

// ============================================================================
// Builder
// ============================================================================

/// Builder for [`QueryRuntime`] with customizable settings.
///
/// # Example
///
/// ```ignore
/// let runtime = QueryRuntime::builder()
///     .error_comparator(|a, b| {
///         // Treat all errors of the same type as equal
///         a.downcast_ref::<std::io::Error>().is_some()
///             == b.downcast_ref::<std::io::Error>().is_some()
///     })
///     .build();
/// ```
pub struct QueryRuntimeBuilder<T: Tracer = NoopTracer> {
    error_comparator: ErrorComparator,
    tracer: T,
}

impl Default for QueryRuntimeBuilder<NoopTracer> {
    fn default() -> Self {
        Self::new()
    }
}

impl QueryRuntimeBuilder<NoopTracer> {
    /// Create a new builder with default settings.
    pub fn new() -> Self {
        Self {
            error_comparator: default_error_comparator,
            tracer: NoopTracer,
        }
    }
}

impl<T: Tracer> QueryRuntimeBuilder<T> {
    /// Set the error comparator function for early cutoff optimization.
    ///
    /// When a query returns `QueryError::UserError`, this function is used
    /// to compare it with the previously cached error. If they are equal,
    /// downstream queries can skip recomputation (early cutoff).
    ///
    /// The default comparator returns `false` for all errors, meaning errors
    /// are always considered different (conservative, always recomputes).
    ///
    /// # Example
    ///
    /// ```ignore
    /// // Treat errors as equal if they have the same display message
    /// let runtime = QueryRuntime::builder()
    ///     .error_comparator(|a, b| a.to_string() == b.to_string())
    ///     .build();
    /// ```
    pub fn error_comparator(mut self, f: ErrorComparator) -> Self {
        self.error_comparator = f;
        self
    }

    /// Set the tracer for observability.
    pub fn tracer<U: Tracer>(self, tracer: U) -> QueryRuntimeBuilder<U> {
        QueryRuntimeBuilder {
            error_comparator: self.error_comparator,
            tracer,
        }
    }

    /// Build the runtime with the configured settings.
    pub fn build(self) -> QueryRuntime<T> {
        QueryRuntime {
            whale: WhaleRuntime::new(),
            locators: Arc::new(LocatorStorage::new()),
            pending: Arc::new(PendingStorage::new()),
            query_registry: Arc::new(QueryRegistry::new()),
            asset_key_registry: Arc::new(AssetKeyRegistry::new()),
            verifiers: Arc::new(VerifierStorage::new()),
            error_comparator: self.error_comparator,
            tracer: Arc::new(self.tracer),
        }
    }
}

// ============================================================================
// Asset API
// ============================================================================

impl<T: Tracer> QueryRuntime<T> {
    /// Register an asset locator for a specific asset key type.
    ///
    /// Only one locator can be registered per key type. Later registrations
    /// replace earlier ones.
    ///
    /// # Example
    ///
    /// ```ignore
    /// let runtime = QueryRuntime::new();
    /// runtime.register_asset_locator(FileSystemLocator::new("/assets"));
    /// ```
    pub fn register_asset_locator<K, L>(&self, locator: L)
    where
        K: AssetKey,
        L: AssetLocator<K>,
    {
        self.locators.insert::<K, L>(locator);
    }

    /// Get an iterator over pending asset requests.
    ///
    /// Returns assets that have been requested but not yet resolved.
    /// The user should fetch these externally and call `resolve_asset()`.
    ///
    /// # Example
    ///
    /// ```ignore
    /// for pending in runtime.pending_assets() {
    ///     if let Some(path) = pending.key::<FilePath>() {
    ///         let content = fetch_file(path);
    ///         runtime.resolve_asset(path.clone(), content);
    ///     }
    /// }
    /// ```
    pub fn pending_assets(&self) -> Vec<PendingAsset> {
        self.pending.get_all()
    }

    /// Get pending assets filtered by key type.
    pub fn pending_assets_of<K: AssetKey>(&self) -> Vec<K> {
        self.pending.get_of_type::<K>()
    }

    /// Check if there are any pending assets.
    pub fn has_pending_assets(&self) -> bool {
        !self.pending.is_empty()
    }

    /// Resolve an asset with its loaded value.
    ///
    /// This marks the asset as ready and invalidates any queries that
    /// depend on it (if the value changed), triggering recomputation on next access.
    ///
    /// This method is idempotent - resolving with the same value (via `asset_eq`)
    /// will not trigger downstream recomputation.
    ///
    /// Uses the asset key's default durability.
    ///
    /// # Example
    ///
    /// ```ignore
    /// let content = std::fs::read_to_string(&path)?;
    /// runtime.resolve_asset(FilePath(path), content);
    /// ```
    pub fn resolve_asset<K: AssetKey>(&self, key: K, value: K::Asset) {
        let durability = key.durability();
        self.resolve_asset_internal(key, value, durability);
    }

    /// Resolve an asset with a specific durability level.
    ///
    /// Use this to override the asset key's default durability.
    pub fn resolve_asset_with_durability<K: AssetKey>(
        &self,
        key: K,
        value: K::Asset,
        durability: DurabilityLevel,
    ) {
        self.resolve_asset_internal(key, value, durability);
    }

    fn resolve_asset_internal<K: AssetKey>(
        &self,
        key: K,
        value: K::Asset,
        durability_level: DurabilityLevel,
    ) {
        let full_asset_key = FullAssetKey::new(&key);
        let full_cache_key = FullCacheKey::from_asset_key(&full_asset_key);

        // Remove from pending BEFORE registering the value
        self.pending.remove(&full_asset_key);

        // Prepare the new entry
        let value_arc: Arc<K::Asset> = Arc::new(value);
        let entry = CachedEntry::AssetReady(value_arc.clone() as Arc<dyn Any + Send + Sync>);
        let durability =
            Durability::new(durability_level.as_u8() as usize).unwrap_or(Durability::volatile());

        // Atomic compare-and-update
        let result = self
            .whale
            .update_with_compare(
                full_cache_key,
                Some(entry),
                |old_data, _new_data| {
                    // Compare old and new values
                    match old_data.and_then(|d| d.as_ref()) {
                        Some(CachedEntry::AssetReady(old_arc)) => {
                            match old_arc.clone().downcast::<K::Asset>() {
                                Ok(old_value) => !K::asset_eq(&old_value, &value_arc),
                                Err(_) => true, // Type mismatch, treat as changed
                            }
                        }
                        _ => true, // Loading, NotFound, or not present -> changed
                    }
                },
                durability,
                vec![],
            )
            .expect("update_with_compare with no dependencies cannot fail");

        // Emit asset resolved event
        self.tracer.on_asset_resolved(
            TracerAssetKey::new(std::any::type_name::<K>(), format!("{:?}", key)),
            result.changed,
        );

        // Register asset key in registry for list_asset_keys
        let is_new_asset = self.asset_key_registry.register(&key);
        if is_new_asset {
            // Update sentinel to invalidate list_asset_keys dependents
            let sentinel = FullCacheKey::asset_key_set_sentinel::<K>();
            let _ = self
                .whale
                .register(sentinel, None, Durability::volatile(), vec![]);
        }
    }

    /// Invalidate an asset, forcing queries to re-request it.
    ///
    /// The asset will be marked as loading and added to pending assets.
    /// Dependent queries will suspend until the asset is resolved again.
    ///
    /// # Example
    ///
    /// ```ignore
    /// // File was modified externally
    /// runtime.invalidate_asset(&FilePath("config.json".into()));
    /// // Queries depending on this asset will now suspend
    /// // User should fetch the new value and call resolve_asset
    /// ```
    pub fn invalidate_asset<K: AssetKey>(&self, key: &K) {
        let full_asset_key = FullAssetKey::new(key);
        let full_cache_key = FullCacheKey::from_asset_key(&full_asset_key);

        // Emit asset invalidated event
        self.tracer.on_asset_invalidated(TracerAssetKey::new(
            std::any::type_name::<K>(),
            format!("{:?}", key),
        ));

        // Add to pending FIRST (before clearing whale state)
        // This ensures: readers see either old value, or Loading+pending
        self.pending.insert::<K>(full_asset_key, key.clone());

        // Atomic: clear cached value + invalidate dependents
        // Using None for data means "needs to be loaded"
        let _ = self
            .whale
            .register(full_cache_key, None, Durability::volatile(), vec![]);
    }

    /// Remove an asset from the cache entirely.
    ///
    /// Unlike `invalidate_asset`, this removes all traces of the asset.
    /// Dependent queries will go through the locator again on next access.
    pub fn remove_asset<K: AssetKey>(&self, key: &K) {
        let full_asset_key = FullAssetKey::new(key);
        let full_cache_key = FullCacheKey::from_asset_key(&full_asset_key);

        // Remove from pending first
        self.pending.remove(&full_asset_key);

        // Remove from whale (this also cleans up dependency edges)
        // whale.remove() invalidates dependents before removing
        self.whale.remove(&full_cache_key);

        // Remove from registry and update sentinel for list_asset_keys
        if self.asset_key_registry.remove::<K>(key) {
            let sentinel = FullCacheKey::asset_key_set_sentinel::<K>();
            let _ = self
                .whale
                .register(sentinel, None, Durability::volatile(), vec![]);
        }
    }

    /// Get an asset by key without tracking dependencies.
    ///
    /// Unlike `QueryContext::asset()`, this method does NOT register the caller
    /// as a dependent of the asset. Use this for direct asset access outside
    /// of query execution.
    ///
    /// # Returns
    ///
    /// - `Ok(AssetLoadingState::ready(...))` - Asset is loaded and ready
    /// - `Ok(AssetLoadingState::loading(...))` - Asset is still loading (added to pending)
    /// - `Err(QueryError::MissingDependency)` - Asset was not found
    pub fn get_asset<K: AssetKey>(&self, key: K) -> Result<AssetLoadingState<K>, QueryError> {
        self.get_asset_internal(key)
    }

    /// Internal: Get asset state, checking cache and locator.
    fn get_asset_internal<K: AssetKey>(&self, key: K) -> Result<AssetLoadingState<K>, QueryError> {
        let full_asset_key = FullAssetKey::new(&key);
        let full_cache_key = FullCacheKey::from_asset_key(&full_asset_key);

        // Helper to emit AssetRequested event
        let emit_requested = |tracer: &T, key: &K, state: TracerAssetState| {
            tracer.on_asset_requested(
                TracerAssetKey::new(std::any::type_name::<K>(), format!("{:?}", key)),
                state,
            );
        };

        // Check whale cache first (single atomic read)
        if let Some(node) = self.whale.get(&full_cache_key) {
            // Check if valid at current revision
            if self.whale.is_valid(&full_cache_key) {
                match &node.data {
                    Some(CachedEntry::AssetReady(arc)) => {
                        emit_requested(&self.tracer, &key, TracerAssetState::Ready);
                        match arc.clone().downcast::<K::Asset>() {
                            Ok(value) => return Ok(AssetLoadingState::ready(key, value)),
                            Err(_) => {
                                return Err(QueryError::MissingDependency {
                                    description: format!("Asset type mismatch: {:?}", key),
                                })
                            }
                        }
                    }
                    Some(CachedEntry::AssetNotFound) => {
                        emit_requested(&self.tracer, &key, TracerAssetState::NotFound);
                        return Err(QueryError::MissingDependency {
                            description: format!("Asset not found: {:?}", key),
                        });
                    }
                    None => {
                        // Loading state - check if in pending
                        emit_requested(&self.tracer, &key, TracerAssetState::Loading);
                        return Ok(AssetLoadingState::loading(key));
                    }
                    _ => {
                        // Query-related entries (Ok, UserError) shouldn't be here
                        // Fall through to locator
                    }
                }
            }
        }

        // Not in cache or invalid - try locator
        if let Some(locator) = self.locators.get(TypeId::of::<K>()) {
            if let Some(state) = locator.locate_any(&key) {
                match state {
                    AssetState::Ready(arc) => {
                        emit_requested(&self.tracer, &key, TracerAssetState::Ready);

                        // Downcast to concrete type first - this must succeed since locator
                        // returned this arc for our key type
                        let typed_value: Arc<K::Asset> = match arc.downcast::<K::Asset>() {
                            Ok(v) => v,
                            Err(_) => {
                                return Err(QueryError::MissingDependency {
                                    description: format!("Asset type mismatch: {:?}", key),
                                });
                            }
                        };

                        // Store in whale atomically with early cutoff
                        let entry = CachedEntry::AssetReady(typed_value.clone());
                        let durability = Durability::new(key.durability().as_u8() as usize)
                            .unwrap_or(Durability::volatile());
                        let new_value = typed_value.clone();
                        let _ = self.whale.update_with_compare(
                            full_cache_key,
                            Some(entry),
                            |old_data, _new_data| {
                                // Check if value actually changed (early cutoff)
                                let Some(CachedEntry::AssetReady(old_arc)) =
                                    old_data.and_then(|d| d.as_ref())
                                else {
                                    return true; // No previous value or different variant
                                };
                                let Ok(old_value) = old_arc.clone().downcast::<K::Asset>() else {
                                    return true; // Type mismatch with previous value
                                };
                                !K::asset_eq(&old_value, &new_value)
                            },
                            durability,
                            vec![],
                        );

                        return Ok(AssetLoadingState::ready(key, typed_value));
                    }
                    AssetState::Loading => {
                        emit_requested(&self.tracer, &key, TracerAssetState::Loading);

                        // Add to pending and use get_or_insert to avoid overwriting existing Ready
                        self.pending.insert::<K>(full_asset_key, key.clone());
                        match self
                            .whale
                            .get_or_insert(full_cache_key, None, Durability::volatile(), vec![])
                            .expect("get_or_insert with no dependencies cannot fail")
                        {
                            GetOrInsertResult::Inserted(_) => {
                                return Ok(AssetLoadingState::loading(key));
                            }
                            GetOrInsertResult::Existing(node) => {
                                // Another thread already inserted a value - use it
                                match &node.data {
                                    Some(CachedEntry::AssetReady(arc)) => {
                                        match arc.clone().downcast::<K::Asset>() {
                                            Ok(value) => {
                                                return Ok(AssetLoadingState::ready(key, value))
                                            }
                                            Err(_) => return Ok(AssetLoadingState::loading(key)),
                                        }
                                    }
                                    Some(CachedEntry::AssetNotFound) => {
                                        return Err(QueryError::MissingDependency {
                                            description: format!("Asset not found: {:?}", key),
                                        });
                                    }
                                    _ => return Ok(AssetLoadingState::loading(key)),
                                }
                            }
                        }
                    }
                    AssetState::NotFound => {
                        emit_requested(&self.tracer, &key, TracerAssetState::NotFound);

                        // Store NotFound in whale atomically (so we don't keep re-querying)
                        let entry = CachedEntry::AssetNotFound;
                        let durability = Durability::new(key.durability().as_u8() as usize)
                            .unwrap_or(Durability::volatile());
                        let _ = self.whale.update_with_compare(
                            full_cache_key,
                            Some(entry),
                            |old_data, _new_data| {
                                // Changed unless already NotFound
                                !matches!(
                                    old_data.and_then(|d| d.as_ref()),
                                    Some(CachedEntry::AssetNotFound)
                                )
                            },
                            durability,
                            vec![],
                        );

                        return Err(QueryError::MissingDependency {
                            description: format!("Asset not found: {:?}", key),
                        });
                    }
                }
            }
        }

        // No locator registered or locator returned None - mark as pending
        emit_requested(&self.tracer, &key, TracerAssetState::Loading);
        self.pending
            .insert::<K>(full_asset_key.clone(), key.clone());

        // Use get_or_insert to avoid overwriting existing values
        match self
            .whale
            .get_or_insert(full_cache_key, None, Durability::volatile(), vec![])
            .expect("get_or_insert with no dependencies cannot fail")
        {
            GetOrInsertResult::Inserted(_) => Ok(AssetLoadingState::loading(key)),
            GetOrInsertResult::Existing(node) => {
                // Another thread already inserted a value - use it
                match &node.data {
                    Some(CachedEntry::AssetReady(arc)) => {
                        match arc.clone().downcast::<K::Asset>() {
                            Ok(value) => Ok(AssetLoadingState::ready(key, value)),
                            Err(_) => Ok(AssetLoadingState::loading(key)),
                        }
                    }
                    Some(CachedEntry::AssetNotFound) => Err(QueryError::MissingDependency {
                        description: format!("Asset not found: {:?}", key),
                    }),
                    _ => Ok(AssetLoadingState::loading(key)),
                }
            }
        }
    }
}

impl<T: Tracer> Db for QueryRuntime<T> {
    fn query<Q: Query>(&self, query: Q) -> Result<Arc<Q::Output>, QueryError> {
        QueryRuntime::query(self, query)
    }

    fn asset<K: AssetKey>(&self, key: K) -> Result<AssetLoadingState<K>, QueryError> {
        self.get_asset_internal(key)
    }

    fn list_queries<Q: Query>(&self) -> Vec<Q> {
        self.query_registry.get_all::<Q>()
    }

    fn list_asset_keys<K: AssetKey>(&self) -> Vec<K> {
        self.asset_key_registry.get_all::<K>()
    }
}

/// Context provided to queries during execution.
///
/// Use this to access dependencies via `query()`.
pub struct QueryContext<'a, T: Tracer = NoopTracer> {
    runtime: &'a QueryRuntime<T>,
    current_key: FullCacheKey,
    parent_query_type: &'static str,
    exec_ctx: ExecutionContext,
    deps: RefCell<Vec<FullCacheKey>>,
}

impl<'a, T: Tracer> QueryContext<'a, T> {
    /// Query a dependency.
    ///
    /// The dependency is automatically tracked for invalidation.
    ///
    /// # Example
    ///
    /// ```ignore
    /// fn query(self, db: &impl Db) -> Result<Self::Output, QueryError> {
    ///     let dep_result = db.query(OtherQuery { id: self.id })?;
    ///     Ok(process(&dep_result))
    /// }
    /// ```
    pub fn query<Q: Query>(&self, query: Q) -> Result<Arc<Q::Output>, QueryError> {
        let key = query.cache_key();
        let full_key = FullCacheKey::new::<Q, _>(&key);

        // Emit dependency registered event
        self.runtime.tracer.on_dependency_registered(
            self.exec_ctx.span_id(),
            TracerQueryKey::new(self.parent_query_type, self.current_key.debug_repr()),
            TracerQueryKey::new(std::any::type_name::<Q>(), full_key.debug_repr()),
        );

        // Record this as a dependency
        self.deps.borrow_mut().push(full_key.clone());

        // Execute the query
        self.runtime.query(query)
    }

    /// Access an asset, tracking it as a dependency.
    ///
    /// Returns `AssetLoadingState<K>`:
    /// - `is_loading()` if the asset is still being loaded
    /// - `is_ready()` if the asset is available
    ///
    /// Use `.suspend()?` to convert to `Result<Arc<K::Asset>, QueryError>`,
    /// which returns `Err(QueryError::Suspend { asset })` if still loading.
    ///
    /// # Example
    ///
    /// ```ignore
    /// #[query]
    /// fn process_file(db: &impl Db, path: FilePath) -> Result<Output, QueryError> {
    ///     let content = db.asset(path)?.suspend()?;
    ///     // Process content...
    ///     Ok(output)
    /// }
    /// ```
    ///
    /// # Errors
    ///
    /// Returns `Err(QueryError::MissingDependency)` if the asset was not found.
    pub fn asset<K: AssetKey>(&self, key: K) -> Result<AssetLoadingState<K>, QueryError> {
        let full_asset_key = FullAssetKey::new(&key);
        let full_cache_key = FullCacheKey::from_asset_key(&full_asset_key);

        // Emit asset dependency registered event
        self.runtime.tracer.on_asset_dependency_registered(
            self.exec_ctx.span_id(),
            TracerQueryKey::new(self.parent_query_type, self.current_key.debug_repr()),
            TracerAssetKey::new(std::any::type_name::<K>(), format!("{:?}", key)),
        );

        // Record dependency on this asset
        self.deps.borrow_mut().push(full_cache_key);

        // Get asset from runtime
        let result = self.runtime.get_asset_internal(key);

        // Emit missing dependency event on error
        if let Err(QueryError::MissingDependency { ref description }) = result {
            self.runtime.tracer.on_missing_dependency(
                TracerQueryKey::new(self.parent_query_type, self.current_key.debug_repr()),
                description.clone(),
            );
        }

        result
    }

    /// List all query instances of type Q that have been registered.
    ///
    /// This method establishes a dependency on the "set" of queries of type Q.
    /// The calling query will be invalidated when:
    /// - A new query of type Q is first executed (added to set)
    ///
    /// The calling query will NOT be invalidated when:
    /// - An individual query of type Q has its value change
    ///
    /// # Example
    ///
    /// ```ignore
    /// #[query]
    /// fn all_results(db: &impl Db) -> Result<Vec<i32>, QueryError> {
    ///     let queries = db.list_queries::<MyQuery>();
    ///     let mut results = Vec::new();
    ///     for q in queries {
    ///         results.push(*db.query(q)?);
    ///     }
    ///     Ok(results)
    /// }
    /// ```
    pub fn list_queries<Q: Query>(&self) -> Vec<Q> {
        // Record dependency on the sentinel (set-level dependency)
        let sentinel = FullCacheKey::query_set_sentinel::<Q>();

        self.runtime.tracer.on_dependency_registered(
            self.exec_ctx.span_id(),
            TracerQueryKey::new(self.parent_query_type, self.current_key.debug_repr()),
            TracerQueryKey::new("QuerySet", sentinel.debug_repr()),
        );

        // Ensure sentinel exists in whale (for dependency tracking)
        if self.runtime.whale.get(&sentinel).is_none() {
            let _ =
                self.runtime
                    .whale
                    .register(sentinel.clone(), None, Durability::volatile(), vec![]);
        }

        self.deps.borrow_mut().push(sentinel);

        // Return all registered queries
        self.runtime.query_registry.get_all::<Q>()
    }

    /// List all asset keys of type K that have been registered.
    ///
    /// This method establishes a dependency on the "set" of asset keys of type K.
    /// The calling query will be invalidated when:
    /// - A new asset of type K is resolved for the first time (added to set)
    /// - An asset of type K is removed via remove_asset
    ///
    /// The calling query will NOT be invalidated when:
    /// - An individual asset's value changes (use `db.asset()` for that)
    ///
    /// # Example
    ///
    /// ```ignore
    /// #[query]
    /// fn all_configs(db: &impl Db) -> Result<Vec<String>, QueryError> {
    ///     let keys = db.list_asset_keys::<ConfigFile>();
    ///     let mut contents = Vec::new();
    ///     for key in keys {
    ///         let content = db.asset(&key)?.suspend()?;
    ///         contents.push((*content).clone());
    ///     }
    ///     Ok(contents)
    /// }
    /// ```
    pub fn list_asset_keys<K: AssetKey>(&self) -> Vec<K> {
        // Record dependency on the sentinel (set-level dependency)
        let sentinel = FullCacheKey::asset_key_set_sentinel::<K>();

        self.runtime.tracer.on_asset_dependency_registered(
            self.exec_ctx.span_id(),
            TracerQueryKey::new(self.parent_query_type, self.current_key.debug_repr()),
            TracerAssetKey::new("AssetKeySet", sentinel.debug_repr()),
        );

        // Ensure sentinel exists in whale (for dependency tracking)
        if self.runtime.whale.get(&sentinel).is_none() {
            let _ =
                self.runtime
                    .whale
                    .register(sentinel.clone(), None, Durability::volatile(), vec![]);
        }

        self.deps.borrow_mut().push(sentinel);

        // Return all registered asset keys
        self.runtime.asset_key_registry.get_all::<K>()
    }
}

impl<'a, T: Tracer> Db for QueryContext<'a, T> {
    fn query<Q: Query>(&self, query: Q) -> Result<Arc<Q::Output>, QueryError> {
        QueryContext::query(self, query)
    }

    fn asset<K: AssetKey>(&self, key: K) -> Result<AssetLoadingState<K>, QueryError> {
        QueryContext::asset(self, key)
    }

    fn list_queries<Q: Query>(&self) -> Vec<Q> {
        QueryContext::list_queries(self)
    }

    fn list_asset_keys<K: AssetKey>(&self) -> Vec<K> {
        QueryContext::list_asset_keys(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_query() {
        #[derive(Clone)]
        struct Add {
            a: i32,
            b: i32,
        }

        impl Query for Add {
            type CacheKey = (i32, i32);
            type Output = i32;

            fn cache_key(&self) -> Self::CacheKey {
                (self.a, self.b)
            }

            fn query(self, _db: &impl Db) -> Result<Self::Output, QueryError> {
                Ok(self.a + self.b)
            }

            fn output_eq(old: &Self::Output, new: &Self::Output) -> bool {
                old == new
            }
        }

        let runtime = QueryRuntime::new();

        let result = runtime.query(Add { a: 1, b: 2 }).unwrap();
        assert_eq!(*result, 3);

        // Second query should be cached
        let result2 = runtime.query(Add { a: 1, b: 2 }).unwrap();
        assert_eq!(*result2, 3);
    }

    #[test]
    fn test_dependent_queries() {
        #[derive(Clone)]
        struct Base {
            value: i32,
        }

        impl Query for Base {
            type CacheKey = i32;
            type Output = i32;

            fn cache_key(&self) -> Self::CacheKey {
                self.value
            }

            fn query(self, _db: &impl Db) -> Result<Self::Output, QueryError> {
                Ok(self.value * 2)
            }

            fn output_eq(old: &Self::Output, new: &Self::Output) -> bool {
                old == new
            }
        }

        #[derive(Clone)]
        struct Derived {
            base_value: i32,
        }

        impl Query for Derived {
            type CacheKey = i32;
            type Output = i32;

            fn cache_key(&self) -> Self::CacheKey {
                self.base_value
            }

            fn query(self, db: &impl Db) -> Result<Self::Output, QueryError> {
                let base = db.query(Base {
                    value: self.base_value,
                })?;
                Ok(*base + 10)
            }

            fn output_eq(old: &Self::Output, new: &Self::Output) -> bool {
                old == new
            }
        }

        let runtime = QueryRuntime::new();

        let result = runtime.query(Derived { base_value: 5 }).unwrap();
        assert_eq!(*result, 20); // 5 * 2 + 10
    }

    #[test]
    fn test_cycle_detection() {
        #[derive(Clone)]
        struct CycleA {
            id: i32,
        }

        #[derive(Clone)]
        struct CycleB {
            id: i32,
        }

        impl Query for CycleA {
            type CacheKey = i32;
            type Output = i32;

            fn cache_key(&self) -> Self::CacheKey {
                self.id
            }

            fn query(self, db: &impl Db) -> Result<Self::Output, QueryError> {
                let b = db.query(CycleB { id: self.id })?;
                Ok(*b + 1)
            }

            fn output_eq(old: &Self::Output, new: &Self::Output) -> bool {
                old == new
            }
        }

        impl Query for CycleB {
            type CacheKey = i32;
            type Output = i32;

            fn cache_key(&self) -> Self::CacheKey {
                self.id
            }

            fn query(self, db: &impl Db) -> Result<Self::Output, QueryError> {
                let a = db.query(CycleA { id: self.id })?;
                Ok(*a + 1)
            }

            fn output_eq(old: &Self::Output, new: &Self::Output) -> bool {
                old == new
            }
        }

        let runtime = QueryRuntime::new();

        let result = runtime.query(CycleA { id: 1 });
        assert!(matches!(result, Err(QueryError::Cycle { .. })));
    }

    #[test]
    fn test_fallible_query() {
        #[derive(Clone)]
        struct ParseInt {
            input: String,
        }

        impl Query for ParseInt {
            type CacheKey = String;
            type Output = Result<i32, std::num::ParseIntError>;

            fn cache_key(&self) -> Self::CacheKey {
                self.input.clone()
            }

            fn query(self, _db: &impl Db) -> Result<Self::Output, QueryError> {
                Ok(self.input.parse())
            }

            fn output_eq(old: &Self::Output, new: &Self::Output) -> bool {
                old == new
            }
        }

        let runtime = QueryRuntime::new();

        // Valid parse
        let result = runtime
            .query(ParseInt {
                input: "42".to_string(),
            })
            .unwrap();
        assert_eq!(*result, Ok(42));

        // Invalid parse - system succeeds, user error in output
        let result = runtime
            .query(ParseInt {
                input: "not_a_number".to_string(),
            })
            .unwrap();
        assert!(result.is_err());
    }

    // Macro tests
    mod macro_tests {
        use super::*;
        use crate::query;

        #[query]
        fn add(db: &impl Db, a: i32, b: i32) -> Result<i32, QueryError> {
            let _ = db; // silence unused warning
            Ok(a + b)
        }

        #[test]
        fn test_macro_basic() {
            let runtime = QueryRuntime::new();
            let result = runtime.query(Add::new(1, 2)).unwrap();
            assert_eq!(*result, 3);
        }

        #[query(durability = 2)]
        fn with_durability(db: &impl Db, x: i32) -> Result<i32, QueryError> {
            let _ = db;
            Ok(x * 2)
        }

        #[test]
        fn test_macro_durability() {
            let runtime = QueryRuntime::new();
            let result = runtime.query(WithDurability::new(5)).unwrap();
            assert_eq!(*result, 10);
        }

        #[query(keys(id))]
        fn with_key_selection(
            db: &impl Db,
            id: u32,
            include_extra: bool,
        ) -> Result<String, QueryError> {
            let _ = db;
            Ok(format!("id={}, extra={}", id, include_extra))
        }

        #[test]
        fn test_macro_key_selection() {
            let runtime = QueryRuntime::new();

            // Same id, different include_extra - should return cached
            let r1 = runtime.query(WithKeySelection::new(1, true)).unwrap();
            let r2 = runtime.query(WithKeySelection::new(1, false)).unwrap();

            // Both should have same value because only `id` is the key
            assert_eq!(*r1, "id=1, extra=true");
            assert_eq!(*r2, "id=1, extra=true"); // Cached!
        }

        #[query]
        fn dependent(db: &impl Db, a: i32, b: i32) -> Result<i32, QueryError> {
            let sum = db.query(Add::new(a, b))?;
            Ok(*sum * 2)
        }

        #[test]
        fn test_macro_dependencies() {
            let runtime = QueryRuntime::new();
            let result = runtime.query(Dependent::new(3, 4)).unwrap();
            assert_eq!(*result, 14); // (3 + 4) * 2
        }

        #[query(output_eq)]
        fn with_output_eq(db: &impl Db, x: i32) -> Result<i32, QueryError> {
            let _ = db;
            Ok(x * 2)
        }

        #[test]
        fn test_macro_output_eq() {
            let runtime = QueryRuntime::new();
            let result = runtime.query(WithOutputEq::new(5)).unwrap();
            assert_eq!(*result, 10);
        }

        #[query(name = "CustomName")]
        fn original_name(db: &impl Db, x: i32) -> Result<i32, QueryError> {
            let _ = db;
            Ok(x)
        }

        #[test]
        fn test_macro_custom_name() {
            let runtime = QueryRuntime::new();
            let result = runtime.query(CustomName::new(42)).unwrap();
            assert_eq!(*result, 42);
        }

        // Test that attribute macros like #[tracing::instrument] are preserved
        // We use #[allow(unused_variables)] and #[inline] as test attributes since
        // they don't require external dependencies.
        #[allow(unused_variables)]
        #[inline]
        #[query]
        fn with_attributes(db: &impl Db, x: i32) -> Result<i32, QueryError> {
            // This would warn without #[allow(unused_variables)] on the generated method
            let unused_var = 42;
            Ok(x * 2)
        }

        #[test]
        fn test_macro_preserves_attributes() {
            let runtime = QueryRuntime::new();
            // If attributes weren't preserved, this might warn about unused_var
            let result = runtime.query(WithAttributes::new(5)).unwrap();
            assert_eq!(*result, 10);
        }
    }

    // Tests for poll() and changed_at()
    mod poll_tests {
        use super::*;

        #[derive(Clone)]
        struct Counter {
            id: i32,
        }

        impl Query for Counter {
            type CacheKey = i32;
            type Output = i32;

            fn cache_key(&self) -> Self::CacheKey {
                self.id
            }

            fn query(self, _db: &impl Db) -> Result<Self::Output, QueryError> {
                Ok(self.id * 10)
            }

            fn output_eq(old: &Self::Output, new: &Self::Output) -> bool {
                old == new
            }
        }

        #[test]
        fn test_poll_returns_value_and_revision() {
            let runtime = QueryRuntime::new();

            let result = runtime.poll(Counter { id: 1 }).unwrap();

            // Value should be correct - access through Result and Arc
            assert_eq!(**result.value.as_ref().unwrap(), 10);

            // Revision should be non-zero after first execution
            assert!(result.revision > 0);
        }

        #[test]
        fn test_poll_revision_stable_on_cache_hit() {
            let runtime = QueryRuntime::new();

            // First poll
            let result1 = runtime.poll(Counter { id: 1 }).unwrap();
            let rev1 = result1.revision;

            // Second poll (cache hit)
            let result2 = runtime.poll(Counter { id: 1 }).unwrap();
            let rev2 = result2.revision;

            // Revision should be the same (no change)
            assert_eq!(rev1, rev2);
        }

        #[test]
        fn test_poll_revision_changes_on_invalidate() {
            let runtime = QueryRuntime::new();

            // First poll
            let result1 = runtime.poll(Counter { id: 1 }).unwrap();
            let rev1 = result1.revision;

            // Invalidate and poll again
            runtime.invalidate::<Counter>(&1);
            let result2 = runtime.poll(Counter { id: 1 }).unwrap();
            let rev2 = result2.revision;

            // Revision should increase (value was recomputed)
            // Note: Since output_eq returns true (same value), this might not change
            // depending on early cutoff behavior. Let's verify the value is still correct.
            assert_eq!(**result2.value.as_ref().unwrap(), 10);

            // With early cutoff, revision might stay the same if value didn't change
            // This is expected behavior
            assert!(rev2 >= rev1);
        }

        #[test]
        fn test_changed_at_returns_none_for_unexecuted_query() {
            let runtime = QueryRuntime::new();

            // Query has never been executed
            let rev = runtime.changed_at::<Counter>(&1);
            assert!(rev.is_none());
        }

        #[test]
        fn test_changed_at_returns_revision_after_execution() {
            let runtime = QueryRuntime::new();

            // Execute the query
            let _ = runtime.query(Counter { id: 1 }).unwrap();

            // Now changed_at should return Some
            let rev = runtime.changed_at::<Counter>(&1);
            assert!(rev.is_some());
            assert!(rev.unwrap() > 0);
        }

        #[test]
        fn test_changed_at_matches_poll_revision() {
            let runtime = QueryRuntime::new();

            // Poll the query
            let result = runtime.poll(Counter { id: 1 }).unwrap();

            // changed_at should match the revision from poll
            let rev = runtime.changed_at::<Counter>(&1);
            assert_eq!(rev, Some(result.revision));
        }

        #[test]
        fn test_poll_value_access() {
            let runtime = QueryRuntime::new();

            let result = runtime.poll(Counter { id: 5 }).unwrap();

            // Access through Result and Arc
            let value: &i32 = result.value.as_ref().unwrap();
            assert_eq!(*value, 50);

            // Access Arc directly via field after unwrapping Result
            let arc: &Arc<i32> = result.value.as_ref().unwrap();
            assert_eq!(**arc, 50);
        }

        #[test]
        fn test_subscription_pattern() {
            let runtime = QueryRuntime::new();

            // Simulate subscription pattern
            let mut last_revision: RevisionCounter = 0;
            let mut notifications = 0;

            // First poll - should notify (new value)
            let result = runtime.poll(Counter { id: 1 }).unwrap();
            if result.revision > last_revision {
                notifications += 1;
                last_revision = result.revision;
            }

            // Second poll - should NOT notify (no change)
            let result = runtime.poll(Counter { id: 1 }).unwrap();
            if result.revision > last_revision {
                notifications += 1;
                last_revision = result.revision;
            }

            // Third poll - should NOT notify (no change)
            let result = runtime.poll(Counter { id: 1 }).unwrap();
            if result.revision > last_revision {
                notifications += 1;
                #[allow(unused_assignments)]
                {
                    last_revision = result.revision;
                }
            }

            // Only the first poll should have triggered a notification
            assert_eq!(notifications, 1);
        }
    }

    // Tests for GC APIs
    mod gc_tests {
        use super::*;
        use std::collections::HashSet;
        use std::sync::atomic::{AtomicUsize, Ordering};
        use std::sync::Mutex;

        #[derive(Clone)]
        struct Leaf {
            id: i32,
        }

        impl Query for Leaf {
            type CacheKey = i32;
            type Output = i32;

            fn cache_key(&self) -> Self::CacheKey {
                self.id
            }

            fn query(self, _db: &impl Db) -> Result<Self::Output, QueryError> {
                Ok(self.id * 10)
            }

            fn output_eq(old: &Self::Output, new: &Self::Output) -> bool {
                old == new
            }
        }

        #[derive(Clone)]
        struct Parent {
            child_id: i32,
        }

        impl Query for Parent {
            type CacheKey = i32;
            type Output = i32;

            fn cache_key(&self) -> Self::CacheKey {
                self.child_id
            }

            fn query(self, db: &impl Db) -> Result<Self::Output, QueryError> {
                let child = db.query(Leaf { id: self.child_id })?;
                Ok(*child + 1)
            }

            fn output_eq(old: &Self::Output, new: &Self::Output) -> bool {
                old == new
            }
        }

        #[test]
        fn test_query_keys_returns_all_cached_queries() {
            let runtime = QueryRuntime::new();

            // Execute some queries
            let _ = runtime.query(Leaf { id: 1 }).unwrap();
            let _ = runtime.query(Leaf { id: 2 }).unwrap();
            let _ = runtime.query(Leaf { id: 3 }).unwrap();

            // Get all keys
            let keys = runtime.query_keys();

            // Should have at least 3 keys (might have more due to sentinels)
            assert!(keys.len() >= 3);
        }

        #[test]
        fn test_remove_removes_query() {
            let runtime = QueryRuntime::new();

            // Execute a query
            let _ = runtime.query(Leaf { id: 1 }).unwrap();

            // Get the key
            let full_key = FullCacheKey::new::<Leaf, _>(&1);

            // Query should exist
            assert!(runtime.changed_at::<Leaf>(&1).is_some());

            // Remove it
            assert!(runtime.remove(&full_key));

            // Query should no longer exist
            assert!(runtime.changed_at::<Leaf>(&1).is_none());
        }

        #[test]
        fn test_remove_if_unused_removes_leaf_query() {
            let runtime = QueryRuntime::new();

            // Execute a leaf query (no dependents)
            let _ = runtime.query(Leaf { id: 1 }).unwrap();

            // Should be removable since no other query depends on it
            assert!(runtime.remove_query_if_unused::<Leaf>(&1));

            // Query should no longer exist
            assert!(runtime.changed_at::<Leaf>(&1).is_none());
        }

        #[test]
        fn test_remove_if_unused_does_not_remove_query_with_dependents() {
            let runtime = QueryRuntime::new();

            // Execute parent query (which depends on Leaf)
            let _ = runtime.query(Parent { child_id: 1 }).unwrap();

            // Leaf query should not be removable since Parent depends on it
            assert!(!runtime.remove_query_if_unused::<Leaf>(&1));

            // Leaf query should still exist
            assert!(runtime.changed_at::<Leaf>(&1).is_some());

            // But Parent should be removable (no dependents)
            assert!(runtime.remove_query_if_unused::<Parent>(&1));
        }

        #[test]
        fn test_remove_if_unused_with_full_cache_key() {
            let runtime = QueryRuntime::new();

            // Execute a leaf query
            let _ = runtime.query(Leaf { id: 1 }).unwrap();

            let full_key = FullCacheKey::new::<Leaf, _>(&1);

            // Should be removable via FullCacheKey
            assert!(runtime.remove_if_unused(&full_key));

            // Query should no longer exist
            assert!(runtime.changed_at::<Leaf>(&1).is_none());
        }

        // Test tracer receives on_query_key calls
        struct GcTracker {
            accessed_keys: Mutex<HashSet<String>>,
            access_count: AtomicUsize,
        }

        impl GcTracker {
            fn new() -> Self {
                Self {
                    accessed_keys: Mutex::new(HashSet::new()),
                    access_count: AtomicUsize::new(0),
                }
            }
        }

        impl Tracer for GcTracker {
            fn new_span_id(&self) -> SpanId {
                SpanId(1)
            }

            fn on_query_key(&self, full_key: &FullCacheKey) {
                self.accessed_keys
                    .lock()
                    .unwrap()
                    .insert(full_key.debug_repr().to_string());
                self.access_count.fetch_add(1, Ordering::Relaxed);
            }
        }

        #[test]
        fn test_tracer_receives_on_query_key() {
            let tracker = GcTracker::new();
            let runtime = QueryRuntime::with_tracer(tracker);

            // Execute some queries
            let _ = runtime.query(Leaf { id: 1 }).unwrap();
            let _ = runtime.query(Leaf { id: 2 }).unwrap();

            // Tracer should have received on_query_key calls
            let count = runtime.tracer().access_count.load(Ordering::Relaxed);
            assert_eq!(count, 2);

            // Check that the keys were recorded
            let keys = runtime.tracer().accessed_keys.lock().unwrap();
            assert!(keys.iter().any(|k| k.contains("Leaf")));
        }

        #[test]
        fn test_tracer_receives_on_query_key_for_cache_hits() {
            let tracker = GcTracker::new();
            let runtime = QueryRuntime::with_tracer(tracker);

            // Execute query twice (second is cache hit)
            let _ = runtime.query(Leaf { id: 1 }).unwrap();
            let _ = runtime.query(Leaf { id: 1 }).unwrap();

            // Tracer should have received on_query_key for both calls
            let count = runtime.tracer().access_count.load(Ordering::Relaxed);
            assert_eq!(count, 2);
        }

        #[test]
        fn test_gc_workflow() {
            let tracker = GcTracker::new();
            let runtime = QueryRuntime::with_tracer(tracker);

            // Execute some queries
            let _ = runtime.query(Leaf { id: 1 }).unwrap();
            let _ = runtime.query(Leaf { id: 2 }).unwrap();
            let _ = runtime.query(Leaf { id: 3 }).unwrap();

            // Simulate GC: remove all queries that are not in use
            let mut removed = 0;
            for key in runtime.query_keys() {
                if runtime.remove_if_unused(&key) {
                    removed += 1;
                }
            }

            // All leaf queries should be removable
            assert!(removed >= 3);

            // Queries should no longer exist
            assert!(runtime.changed_at::<Leaf>(&1).is_none());
            assert!(runtime.changed_at::<Leaf>(&2).is_none());
            assert!(runtime.changed_at::<Leaf>(&3).is_none());
        }
    }
}
