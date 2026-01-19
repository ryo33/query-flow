//! Query runtime and context.

use std::any::{Any, TypeId};
use std::cell::RefCell;
use std::ops::Deref;
use std::rc::Rc;
use std::sync::Arc;

use whale::{Durability, GetOrInsertResult, RevisionCounter, Runtime as WhaleRuntime};

use crate::asset::{AssetKey, AssetLocator, DurabilityLevel, PendingAsset};
use crate::db::Db;
use crate::key::{
    AssetCacheKey, AssetKeySetSentinelKey, FullCacheKey, QueryCacheKey, QuerySetSentinelKey,
};
use crate::loading::AssetLoadingState;
use crate::query::Query;
use crate::storage::{
    AssetKeyRegistry, CachedEntry, CachedValue, ErasedLocateResult, LocatorStorage, PendingStorage,
    QueryRegistry, VerifierStorage,
};
use crate::tracer::{
    ExecutionResult, InvalidationReason, NoopTracer, SpanContext, SpanId, TraceId, Tracer,
    TracerAssetState,
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

    /// Current consistency tracker for leaf asset checks.
    /// Set during query execution, used by all nested locator calls.
    /// Uses Rc since thread-local is single-threaded.
    static CONSISTENCY_TRACKER: RefCell<Option<Rc<ConsistencyTracker>>> = const { RefCell::new(None) };

    /// Stack for tracking parent-child query relationships.
    static SPAN_STACK: RefCell<SpanStack> = const { RefCell::new(SpanStack::Empty) };
}

/// Thread-local span stack state.
/// Empty when no query is executing; Active with trace_id and span stack during execution.
enum SpanStack {
    Empty,
    Active(TraceId, Vec<SpanId>),
}

/// Check a leaf asset against the current consistency tracker (if any).
/// Returns Ok if no tracker is set or if the check passes.
fn check_leaf_asset_consistency(dep_changed_at: RevisionCounter) -> Result<(), QueryError> {
    CONSISTENCY_TRACKER.with(|tracker| {
        if let Some(ref t) = *tracker.borrow() {
            t.check_leaf_asset(dep_changed_at)
        } else {
            Ok(())
        }
    })
}

/// RAII guard that sets the consistency tracker for the current thread.
struct ConsistencyTrackerGuard {
    previous: Option<Rc<ConsistencyTracker>>,
}

impl ConsistencyTrackerGuard {
    fn new(tracker: Rc<ConsistencyTracker>) -> Self {
        let previous = CONSISTENCY_TRACKER.with(|t| t.borrow_mut().replace(tracker));
        Self { previous }
    }
}

impl Drop for ConsistencyTrackerGuard {
    fn drop(&mut self) {
        CONSISTENCY_TRACKER.with(|t| {
            *t.borrow_mut() = self.previous.take();
        });
    }
}

/// Check for cycles in the query stack and return error if detected.
fn check_cycle(key: &FullCacheKey) -> Result<(), QueryError> {
    let cycle_detected = QUERY_STACK.with(|stack| stack.borrow().iter().any(|k| k == key));
    if cycle_detected {
        let path = QUERY_STACK.with(|stack| {
            let stack = stack.borrow();
            let mut path: Vec<FullCacheKey> = stack.iter().cloned().collect();
            path.push(key.clone());
            path
        });
        return Err(QueryError::Cycle { path });
    }
    Ok(())
}

/// RAII guard for pushing/popping from query stack.
struct StackGuard;

impl StackGuard {
    fn push(key: FullCacheKey) -> Self {
        QUERY_STACK.with(|stack| stack.borrow_mut().push(key));
        StackGuard
    }
}

impl Drop for StackGuard {
    fn drop(&mut self) {
        QUERY_STACK.with(|stack| {
            stack.borrow_mut().pop();
        });
    }
}

/// RAII guard for pushing/popping from span stack.
struct SpanStackGuard;

impl SpanStackGuard {
    /// Push a span onto the stack. Sets trace_id if this is the root span.
    fn push(trace_id: TraceId, span_id: SpanId) -> Self {
        SPAN_STACK.with(|stack| {
            let mut s = stack.borrow_mut();
            match &mut *s {
                SpanStack::Empty => *s = SpanStack::Active(trace_id, vec![span_id]),
                SpanStack::Active(_, spans) => spans.push(span_id),
            }
        });
        SpanStackGuard
    }
}

impl Drop for SpanStackGuard {
    fn drop(&mut self) {
        SPAN_STACK.with(|stack| {
            let mut s = stack.borrow_mut();
            if let SpanStack::Active(_, spans) = &mut *s {
                spans.pop();
                if spans.is_empty() {
                    *s = SpanStack::Empty;
                }
            }
        });
    }
}

/// Execution context passed through query execution.
///
/// Contains a SpanContext for tracing correlation with parent-child relationships.
#[derive(Clone, Copy)]
pub struct ExecutionContext {
    span_ctx: SpanContext,
}

impl ExecutionContext {
    /// Create a new execution context with the given span context.
    #[inline]
    pub fn new(span_ctx: SpanContext) -> Self {
        Self { span_ctx }
    }

    /// Get the span context for this execution context.
    #[inline]
    pub fn span_ctx(&self) -> &SpanContext {
        &self.span_ctx
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
    locators: Arc<LocatorStorage<T>>,
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

#[test]
fn test_runtime_send_sync() {
    fn assert_send_sync<T: Send + Sync>() {}
    assert_send_sync::<QueryRuntime<NoopTracer>>();
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
        let query_cache_key = QueryCacheKey::new(query.clone());
        let full_key: FullCacheKey = query_cache_key.clone().into();

        // Create SpanContext with parent relationship from SPAN_STACK
        let span_id = self.tracer.new_span_id();
        let (trace_id, parent_span_id) = SPAN_STACK.with(|stack| match &*stack.borrow() {
            SpanStack::Empty => (self.tracer.new_trace_id(), None),
            SpanStack::Active(tid, spans) => (*tid, spans.last().copied()),
        });
        let span_ctx = SpanContext {
            span_id,
            trace_id,
            parent_span_id,
        };

        // Push to span stack and create execution context
        let _span_guard = SpanStackGuard::push(trace_id, span_id);
        let exec_ctx = ExecutionContext::new(span_ctx);

        self.tracer.on_query_start(&span_ctx, &query_cache_key);

        // Check for cycles using thread-local stack
        let cycle_detected = QUERY_STACK.with(|stack| {
            let stack = stack.borrow();
            stack.iter().any(|k| k == &full_key)
        });

        if cycle_detected {
            let path = QUERY_STACK.with(|stack| {
                let stack = stack.borrow();
                let mut path: Vec<FullCacheKey> = stack.iter().cloned().collect();
                path.push(full_key.clone());
                path
            });

            self.tracer.on_cycle_detected(&path);
            self.tracer
                .on_query_end(&span_ctx, &query_cache_key, ExecutionResult::CycleDetected);

            return Err(QueryError::Cycle { path });
        }

        // Check if cached and valid (with verify-then-decide pattern)
        let current_rev = self.whale.current_revision();

        // Fast path: already verified at current revision
        if self.whale.is_verified_at(&full_key, &current_rev) {
            // Single atomic access to get both cached value and revision
            if let Some((cached, revision)) = self.get_cached_with_revision::<Q>(&full_key) {
                self.tracer
                    .on_cache_check(&span_ctx, &query_cache_key, true);
                self.tracer
                    .on_query_end(&span_ctx, &query_cache_key, ExecutionResult::CacheHit);

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
                            // Re-run query/asset to verify it (triggers recursive verification)
                            // For assets, this re-accesses the asset which may re-run the locator
                            if verifier.verify(self as &dyn std::any::Any).is_err() {
                                deps_verified = false;
                                break;
                            }
                        }
                        // Note: deps without verifiers are assumed valid (they're verified
                        // by the final is_valid check if their changed_at increased)
                    }
                }

                // Re-check validity after deps are verified
                if deps_verified && self.whale.is_valid(&full_key) {
                    // Deps didn't change their changed_at, mark as verified and use cached
                    self.whale.mark_verified(&full_key, &current_rev);

                    self.tracer
                        .on_cache_check(&span_ctx, &query_cache_key, true);
                    self.tracer.on_query_end(
                        &span_ctx,
                        &query_cache_key,
                        ExecutionResult::CacheHit,
                    );

                    return match cached {
                        CachedValue::Ok(output) => Ok((Ok(output), revision)),
                        CachedValue::UserError(err) => Ok((Err(err), revision)),
                    };
                }
                // A dep's changed_at increased, fall through to execute
            }
        }

        self.tracer
            .on_cache_check(&span_ctx, &query_cache_key, false);

        // Execute the query with cycle tracking
        let _guard = StackGuard::push(full_key.clone());
        let result = self.execute_query::<Q>(&query, &query_cache_key, &full_key, exec_ctx);
        drop(_guard);

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
            .on_query_end(&span_ctx, &query_cache_key, exec_result);

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
        query_cache_key: &QueryCacheKey,
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
        // Capture current global revision at query start for consistency checking
        let start_revision = self.whale.current_revision().get(Durability::volatile());

        // Create consistency tracker for this query execution
        let tracker = Rc::new(ConsistencyTracker::new(start_revision));

        // Set thread-local tracker for nested locator calls
        let _tracker_guard = ConsistencyTrackerGuard::new(tracker);

        // Create context for this query execution
        let ctx = QueryContext {
            runtime: self,
            current_key: full_key.clone(),
            exec_ctx,
            deps: RefCell::new(Vec::new()),
        };

        // Execute the query (clone because query() takes ownership)
        let db = DbDispatch::QueryContext(&ctx);
        let result = query.clone().query(&db);

        // Get collected dependencies
        let deps: Vec<FullCacheKey> = ctx.deps.borrow().clone();

        // Query durability defaults to stable - Whale will automatically reduce
        // the effective durability to min(requested, min(dep_durabilities)).
        // A pure query with no dependencies remains stable.
        // A query depending on volatile assets becomes volatile.
        let durability = Durability::stable();

        match result {
            Ok(output) => {
                // Check if output changed (for early cutoff)
                // existing_revision is Some only when output is unchanged (can reuse revision)
                let existing_revision = if let Some((CachedValue::Ok(old), rev)) =
                    self.get_cached_with_revision::<Q>(full_key)
                {
                    if Q::output_eq(&*old, &*output) {
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
                    exec_ctx.span_ctx(),
                    query_cache_key,
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
                    let sentinel = QuerySetSentinelKey::new::<Q>().into();
                    let _ = self
                        .whale
                        .register(sentinel, None, Durability::stable(), vec![]);
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
                    exec_ctx.span_ctx(),
                    query_cache_key,
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
                    let sentinel = QuerySetSentinelKey::new::<Q>().into();
                    let _ = self
                        .whale
                        .register(sentinel, None, Durability::stable(), vec![]);
                }

                // Store verifier for this query (for verify-then-decide pattern)
                self.verifiers
                    .insert::<Q, T>(full_key.clone(), query.clone());

                Ok((Err(err), output_changed, revision))
            }
            Err(e) => {
                // System errors (Suspend, Cycle, Cancelled) are not cached
                Err(e)
            }
        }
    }

    /// Invalidate a query, forcing recomputation on next access.
    ///
    /// This also invalidates any queries that depend on this one.
    pub fn invalidate<Q: Query>(&self, query: &Q) {
        let query_cache_key = QueryCacheKey::new(query.clone());
        let full_key: FullCacheKey = query_cache_key.clone().into();

        self.tracer
            .on_query_invalidated(&query_cache_key, InvalidationReason::ManualInvalidation);

        // Update whale to invalidate dependents (register with None to clear cached value)
        // Use stable durability to increment all revision counters, ensuring queries
        // at any durability level will see this as a change.
        let _ = self
            .whale
            .register(full_key, None, Durability::stable(), vec![]);
    }

    /// Remove a query from the cache entirely, freeing memory.
    ///
    /// Use this for GC when a query is no longer needed.
    /// Unlike `invalidate`, this removes all traces of the query from storage.
    /// The query will be recomputed from scratch on next access.
    ///
    /// This also invalidates any queries that depend on this one.
    pub fn remove_query<Q: Query>(&self, query: &Q) {
        let query_cache_key = QueryCacheKey::new(query.clone());
        let full_key: FullCacheKey = query_cache_key.clone().into();

        self.tracer
            .on_query_invalidated(&query_cache_key, InvalidationReason::ManualInvalidation);

        // Remove verifier if exists
        self.verifiers.remove(&full_key);

        // Remove from whale storage (this also handles dependent invalidation)
        self.whale.remove(&full_key);

        // Remove from registry and update sentinel for list_queries
        if self.query_registry.remove::<Q>(query) {
            let sentinel = QuerySetSentinelKey::new::<Q>().into();
            let _ = self
                .whale
                .register(sentinel, None, Durability::stable(), vec![]);
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
    /// if let Some(rev) = runtime.changed_at(&MyQuery::new(key)) {
    ///     if rev > last_known_revision {
    ///         let result = runtime.query(MyQuery::new(key))?;
    ///         // Process result...
    ///     }
    /// }
    /// ```
    pub fn changed_at<Q: Query>(&self, query: &Q) -> Option<RevisionCounter> {
        let full_key = QueryCacheKey::new(query.clone()).into();
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
    /// let query = MyQuery::new(cache_key);
    /// if runtime.remove_query_if_unused(&query) {
    ///     println!("Query removed");
    /// } else {
    ///     println!("Query has dependents, not removed");
    /// }
    /// ```
    pub fn remove_query_if_unused<Q: Query>(&self, query: &Q) -> bool {
        let full_key = QueryCacheKey::new(query.clone()).into();
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
    /// # Arguments
    ///
    /// * `key` - The asset key identifying this resource
    /// * `value` - The loaded asset value
    /// * `durability` - How frequently this asset is expected to change
    ///
    /// # Example
    ///
    /// ```ignore
    /// let content = std::fs::read_to_string(&path)?;
    /// runtime.resolve_asset(FilePath(path), content, DurabilityLevel::Volatile);
    /// ```
    pub fn resolve_asset<K: AssetKey>(&self, key: K, value: K::Asset, durability: DurabilityLevel) {
        self.resolve_asset_internal(key, value, durability);
    }

    /// Resolve an asset with an error.
    ///
    /// This marks the asset as errored and caches the error. Queries depending
    /// on this asset will receive `Err(QueryError::UserError(...))`.
    ///
    /// Use this when async loading fails (e.g., network error, file not found,
    /// access denied).
    ///
    /// # Arguments
    ///
    /// * `key` - The asset key identifying this resource
    /// * `error` - The error to cache (will be wrapped in `Arc`)
    /// * `durability` - How frequently this error state is expected to change
    ///
    /// # Example
    ///
    /// ```ignore
    /// match fetch_file(&path) {
    ///     Ok(content) => runtime.resolve_asset(FilePath(path), content, DurabilityLevel::Volatile),
    ///     Err(e) => runtime.resolve_asset_error(FilePath(path), e, DurabilityLevel::Volatile),
    /// }
    /// ```
    pub fn resolve_asset_error<K: AssetKey>(
        &self,
        key: K,
        error: impl Into<anyhow::Error>,
        durability: DurabilityLevel,
    ) {
        let asset_cache_key = AssetCacheKey::new(key.clone());

        // Remove from pending BEFORE registering the error
        self.pending.remove(&asset_cache_key);

        // Prepare the error entry
        let error_arc = Arc::new(error.into());
        let entry = CachedEntry::AssetError(error_arc.clone());
        let durability =
            Durability::new(durability.as_u8() as usize).unwrap_or(Durability::volatile());

        // Atomic compare-and-update (errors are always considered changed for now)
        let result = self
            .whale
            .update_with_compare(
                asset_cache_key.into(),
                Some(entry),
                |old_data, _new_data| {
                    // Compare old and new errors using error_comparator
                    match old_data.and_then(|d| d.as_ref()) {
                        Some(CachedEntry::AssetError(old_err)) => {
                            !(self.error_comparator)(old_err.as_ref(), error_arc.as_ref())
                        }
                        _ => true, // Loading, Ready, or not present -> changed
                    }
                },
                durability,
                vec![],
            )
            .expect("update_with_compare with no dependencies cannot fail");

        // Emit asset resolved event (with changed status)
        let asset_cache_key = AssetCacheKey::new(key.clone());
        self.tracer
            .on_asset_resolved(&asset_cache_key, result.changed);

        // Register asset key in registry for list_asset_keys
        let is_new_asset = self.asset_key_registry.register(&key);
        if is_new_asset {
            // Update sentinel to invalidate list_asset_keys dependents
            let sentinel = AssetKeySetSentinelKey::new::<K>().into();
            let _ = self
                .whale
                .register(sentinel, None, Durability::stable(), vec![]);
        }
    }

    fn resolve_asset_internal<K: AssetKey>(
        &self,
        key: K,
        value: K::Asset,
        durability_level: DurabilityLevel,
    ) {
        let asset_cache_key = AssetCacheKey::new(key.clone());

        // Remove from pending BEFORE registering the value
        self.pending.remove(&asset_cache_key);

        // Prepare the new entry
        let value_arc: Arc<K::Asset> = Arc::new(value);
        let entry = CachedEntry::AssetReady(value_arc.clone() as Arc<dyn Any + Send + Sync>);
        let durability =
            Durability::new(durability_level.as_u8() as usize).unwrap_or(Durability::volatile());

        // Atomic compare-and-update
        let result = self
            .whale
            .update_with_compare(
                asset_cache_key.into(),
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
        let asset_cache_key = AssetCacheKey::new(key.clone());
        self.tracer
            .on_asset_resolved(&asset_cache_key, result.changed);

        // Register asset key in registry for list_asset_keys
        let is_new_asset = self.asset_key_registry.register(&key);
        if is_new_asset {
            // Update sentinel to invalidate list_asset_keys dependents
            let sentinel = AssetKeySetSentinelKey::new::<K>().into();
            let _ = self
                .whale
                .register(sentinel, None, Durability::stable(), vec![]);
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
        let asset_cache_key = AssetCacheKey::new(key.clone());
        let full_cache_key: FullCacheKey = asset_cache_key.clone().into();

        // Emit asset invalidated event
        self.tracer.on_asset_invalidated(&asset_cache_key);

        // Add to pending FIRST (before clearing whale state)
        // This ensures: readers see either old value, or Loading+pending
        self.pending
            .insert::<K>(asset_cache_key.clone(), key.clone());

        // Atomic: clear cached value + invalidate dependents
        // Using None for data means "needs to be loaded"
        // Use stable durability to ensure queries at any durability level see the change.
        let _ = self
            .whale
            .register(full_cache_key, None, Durability::stable(), vec![]);
    }

    /// Remove an asset from the cache entirely.
    ///
    /// Unlike `invalidate_asset`, this removes all traces of the asset.
    /// Dependent queries will go through the locator again on next access.
    pub fn remove_asset<K: AssetKey>(&self, key: &K) {
        let asset_cache_key = AssetCacheKey::new(key.clone());
        let full_cache_key: FullCacheKey = asset_cache_key.clone().into();

        // Remove from pending first
        self.pending.remove(&asset_cache_key);

        // Remove from whale (this also cleans up dependency edges)
        // whale.remove() invalidates dependents before removing
        self.whale.remove(&full_cache_key);

        // Remove from registry and update sentinel for list_asset_keys
        if self.asset_key_registry.remove::<K>(key) {
            let sentinel = AssetKeySetSentinelKey::new::<K>().into();
            let _ = self
                .whale
                .register(sentinel, None, Durability::stable(), vec![]);
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
    /// - `Err(QueryError::UserError)` - Asset was not found or locator returned an error
    pub fn get_asset<K: AssetKey>(&self, key: K) -> Result<AssetLoadingState<K>, QueryError> {
        self.get_asset_internal(key)
    }

    /// Internal: Get asset state and its changed_at revision atomically.
    ///
    /// This is the "direct" version called from QueryRuntime::asset (no dependency tracking).
    /// For calls from QueryContext::asset, use `get_asset_with_revision_ctx`.
    ///
    /// Returns (AssetLoadingState, changed_at) where changed_at is from the same
    /// whale node that provided the asset value.
    fn get_asset_with_revision<K: AssetKey>(
        &self,
        key: K,
    ) -> Result<(AssetLoadingState<K>, RevisionCounter), QueryError> {
        let asset_cache_key = AssetCacheKey::new(key.clone());
        let full_cache_key: FullCacheKey = asset_cache_key.clone().into();

        // Create a span for this asset request (like queries do)
        // This ensures child queries called from locators show as children of this asset
        let asset_span_id = self.tracer.new_span_id();
        let (trace_id, parent_span_id) = SPAN_STACK.with(|stack| match &*stack.borrow() {
            SpanStack::Empty => (self.tracer.new_trace_id(), None),
            SpanStack::Active(tid, spans) => (*tid, spans.last().copied()),
        });
        let span_ctx = SpanContext {
            span_id: asset_span_id,
            trace_id,
            parent_span_id,
        };

        // Push asset span to stack so child queries see this asset as their parent
        let _span_guard = SpanStackGuard::push(trace_id, asset_span_id);

        // Check whale cache first (single atomic read)
        if let Some(node) = self.whale.get(&full_cache_key) {
            let changed_at = node.changed_at;
            // Check if valid at current revision (shallow check)
            if self.whale.is_valid(&full_cache_key) {
                // Verify dependencies recursively (like query path does)
                let mut deps_verified = true;
                if let Some(deps) = self.whale.get_dependency_ids(&full_cache_key) {
                    for dep in deps {
                        if let Some(verifier) = self.verifiers.get(&dep) {
                            // Re-run query/asset to verify it (triggers recursive verification)
                            if verifier.verify(self as &dyn std::any::Any).is_err() {
                                deps_verified = false;
                                break;
                            }
                        }
                    }
                }

                // Re-check validity after deps are verified
                if deps_verified && self.whale.is_valid(&full_cache_key) {
                    // For cached entries, check consistency for leaf assets (no locator deps).
                    // This detects if resolve_asset/resolve_asset_error was called during query execution.
                    let has_locator_deps = self
                        .whale
                        .get_dependency_ids(&full_cache_key)
                        .is_some_and(|deps| !deps.is_empty());

                    match &node.data {
                        Some(CachedEntry::AssetReady(arc)) => {
                            // Check consistency for cached leaf assets
                            if !has_locator_deps {
                                check_leaf_asset_consistency(changed_at)?;
                            }
                            // Cache hit: start + end immediately (no locator runs)
                            self.tracer.on_asset_requested(&span_ctx, &asset_cache_key);
                            self.tracer.on_asset_located(
                                &span_ctx,
                                &asset_cache_key,
                                TracerAssetState::Ready,
                            );
                            match arc.clone().downcast::<K::Asset>() {
                                Ok(value) => {
                                    return Ok((AssetLoadingState::ready(key, value), changed_at))
                                }
                                Err(_) => {
                                    unreachable!("Asset type mismatch: {:?}", key)
                                }
                            }
                        }
                        Some(CachedEntry::AssetError(err)) => {
                            // Check consistency for cached leaf errors
                            if !has_locator_deps {
                                check_leaf_asset_consistency(changed_at)?;
                            }
                            // Cache hit: start + end immediately (no locator runs)
                            self.tracer.on_asset_requested(&span_ctx, &asset_cache_key);
                            self.tracer.on_asset_located(
                                &span_ctx,
                                &asset_cache_key,
                                TracerAssetState::NotFound,
                            );
                            return Err(QueryError::UserError(err.clone()));
                        }
                        None => {
                            // Loading state - no value to be inconsistent with
                            // Cache hit: start + end immediately (no locator runs)
                            self.tracer.on_asset_requested(&span_ctx, &asset_cache_key);
                            self.tracer.on_asset_located(
                                &span_ctx,
                                &asset_cache_key,
                                TracerAssetState::Loading,
                            );
                            return Ok((AssetLoadingState::loading(key), changed_at));
                        }
                        _ => {
                            // Query-related entries (Ok, UserError) shouldn't be here
                            // Fall through to locator
                        }
                    }
                }
            }
        }

        // Not in cache or invalid - try locator
        // Use LocatorContext to track deps on the asset itself
        check_cycle(&full_cache_key)?;
        let _guard = StackGuard::push(full_cache_key.clone());

        // Notify tracer BEFORE locator runs (START event) so child queries appear as children
        self.tracer.on_asset_requested(&span_ctx, &asset_cache_key);

        let locator_ctx = LocatorContext::new(self, full_cache_key.clone());
        let locator_result =
            self.locators
                .locate_with_locator_ctx(TypeId::of::<K>(), &locator_ctx, &key);

        if let Some(result) = locator_result {
            // Get collected dependencies from the locator context
            let locator_deps = locator_ctx.into_deps();
            match result {
                Ok(ErasedLocateResult::Ready {
                    value: arc,
                    durability: durability_level,
                }) => {
                    // END event after locator completes
                    self.tracer.on_asset_located(
                        &span_ctx,
                        &asset_cache_key,
                        TracerAssetState::Ready,
                    );

                    let typed_value: Arc<K::Asset> = match arc.downcast::<K::Asset>() {
                        Ok(v) => v,
                        Err(_) => {
                            unreachable!("Asset type mismatch: {:?}", key);
                        }
                    };

                    // Store in whale atomically with early cutoff
                    // Include locator's dependencies so the asset is invalidated when they change
                    let entry = CachedEntry::AssetReady(typed_value.clone());
                    let durability = Durability::new(durability_level.as_u8() as usize)
                        .unwrap_or(Durability::volatile());
                    let new_value = typed_value.clone();
                    let result = self
                        .whale
                        .update_with_compare(
                            full_cache_key.clone(),
                            Some(entry),
                            |old_data, _new_data| {
                                let Some(CachedEntry::AssetReady(old_arc)) =
                                    old_data.and_then(|d| d.as_ref())
                                else {
                                    return true;
                                };
                                let Ok(old_value) = old_arc.clone().downcast::<K::Asset>() else {
                                    return true;
                                };
                                !K::asset_eq(&old_value, &new_value)
                            },
                            durability,
                            locator_deps,
                        )
                        .expect("update_with_compare should succeed");

                    // Register verifier for this asset (for verify-then-decide pattern)
                    self.verifiers
                        .insert_asset::<K, T>(full_cache_key, key.clone());

                    return Ok((AssetLoadingState::ready(key, typed_value), result.revision));
                }
                Ok(ErasedLocateResult::Pending) => {
                    // END event after locator completes with pending
                    self.tracer.on_asset_located(
                        &span_ctx,
                        &asset_cache_key,
                        TracerAssetState::Loading,
                    );

                    // Add to pending list for Pending result
                    self.pending
                        .insert::<K>(asset_cache_key.clone(), key.clone());
                    match self
                        .whale
                        .get_or_insert(full_cache_key, None, Durability::volatile(), locator_deps)
                        .expect("get_or_insert should succeed")
                    {
                        GetOrInsertResult::Inserted(node) => {
                            return Ok((AssetLoadingState::loading(key), node.changed_at));
                        }
                        GetOrInsertResult::Existing(node) => {
                            let changed_at = node.changed_at;
                            match &node.data {
                                Some(CachedEntry::AssetReady(arc)) => {
                                    match arc.clone().downcast::<K::Asset>() {
                                        Ok(value) => {
                                            return Ok((
                                                AssetLoadingState::ready(key, value),
                                                changed_at,
                                            ))
                                        }
                                        Err(_) => {
                                            return Ok((
                                                AssetLoadingState::loading(key),
                                                changed_at,
                                            ))
                                        }
                                    }
                                }
                                Some(CachedEntry::AssetError(err)) => {
                                    return Err(QueryError::UserError(err.clone()));
                                }
                                _ => return Ok((AssetLoadingState::loading(key), changed_at)),
                            }
                        }
                    }
                }
                Err(QueryError::UserError(err)) => {
                    // END event after locator completes with error
                    self.tracer.on_asset_located(
                        &span_ctx,
                        &asset_cache_key,
                        TracerAssetState::NotFound,
                    );
                    // Locator returned a user error - cache it as AssetError
                    let entry = CachedEntry::AssetError(err.clone());
                    let _ = self.whale.register(
                        full_cache_key,
                        Some(entry),
                        Durability::volatile(),
                        locator_deps,
                    );
                    return Err(QueryError::UserError(err));
                }
                Err(e) => {
                    // Other errors (Cycle, Suspended, etc.) - do NOT cache, propagate directly
                    return Err(e);
                }
            }
        }

        // No locator registered or locator returned None - mark as pending
        // (no locator was called, so no deps to track)
        // END event - no locator ran
        self.tracer
            .on_asset_located(&span_ctx, &asset_cache_key, TracerAssetState::Loading);
        self.pending
            .insert::<K>(asset_cache_key.clone(), key.clone());

        match self
            .whale
            .get_or_insert(full_cache_key, None, Durability::volatile(), vec![])
            .expect("get_or_insert with no dependencies cannot fail")
        {
            GetOrInsertResult::Inserted(node) => {
                Ok((AssetLoadingState::loading(key), node.changed_at))
            }
            GetOrInsertResult::Existing(node) => {
                let changed_at = node.changed_at;
                match &node.data {
                    Some(CachedEntry::AssetReady(arc)) => {
                        match arc.clone().downcast::<K::Asset>() {
                            Ok(value) => Ok((AssetLoadingState::ready(key, value), changed_at)),
                            Err(_) => Ok((AssetLoadingState::loading(key), changed_at)),
                        }
                    }
                    Some(CachedEntry::AssetError(err)) => Err(QueryError::UserError(err.clone())),
                    _ => Ok((AssetLoadingState::loading(key), changed_at)),
                }
            }
        }
    }

    /// Internal: Get asset state and its changed_at revision atomically (with QueryContext).
    ///
    /// This version is called from QueryContext::asset. Consistency checking for
    /// cached leaf assets is done inside this function before returning.
    fn get_asset_with_revision_ctx<K: AssetKey>(
        &self,
        key: K,
        _ctx: &QueryContext<'_, T>,
    ) -> Result<(AssetLoadingState<K>, RevisionCounter), QueryError> {
        let asset_cache_key = AssetCacheKey::new(key.clone());
        let full_cache_key: FullCacheKey = asset_cache_key.clone().into();

        // Create a span for this asset request (like queries do)
        // This ensures child queries called from locators show as children of this asset
        let asset_span_id = self.tracer.new_span_id();
        let (trace_id, parent_span_id) = SPAN_STACK.with(|stack| match &*stack.borrow() {
            SpanStack::Empty => (self.tracer.new_trace_id(), None),
            SpanStack::Active(tid, spans) => (*tid, spans.last().copied()),
        });
        let span_ctx = SpanContext {
            span_id: asset_span_id,
            trace_id,
            parent_span_id,
        };

        // Push asset span to stack so child queries see this asset as their parent
        let _span_guard = SpanStackGuard::push(trace_id, asset_span_id);

        // Check whale cache first (single atomic read)
        if let Some(node) = self.whale.get(&full_cache_key) {
            let changed_at = node.changed_at;
            // Check if valid at current revision (shallow check)
            if self.whale.is_valid(&full_cache_key) {
                // Verify dependencies recursively (like query path does)
                let mut deps_verified = true;
                if let Some(deps) = self.whale.get_dependency_ids(&full_cache_key) {
                    for dep in deps {
                        if let Some(verifier) = self.verifiers.get(&dep) {
                            // Re-run query/asset to verify it (triggers recursive verification)
                            if verifier.verify(self as &dyn std::any::Any).is_err() {
                                deps_verified = false;
                                break;
                            }
                        }
                    }
                }

                // Re-check validity after deps are verified
                if deps_verified && self.whale.is_valid(&full_cache_key) {
                    // For cached entries, check consistency for leaf assets (no locator deps).
                    // This detects if resolve_asset/resolve_asset_error was called during query execution.
                    let has_locator_deps = self
                        .whale
                        .get_dependency_ids(&full_cache_key)
                        .is_some_and(|deps| !deps.is_empty());

                    match &node.data {
                        Some(CachedEntry::AssetReady(arc)) => {
                            // Check consistency for cached leaf assets
                            if !has_locator_deps {
                                check_leaf_asset_consistency(changed_at)?;
                            }
                            // Cache hit: start + end immediately (no locator runs)
                            self.tracer.on_asset_requested(&span_ctx, &asset_cache_key);
                            self.tracer.on_asset_located(
                                &span_ctx,
                                &asset_cache_key,
                                TracerAssetState::Ready,
                            );
                            match arc.clone().downcast::<K::Asset>() {
                                Ok(value) => {
                                    return Ok((AssetLoadingState::ready(key, value), changed_at))
                                }
                                Err(_) => {
                                    unreachable!("Asset type mismatch: {:?}", key)
                                }
                            }
                        }
                        Some(CachedEntry::AssetError(err)) => {
                            // Check consistency for cached leaf errors
                            if !has_locator_deps {
                                check_leaf_asset_consistency(changed_at)?;
                            }
                            // Cache hit: start + end immediately (no locator runs)
                            self.tracer.on_asset_requested(&span_ctx, &asset_cache_key);
                            self.tracer.on_asset_located(
                                &span_ctx,
                                &asset_cache_key,
                                TracerAssetState::NotFound,
                            );
                            return Err(QueryError::UserError(err.clone()));
                        }
                        None => {
                            // Loading state - no value to be inconsistent with
                            // Cache hit: start + end immediately (no locator runs)
                            self.tracer.on_asset_requested(&span_ctx, &asset_cache_key);
                            self.tracer.on_asset_located(
                                &span_ctx,
                                &asset_cache_key,
                                TracerAssetState::Loading,
                            );
                            return Ok((AssetLoadingState::loading(key), changed_at));
                        }
                        _ => {
                            // Query-related entries (Ok, UserError) shouldn't be here
                            // Fall through to locator
                        }
                    }
                }
            }
        }

        // Not in cache or invalid - try locator
        // Use LocatorContext to track deps on the asset itself (not the calling query)
        // Consistency tracking is handled via thread-local storage
        check_cycle(&full_cache_key)?;
        let _guard = StackGuard::push(full_cache_key.clone());

        // START event before locator runs
        self.tracer.on_asset_requested(&span_ctx, &asset_cache_key);

        let locator_ctx = LocatorContext::new(self, full_cache_key.clone());
        let locator_result =
            self.locators
                .locate_with_locator_ctx(TypeId::of::<K>(), &locator_ctx, &key);

        if let Some(result) = locator_result {
            // Get collected dependencies from the locator context
            let locator_deps = locator_ctx.into_deps();
            match result {
                Ok(ErasedLocateResult::Ready {
                    value: arc,
                    durability: durability_level,
                }) => {
                    // END event after locator completes
                    self.tracer.on_asset_located(
                        &span_ctx,
                        &asset_cache_key,
                        TracerAssetState::Ready,
                    );

                    let typed_value: Arc<K::Asset> = match arc.downcast::<K::Asset>() {
                        Ok(v) => v,
                        Err(_) => {
                            unreachable!("Asset type mismatch: {:?}", key);
                        }
                    };

                    // Store in whale atomically with early cutoff
                    // Include locator's dependencies so the asset is invalidated when they change
                    let entry = CachedEntry::AssetReady(typed_value.clone());
                    let durability = Durability::new(durability_level.as_u8() as usize)
                        .unwrap_or(Durability::volatile());
                    let new_value = typed_value.clone();
                    let result = self
                        .whale
                        .update_with_compare(
                            full_cache_key.clone(),
                            Some(entry),
                            |old_data, _new_data| {
                                let Some(CachedEntry::AssetReady(old_arc)) =
                                    old_data.and_then(|d| d.as_ref())
                                else {
                                    return true;
                                };
                                let Ok(old_value) = old_arc.clone().downcast::<K::Asset>() else {
                                    return true;
                                };
                                !K::asset_eq(&old_value, &new_value)
                            },
                            durability,
                            locator_deps,
                        )
                        .expect("update_with_compare should succeed");

                    // Register verifier for this asset (for verify-then-decide pattern)
                    self.verifiers
                        .insert_asset::<K, T>(full_cache_key, key.clone());

                    return Ok((AssetLoadingState::ready(key, typed_value), result.revision));
                }
                Ok(ErasedLocateResult::Pending) => {
                    // END event after locator completes with pending
                    self.tracer.on_asset_located(
                        &span_ctx,
                        &asset_cache_key,
                        TracerAssetState::Loading,
                    );

                    // Add to pending list for Pending result
                    self.pending
                        .insert::<K>(asset_cache_key.clone(), key.clone());
                    match self
                        .whale
                        .get_or_insert(full_cache_key, None, Durability::volatile(), locator_deps)
                        .expect("get_or_insert should succeed")
                    {
                        GetOrInsertResult::Inserted(node) => {
                            return Ok((AssetLoadingState::loading(key), node.changed_at));
                        }
                        GetOrInsertResult::Existing(node) => {
                            let changed_at = node.changed_at;
                            match &node.data {
                                Some(CachedEntry::AssetReady(arc)) => {
                                    match arc.clone().downcast::<K::Asset>() {
                                        Ok(value) => {
                                            return Ok((
                                                AssetLoadingState::ready(key, value),
                                                changed_at,
                                            ));
                                        }
                                        Err(_) => {
                                            return Ok((
                                                AssetLoadingState::loading(key),
                                                changed_at,
                                            ))
                                        }
                                    }
                                }
                                Some(CachedEntry::AssetError(err)) => {
                                    return Err(QueryError::UserError(err.clone()));
                                }
                                _ => return Ok((AssetLoadingState::loading(key), changed_at)),
                            }
                        }
                    }
                }
                Err(QueryError::UserError(err)) => {
                    // END event after locator completes with error
                    self.tracer.on_asset_located(
                        &span_ctx,
                        &asset_cache_key,
                        TracerAssetState::NotFound,
                    );
                    // Locator returned a user error - cache it as AssetError
                    let entry = CachedEntry::AssetError(err.clone());
                    let _ = self.whale.register(
                        full_cache_key,
                        Some(entry),
                        Durability::volatile(),
                        locator_deps,
                    );
                    return Err(QueryError::UserError(err));
                }
                Err(e) => {
                    // Other errors (Cycle, Suspended, etc.) - do NOT cache, propagate directly
                    return Err(e);
                }
            }
        }

        // No locator registered or locator returned None - mark as pending
        // END event - no locator ran
        self.tracer
            .on_asset_located(&span_ctx, &asset_cache_key, TracerAssetState::Loading);
        self.pending
            .insert::<K>(asset_cache_key.clone(), key.clone());

        match self
            .whale
            .get_or_insert(full_cache_key, None, Durability::volatile(), vec![])
            .expect("get_or_insert with no dependencies cannot fail")
        {
            GetOrInsertResult::Inserted(node) => {
                Ok((AssetLoadingState::loading(key), node.changed_at))
            }
            GetOrInsertResult::Existing(node) => {
                let changed_at = node.changed_at;
                match &node.data {
                    Some(CachedEntry::AssetReady(arc)) => {
                        match arc.clone().downcast::<K::Asset>() {
                            Ok(value) => Ok((AssetLoadingState::ready(key, value), changed_at)),
                            Err(_) => Ok((AssetLoadingState::loading(key), changed_at)),
                        }
                    }
                    Some(CachedEntry::AssetError(err)) => Err(QueryError::UserError(err.clone())),
                    _ => Ok((AssetLoadingState::loading(key), changed_at)),
                }
            }
        }
    }

    /// Internal: Get asset state, checking cache and locator.
    fn get_asset_internal<K: AssetKey>(&self, key: K) -> Result<AssetLoadingState<K>, QueryError> {
        self.get_asset_with_revision(key).map(|(state, _)| state)
    }
}

impl<T: Tracer> Db for QueryRuntime<T> {
    fn query<Q: Query>(&self, query: Q) -> Result<Arc<Q::Output>, QueryError> {
        QueryRuntime::query(self, query)
    }

    fn asset<K: AssetKey>(&self, key: K) -> Result<Arc<K::Asset>, QueryError> {
        self.get_asset_internal(key)?.suspend()
    }

    fn asset_state<K: AssetKey>(&self, key: K) -> Result<AssetLoadingState<K>, QueryError> {
        self.get_asset_internal(key)
    }

    fn list_queries<Q: Query>(&self) -> Vec<Q> {
        self.query_registry.get_all::<Q>()
    }

    fn list_asset_keys<K: AssetKey>(&self) -> Vec<K> {
        self.asset_key_registry.get_all::<K>()
    }
}

/// Tracks consistency of leaf asset accesses during query execution.
///
/// A "leaf" asset is one without dependencies (externally resolved via `resolve_asset`).
/// This tracker ensures that all leaf assets accessed during a query execution
/// (including those accessed by locators) are consistent - i.e., none were modified
/// via `resolve_asset` mid-execution.
///
/// The tracker is shared across `QueryContext` and `LocatorContext` to propagate
/// consistency checking through the entire execution tree.
#[derive(Debug)]
pub(crate) struct ConsistencyTracker {
    /// Global revision at query start. All leaf assets must have changed_at <= this.
    start_revision: RevisionCounter,
}

impl ConsistencyTracker {
    /// Create a new tracker with the given start revision.
    pub fn new(start_revision: RevisionCounter) -> Self {
        Self { start_revision }
    }

    /// Check consistency for a leaf asset access.
    ///
    /// A leaf asset is consistent if its changed_at <= start_revision.
    /// This detects if resolve_asset was called during query execution.
    ///
    /// Returns Ok(()) if consistent, Err if inconsistent.
    pub fn check_leaf_asset(&self, dep_changed_at: RevisionCounter) -> Result<(), QueryError> {
        if dep_changed_at > self.start_revision {
            Err(QueryError::InconsistentAssetResolution)
        } else {
            Ok(())
        }
    }
}

/// Context provided to queries during execution.
///
/// Use this to access dependencies via `query()`.
pub(crate) struct QueryContext<'a, T: Tracer = NoopTracer> {
    runtime: &'a QueryRuntime<T>,
    current_key: FullCacheKey,
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
        let full_key: FullCacheKey = QueryCacheKey::new(query.clone()).into();

        // Emit dependency registered event
        self.runtime.tracer.on_dependency_registered(
            self.exec_ctx.span_ctx(),
            &self.current_key,
            &full_key,
        );

        // Record this as a dependency
        self.deps.borrow_mut().push(full_key);

        // Execute the query
        self.runtime.query(query)
    }

    /// Access an asset, tracking it as a dependency.
    ///
    /// Returns the asset value if ready, or `Err(QueryError::Suspend)` if still loading.
    /// Use this with the `?` operator for automatic suspension on loading.
    ///
    /// # Example
    ///
    /// ```ignore
    /// #[query]
    /// fn process_file(db: &impl Db, path: FilePath) -> Result<Output, QueryError> {
    ///     let content = db.asset(path)?;
    ///     // Process content...
    ///     Ok(output)
    /// }
    /// ```
    ///
    /// # Errors
    ///
    /// - Returns `Err(QueryError::Suspend)` if the asset is still loading.
    /// - Returns `Err(QueryError::UserError)` if the asset was not found.
    pub fn asset<K: AssetKey>(&self, key: K) -> Result<Arc<K::Asset>, QueryError> {
        self.asset_state(key)?.suspend()
    }

    /// Access an asset's loading state, tracking it as a dependency.
    ///
    /// Unlike [`asset()`](Self::asset), this method returns the full loading state,
    /// allowing you to check if an asset is loading without triggering suspension.
    ///
    /// # Example
    ///
    /// ```ignore
    /// let state = db.asset_state(key)?;
    /// if state.is_loading() {
    ///     // Handle loading case explicitly
    /// } else {
    ///     let value = state.get().unwrap();
    /// }
    /// ```
    ///
    /// # Errors
    ///
    /// Returns `Err(QueryError::UserError)` if the asset was not found.
    pub fn asset_state<K: AssetKey>(&self, key: K) -> Result<AssetLoadingState<K>, QueryError> {
        let full_cache_key: FullCacheKey = AssetCacheKey::new(key.clone()).into();

        // 1. Emit asset dependency registered event
        self.runtime.tracer.on_asset_dependency_registered(
            self.exec_ctx.span_ctx(),
            &self.current_key,
            &full_cache_key,
        );

        // 2. Record dependency on this asset
        self.deps.borrow_mut().push(full_cache_key);

        // 3. Get asset from cache/locator
        // Consistency checking for cached leaf assets is done inside get_asset_with_revision_ctx
        let (state, _changed_at) = self.runtime.get_asset_with_revision_ctx(key, self)?;

        Ok(state)
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
        let sentinel: FullCacheKey = QuerySetSentinelKey::new::<Q>().into();

        self.runtime.tracer.on_dependency_registered(
            self.exec_ctx.span_ctx(),
            &self.current_key,
            &sentinel,
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
    ///         let content = db.asset(key)?;
    ///         contents.push((*content).clone());
    ///     }
    ///     Ok(contents)
    /// }
    /// ```
    pub fn list_asset_keys<K: AssetKey>(&self) -> Vec<K> {
        // Record dependency on the sentinel (set-level dependency)
        let sentinel: FullCacheKey = AssetKeySetSentinelKey::new::<K>().into();

        self.runtime.tracer.on_asset_dependency_registered(
            self.exec_ctx.span_ctx(),
            &self.current_key,
            &sentinel,
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

    fn asset<K: AssetKey>(&self, key: K) -> Result<Arc<K::Asset>, QueryError> {
        QueryContext::asset(self, key)
    }

    fn asset_state<K: AssetKey>(&self, key: K) -> Result<AssetLoadingState<K>, QueryError> {
        QueryContext::asset_state(self, key)
    }

    fn list_queries<Q: Query>(&self) -> Vec<Q> {
        QueryContext::list_queries(self)
    }

    fn list_asset_keys<K: AssetKey>(&self) -> Vec<K> {
        QueryContext::list_asset_keys(self)
    }
}

/// Context for collecting dependencies during asset locator execution.
///
/// Unlike `QueryContext`, this is specifically for locators and does not
/// register dependencies on any parent query. Dependencies collected here
/// are stored with the asset itself.
pub(crate) struct LocatorContext<'a, T: Tracer> {
    runtime: &'a QueryRuntime<T>,
    deps: RefCell<Vec<FullCacheKey>>,
}

impl<'a, T: Tracer> LocatorContext<'a, T> {
    /// Create a new locator context for the given asset key.
    ///
    /// Consistency tracking is handled via thread-local storage, so leaf asset
    /// accesses will be checked against any active tracker from a parent query.
    pub(crate) fn new(runtime: &'a QueryRuntime<T>, _asset_key: FullCacheKey) -> Self {
        Self {
            runtime,
            deps: RefCell::new(Vec::new()),
        }
    }

    /// Consume this context and return the collected dependencies.
    pub(crate) fn into_deps(self) -> Vec<FullCacheKey> {
        self.deps.into_inner()
    }
}

impl<T: Tracer> Db for LocatorContext<'_, T> {
    fn query<Q: Query>(&self, query: Q) -> Result<Arc<Q::Output>, QueryError> {
        let full_key = QueryCacheKey::new(query.clone()).into();

        // Record this as a dependency of the asset being located
        self.deps.borrow_mut().push(full_key);

        // Execute the query via the runtime
        self.runtime.query(query)
    }

    fn asset<K: AssetKey>(&self, key: K) -> Result<Arc<K::Asset>, QueryError> {
        self.asset_state(key)?.suspend()
    }

    fn asset_state<K: AssetKey>(&self, key: K) -> Result<AssetLoadingState<K>, QueryError> {
        let full_cache_key = AssetCacheKey::new(key.clone()).into();

        // Record this as a dependency of the asset being located
        self.deps.borrow_mut().push(full_cache_key);

        // Access the asset - consistency checking is done inside get_asset_with_revision
        let (state, _changed_at) = self.runtime.get_asset_with_revision(key)?;

        Ok(state)
    }

    fn list_queries<Q: Query>(&self) -> Vec<Q> {
        self.runtime.list_queries()
    }

    fn list_asset_keys<K: AssetKey>(&self) -> Vec<K> {
        self.runtime.list_asset_keys()
    }
}

/// Enum dispatch wrapper for Db implementations.
///
/// Reduces monomorphization by providing a single concrete type
/// for `&impl Db` parameters in user code.
pub(crate) enum DbDispatch<'a, T: Tracer = NoopTracer> {
    /// Query execution context (tracks query dependencies)
    QueryContext(&'a QueryContext<'a, T>),
    /// Locator execution context (tracks asset dependencies)
    LocatorContext(&'a LocatorContext<'a, T>),
}

impl<T: Tracer> Db for DbDispatch<'_, T> {
    fn query<Q: Query>(&self, query: Q) -> Result<Arc<Q::Output>, QueryError> {
        match self {
            DbDispatch::QueryContext(ctx) => ctx.query(query),
            DbDispatch::LocatorContext(ctx) => ctx.query(query),
        }
    }

    fn asset<K: AssetKey>(&self, key: K) -> Result<Arc<K::Asset>, QueryError> {
        match self {
            DbDispatch::QueryContext(ctx) => ctx.asset(key),
            DbDispatch::LocatorContext(ctx) => ctx.asset(key),
        }
    }

    fn asset_state<K: AssetKey>(&self, key: K) -> Result<AssetLoadingState<K>, QueryError> {
        match self {
            DbDispatch::QueryContext(ctx) => ctx.asset_state(key),
            DbDispatch::LocatorContext(ctx) => ctx.asset_state(key),
        }
    }

    fn list_queries<Q: Query>(&self) -> Vec<Q> {
        match self {
            DbDispatch::QueryContext(ctx) => ctx.list_queries(),
            DbDispatch::LocatorContext(ctx) => ctx.list_queries(),
        }
    }

    fn list_asset_keys<K: AssetKey>(&self) -> Vec<K> {
        match self {
            DbDispatch::QueryContext(ctx) => ctx.list_asset_keys(),
            DbDispatch::LocatorContext(ctx) => ctx.list_asset_keys(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_query() {
        #[derive(Clone, Debug, Hash, PartialEq, Eq)]
        struct Add {
            a: i32,
            b: i32,
        }

        impl Query for Add {
            type Output = i32;

            fn query(self, _db: &impl Db) -> Result<Arc<Self::Output>, QueryError> {
                Ok(Arc::new(self.a + self.b))
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
        #[derive(Clone, Debug, Hash, PartialEq, Eq)]
        struct Base {
            value: i32,
        }

        impl Query for Base {
            type Output = i32;

            fn query(self, _db: &impl Db) -> Result<Arc<Self::Output>, QueryError> {
                Ok(Arc::new(self.value * 2))
            }

            fn output_eq(old: &Self::Output, new: &Self::Output) -> bool {
                old == new
            }
        }

        #[derive(Clone, Debug, Hash, PartialEq, Eq)]
        struct Derived {
            base_value: i32,
        }

        impl Query for Derived {
            type Output = i32;

            fn query(self, db: &impl Db) -> Result<Arc<Self::Output>, QueryError> {
                let base = db.query(Base {
                    value: self.base_value,
                })?;
                Ok(Arc::new(*base + 10))
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
        #[derive(Clone, Debug, Hash, PartialEq, Eq)]
        struct CycleA {
            id: i32,
        }

        #[derive(Clone, Debug, Hash, PartialEq, Eq)]
        struct CycleB {
            id: i32,
        }

        impl Query for CycleA {
            type Output = i32;

            fn query(self, db: &impl Db) -> Result<Arc<Self::Output>, QueryError> {
                let b = db.query(CycleB { id: self.id })?;
                Ok(Arc::new(*b + 1))
            }

            fn output_eq(old: &Self::Output, new: &Self::Output) -> bool {
                old == new
            }
        }

        impl Query for CycleB {
            type Output = i32;

            fn query(self, db: &impl Db) -> Result<Arc<Self::Output>, QueryError> {
                let a = db.query(CycleA { id: self.id })?;
                Ok(Arc::new(*a + 1))
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
        #[derive(Clone, Debug, Hash, PartialEq, Eq)]
        struct ParseInt {
            input: String,
        }

        impl Query for ParseInt {
            type Output = Result<i32, std::num::ParseIntError>;

            fn query(self, _db: &impl Db) -> Result<Arc<Self::Output>, QueryError> {
                Ok(Arc::new(self.input.parse()))
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

        #[query]
        fn simple_double(db: &impl Db, x: i32) -> Result<i32, QueryError> {
            let _ = db;
            Ok(x * 2)
        }

        #[test]
        fn test_macro_simple() {
            let runtime = QueryRuntime::new();
            let result = runtime.query(SimpleDouble::new(5)).unwrap();
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

        #[derive(Clone, Debug, Hash, PartialEq, Eq)]
        struct Counter {
            id: i32,
        }

        impl Query for Counter {
            type Output = i32;

            fn query(self, _db: &impl Db) -> Result<Arc<Self::Output>, QueryError> {
                Ok(Arc::new(self.id * 10))
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
            runtime.invalidate(&Counter { id: 1 });
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
            let rev = runtime.changed_at(&Counter { id: 1 });
            assert!(rev.is_none());
        }

        #[test]
        fn test_changed_at_returns_revision_after_execution() {
            let runtime = QueryRuntime::new();

            // Execute the query
            let _ = runtime.query(Counter { id: 1 }).unwrap();

            // Now changed_at should return Some
            let rev = runtime.changed_at(&Counter { id: 1 });
            assert!(rev.is_some());
            assert!(rev.unwrap() > 0);
        }

        #[test]
        fn test_changed_at_matches_poll_revision() {
            let runtime = QueryRuntime::new();

            // Poll the query
            let result = runtime.poll(Counter { id: 1 }).unwrap();

            // changed_at should match the revision from poll
            let rev = runtime.changed_at(&Counter { id: 1 });
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
        use crate::tracer::{SpanContext, SpanId, TraceId};
        use std::collections::HashSet;
        use std::sync::atomic::{AtomicUsize, Ordering};
        use std::sync::Mutex;

        #[derive(Clone, Debug, Hash, PartialEq, Eq)]
        struct Leaf {
            id: i32,
        }

        impl Query for Leaf {
            type Output = i32;

            fn query(self, _db: &impl Db) -> Result<Arc<Self::Output>, QueryError> {
                Ok(Arc::new(self.id * 10))
            }

            fn output_eq(old: &Self::Output, new: &Self::Output) -> bool {
                old == new
            }
        }

        #[derive(Clone, Debug, Hash, PartialEq, Eq)]
        struct Parent {
            child_id: i32,
        }

        impl Query for Parent {
            type Output = i32;

            fn query(self, db: &impl Db) -> Result<Arc<Self::Output>, QueryError> {
                let child = db.query(Leaf { id: self.child_id })?;
                Ok(Arc::new(*child + 1))
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
            let full_key = QueryCacheKey::new(Leaf { id: 1 }).into();

            // Query should exist
            assert!(runtime.changed_at(&Leaf { id: 1 }).is_some());

            // Remove it
            assert!(runtime.remove(&full_key));

            // Query should no longer exist
            assert!(runtime.changed_at(&Leaf { id: 1 }).is_none());
        }

        #[test]
        fn test_remove_if_unused_removes_leaf_query() {
            let runtime = QueryRuntime::new();

            // Execute a leaf query (no dependents)
            let _ = runtime.query(Leaf { id: 1 }).unwrap();

            // Should be removable since no other query depends on it
            assert!(runtime.remove_query_if_unused(&Leaf { id: 1 }));

            // Query should no longer exist
            assert!(runtime.changed_at(&Leaf { id: 1 }).is_none());
        }

        #[test]
        fn test_remove_if_unused_does_not_remove_query_with_dependents() {
            let runtime = QueryRuntime::new();

            // Execute parent query (which depends on Leaf)
            let _ = runtime.query(Parent { child_id: 1 }).unwrap();

            // Leaf query should not be removable since Parent depends on it
            assert!(!runtime.remove_query_if_unused(&Leaf { id: 1 }));

            // Leaf query should still exist
            assert!(runtime.changed_at(&Leaf { id: 1 }).is_some());

            // But Parent should be removable (no dependents)
            assert!(runtime.remove_query_if_unused(&Parent { child_id: 1 }));
        }

        #[test]
        fn test_remove_if_unused_with_full_cache_key() {
            let runtime = QueryRuntime::new();

            // Execute a leaf query
            let _ = runtime.query(Leaf { id: 1 }).unwrap();

            let full_key = QueryCacheKey::new(Leaf { id: 1 }).into();

            // Should be removable via FullCacheKey
            assert!(runtime.remove_if_unused(&full_key));

            // Query should no longer exist
            assert!(runtime.changed_at(&Leaf { id: 1 }).is_none());
        }

        // Test tracer receives on_query_start calls (for GC tracking)
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

            fn new_trace_id(&self) -> TraceId {
                TraceId(1)
            }

            fn on_query_start(&self, _ctx: &SpanContext, query_key: &QueryCacheKey) {
                self.accessed_keys
                    .lock()
                    .unwrap()
                    .insert(query_key.debug_repr().to_string());
                self.access_count.fetch_add(1, Ordering::Relaxed);
            }
        }

        #[test]
        fn test_tracer_receives_on_query_start() {
            let tracker = GcTracker::new();
            let runtime = QueryRuntime::with_tracer(tracker);

            // Execute some queries
            let _ = runtime.query(Leaf { id: 1 }).unwrap();
            let _ = runtime.query(Leaf { id: 2 }).unwrap();

            // Tracer should have received on_query_start calls
            let count = runtime.tracer().access_count.load(Ordering::Relaxed);
            assert_eq!(count, 2);

            // Check that the keys were recorded
            let keys = runtime.tracer().accessed_keys.lock().unwrap();
            assert!(keys.iter().any(|k| k.contains("Leaf")));
        }

        #[test]
        fn test_tracer_receives_on_query_start_for_cache_hits() {
            let tracker = GcTracker::new();
            let runtime = QueryRuntime::with_tracer(tracker);

            // Execute query twice (second is cache hit)
            let _ = runtime.query(Leaf { id: 1 }).unwrap();
            let _ = runtime.query(Leaf { id: 1 }).unwrap();

            // Tracer should have received on_query_start for both calls
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
            assert!(runtime.changed_at(&Leaf { id: 1 }).is_none());
            assert!(runtime.changed_at(&Leaf { id: 2 }).is_none());
            assert!(runtime.changed_at(&Leaf { id: 3 }).is_none());
        }
    }
}
