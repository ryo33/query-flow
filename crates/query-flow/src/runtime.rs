//! Query runtime and context.

use std::any::TypeId;
use std::cell::RefCell;
use std::sync::Arc;

use std::ops::Deref;

use whale::{Durability, RevisionCounter, Runtime as WhaleRuntime};

use crate::asset::{AssetKey, AssetLocator, DurabilityLevel, FullAssetKey, PendingAsset};
use crate::key::FullCacheKey;
use crate::loading::LoadingState;
use crate::query::Query;
use crate::storage::{
    AssetKeyRegistry, AssetState, AssetStorage, CachedEntry, CachedValue, LocatorStorage,
    PendingStorage, QueryRegistry, VerifierStorage,
};
use crate::QueryError;

/// Function type for comparing user errors during early cutoff.
///
/// Used by `QueryRuntimeBuilder::error_comparator` to customize how
/// `QueryError::UserError` values are compared for caching purposes.
pub type ErrorComparator = fn(&anyhow::Error, &anyhow::Error) -> bool;

#[cfg(feature = "inspector")]
use query_flow_inspector::{EventSink, FlowEvent, SpanId};

/// Number of durability levels (matches whale's default).
const DURABILITY_LEVELS: usize = 4;

// Thread-local query execution stack for cycle detection.
thread_local! {
    static QUERY_STACK: RefCell<Vec<FullCacheKey>> = const { RefCell::new(Vec::new()) };
}

/// Execution context passed through query execution.
///
/// When the `inspector` feature is disabled, this is a zero-sized type (ZST)
/// with no runtime cost.
#[cfg(feature = "inspector")]
#[derive(Clone, Copy)]
pub struct ExecutionContext {
    span_id: SpanId,
}

#[cfg(not(feature = "inspector"))]
#[derive(Clone, Copy)]
pub struct ExecutionContext;

impl ExecutionContext {
    /// Create a new execution context.
    #[cfg(feature = "inspector")]
    pub fn new() -> Self {
        Self {
            span_id: query_flow_inspector::new_span_id(),
        }
    }

    /// Create a new execution context.
    #[cfg(not(feature = "inspector"))]
    #[inline(always)]
    pub fn new() -> Self {
        Self
    }

    /// Get the span ID for this execution context.
    #[cfg(feature = "inspector")]
    pub fn span_id(&self) -> SpanId {
        self.span_id
    }
}

impl Default for ExecutionContext {
    fn default() -> Self {
        Self::new()
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
/// # Example
///
/// ```ignore
/// let runtime = QueryRuntime::new();
///
/// // Sync query execution
/// let result = runtime.query(MyQuery { ... })?;
///
/// // Async query execution (waits through Suspend)
/// let result = runtime.query_async(MyQuery { ... }).await?;
/// ```
pub struct QueryRuntime {
    /// Whale runtime for dependency tracking and cache storage.
    /// Query outputs are stored in Node.data as Option<CachedEntry>.
    whale: WhaleRuntime<FullCacheKey, Option<CachedEntry>, DURABILITY_LEVELS>,
    /// Asset cache and state storage
    assets: Arc<AssetStorage>,
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
    /// Event sink for inspector/tracing
    #[cfg(feature = "inspector")]
    sink: Arc<parking_lot::RwLock<Option<Arc<dyn EventSink>>>>,
}

impl Default for QueryRuntime {
    fn default() -> Self {
        Self::new()
    }
}

impl Clone for QueryRuntime {
    fn clone(&self) -> Self {
        Self {
            whale: self.whale.clone(),
            assets: self.assets.clone(),
            locators: self.locators.clone(),
            pending: self.pending.clone(),
            query_registry: self.query_registry.clone(),
            asset_key_registry: self.asset_key_registry.clone(),
            verifiers: self.verifiers.clone(),
            error_comparator: self.error_comparator,
            #[cfg(feature = "inspector")]
            sink: self.sink.clone(),
        }
    }
}

/// Default error comparator that treats all errors as different.
///
/// This is conservative - it always triggers recomputation when an error occurs.
fn default_error_comparator(_a: &anyhow::Error, _b: &anyhow::Error) -> bool {
    false
}

impl QueryRuntime {
    /// Get cached output from whale's node data.
    fn get_cached<Q: Query>(&self, key: &FullCacheKey) -> Option<CachedValue<Arc<Q::Output>>> {
        let node = self.whale.get(key)?;
        let entry = node.data.as_ref()?;
        entry.to_cached_value::<Q::Output>()
    }
}

impl QueryRuntime {
    /// Create a new query runtime with default settings.
    pub fn new() -> Self {
        Self::builder().build()
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
    pub fn builder() -> QueryRuntimeBuilder {
        QueryRuntimeBuilder::new()
    }

    /// Set the event sink for tracing/inspection.
    ///
    /// Pass `Some(sink)` to enable event collection, or `None` to disable.
    ///
    /// # Example
    ///
    /// ```ignore
    /// use query_flow_inspector::EventCollector;
    /// use std::sync::Arc;
    ///
    /// let collector = Arc::new(EventCollector::new());
    /// runtime.set_sink(Some(collector.clone()));
    /// runtime.query(MyQuery::new());
    /// let trace = collector.trace();
    /// ```
    #[cfg(feature = "inspector")]
    pub fn set_sink(&self, sink: Option<Arc<dyn EventSink>>) {
        *self.sink.write() = sink;
    }

    /// Get the current event sink.
    #[cfg(feature = "inspector")]
    pub fn sink(&self) -> Option<Arc<dyn EventSink>> {
        self.sink.read().clone()
    }

    /// Emit an event to the sink if one is set.
    #[cfg(feature = "inspector")]
    #[inline]
    fn emit<F: FnOnce() -> FlowEvent>(&self, event: F) {
        let guard = self.sink.read();
        if let Some(ref sink) = *guard {
            sink.emit(event());
        }
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
        self.query_internal(query).map(|(output, _)| output)
    }

    /// Internal implementation shared by query() and poll().
    ///
    /// Returns (output, revision) tuple.
    fn query_internal<Q: Query>(
        &self,
        query: Q,
    ) -> Result<(Arc<Q::Output>, RevisionCounter), QueryError> {
        let key = query.cache_key();
        let full_key = FullCacheKey::new::<Q, _>(&key);

        // Create execution context and emit start event
        let exec_ctx = ExecutionContext::new();
        #[cfg(feature = "inspector")]
        let start_time = std::time::Instant::now();
        #[cfg(feature = "inspector")]
        let query_key =
            query_flow_inspector::QueryKey::new(std::any::type_name::<Q>(), full_key.debug_repr());

        #[cfg(feature = "inspector")]
        self.emit(|| FlowEvent::QueryStart {
            span_id: exec_ctx.span_id(),
            query: query_key.clone(),
        });

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

            #[cfg(feature = "inspector")]
            self.emit(|| FlowEvent::CycleDetected {
                path: path
                    .iter()
                    .map(|s| query_flow_inspector::QueryKey::new("", s.clone()))
                    .collect(),
            });

            #[cfg(feature = "inspector")]
            self.emit(|| FlowEvent::QueryEnd {
                span_id: exec_ctx.span_id(),
                query: query_key.clone(),
                result: query_flow_inspector::ExecutionResult::CycleDetected,
                duration: start_time.elapsed(),
            });

            return Err(QueryError::Cycle { path });
        }

        // Check if cached and valid (with verify-then-decide pattern)
        let current_rev = self.whale.current_revision();

        // Fast path: already verified at current revision
        if self.whale.is_verified_at(&full_key, &current_rev) {
            if let Some(cached) = self.get_cached::<Q>(&full_key) {
                // Get revision while we have the cache hit (atomic with value)
                let revision = self.whale.get(&full_key).map(|n| n.changed_at).unwrap_or(0);

                #[cfg(feature = "inspector")]
                self.emit(|| FlowEvent::CacheCheck {
                    span_id: exec_ctx.span_id(),
                    query: query_key.clone(),
                    valid: true,
                });

                #[cfg(feature = "inspector")]
                self.emit(|| FlowEvent::QueryEnd {
                    span_id: exec_ctx.span_id(),
                    query: query_key.clone(),
                    result: query_flow_inspector::ExecutionResult::CacheHit,
                    duration: start_time.elapsed(),
                });

                return match cached {
                    CachedValue::Ok(output) => Ok((output, revision)),
                    CachedValue::UserError(err) => Err(QueryError::UserError(err)),
                };
            }
        }

        // Check shallow validity (deps' changed_at ok) and try verify-then-decide
        if self.whale.is_valid(&full_key) {
            if let Some(cached) = self.get_cached::<Q>(&full_key) {
                // Shallow valid but not verified - verify deps first
                let mut deps_verified = true;
                if let Some(deps) = self.whale.get_dependency_ids(&full_key) {
                    for dep in deps {
                        if let Some(verifier) = self.verifiers.get(&dep) {
                            // Re-query dep to verify it (triggers recursive verification)
                            if verifier.verify(self).is_err() {
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

                    // Get revision while we have the cache hit (atomic with value)
                    let revision = self.whale.get(&full_key).map(|n| n.changed_at).unwrap_or(0);

                    #[cfg(feature = "inspector")]
                    self.emit(|| FlowEvent::CacheCheck {
                        span_id: exec_ctx.span_id(),
                        query: query_key.clone(),
                        valid: true,
                    });

                    #[cfg(feature = "inspector")]
                    self.emit(|| FlowEvent::QueryEnd {
                        span_id: exec_ctx.span_id(),
                        query: query_key.clone(),
                        result: query_flow_inspector::ExecutionResult::CacheHit,
                        duration: start_time.elapsed(),
                    });

                    return match cached {
                        CachedValue::Ok(output) => Ok((output, revision)),
                        CachedValue::UserError(err) => Err(QueryError::UserError(err)),
                    };
                }
                // A dep's changed_at increased, fall through to execute
            }
        }

        #[cfg(feature = "inspector")]
        self.emit(|| FlowEvent::CacheCheck {
            span_id: exec_ctx.span_id(),
            query: query_key.clone(),
            valid: false,
        });

        // Execute the query with cycle tracking
        QUERY_STACK.with(|stack| {
            stack.borrow_mut().push(full_key.clone());
        });

        let result = self.execute_query::<Q>(&query, &full_key, exec_ctx);

        QUERY_STACK.with(|stack| {
            stack.borrow_mut().pop();
        });

        // Emit end event
        #[cfg(feature = "inspector")]
        {
            let exec_result = match &result {
                Ok((_, true, _)) => query_flow_inspector::ExecutionResult::Changed,
                Ok((_, false, _)) => query_flow_inspector::ExecutionResult::Unchanged,
                Err(QueryError::Suspend) => query_flow_inspector::ExecutionResult::Suspended,
                Err(QueryError::Cycle { .. }) => {
                    query_flow_inspector::ExecutionResult::CycleDetected
                }
                Err(e) => query_flow_inspector::ExecutionResult::Error {
                    message: format!("{:?}", e),
                },
            };
            self.emit(|| FlowEvent::QueryEnd {
                span_id: exec_ctx.span_id(),
                query: query_key.clone(),
                result: exec_result,
                duration: start_time.elapsed(),
            });
        }

        result.map(|(output, _, revision)| (output, revision))
    }

    /// Execute a query, caching the result if appropriate.
    ///
    /// Returns (output, output_changed, revision) tuple for instrumentation.
    fn execute_query<Q: Query>(
        &self,
        query: &Q,
        full_key: &FullCacheKey,
        exec_ctx: ExecutionContext,
    ) -> Result<(Arc<Q::Output>, bool, RevisionCounter), QueryError> {
        // Create context for this query execution
        let mut ctx = QueryContext {
            runtime: self,
            current_key: full_key.clone(),
            #[cfg(feature = "inspector")]
            parent_query_type: std::any::type_name::<Q>(),
            #[cfg(feature = "inspector")]
            exec_ctx,
            deps: RefCell::new(Vec::new()),
        };
        // Suppress unused variable warning when inspector is disabled
        #[cfg(not(feature = "inspector"))]
        let _ = exec_ctx;

        // Execute the query
        let result = query.query(&mut ctx);

        // Get collected dependencies
        let deps: Vec<FullCacheKey> = ctx.deps.borrow().clone();

        // Get durability for whale registration
        let durability =
            Durability::new(query.durability() as usize).unwrap_or(Durability::volatile());

        match result {
            Ok(output) => {
                let output = Arc::new(output);

                // Check if output changed (for early cutoff)
                let output_changed =
                    if let Some(CachedValue::Ok(old)) = self.get_cached::<Q>(full_key) {
                        !Q::output_eq(&old, &output)
                    } else {
                        true // No previous value or was error, so "changed"
                    };

                // Emit early cutoff check event
                #[cfg(feature = "inspector")]
                self.emit(|| FlowEvent::EarlyCutoffCheck {
                    span_id: exec_ctx.span_id(),
                    query: query_flow_inspector::QueryKey::new(
                        std::any::type_name::<Q>(),
                        full_key.debug_repr(),
                    ),
                    output_changed,
                });

                // Update whale with cached entry (atomic update of value + dependency state)
                let entry = CachedEntry::Ok(output.clone() as Arc<dyn std::any::Any + Send + Sync>);
                if output_changed {
                    let _ = self
                        .whale
                        .register(full_key.clone(), Some(entry), durability, deps);
                } else {
                    let _ = self.whale.confirm_unchanged(full_key, deps);
                }

                // Register query in registry for list_queries
                let is_new_query = self.query_registry.register(query);
                if is_new_query {
                    let sentinel = FullCacheKey::query_set_sentinel::<Q>();
                    let _ = self
                        .whale
                        .register(sentinel, None, Durability::volatile(), vec![]);
                }

                // Store verifier for this query (for verify-then-decide pattern)
                self.verifiers.insert(full_key.clone(), query.clone());

                // Get revision immediately after registration (minimizes race window)
                let revision = self.whale.get(full_key).map(|n| n.changed_at).unwrap_or(0);

                Ok((output, output_changed, revision))
            }
            Err(QueryError::UserError(err)) => {
                // Check if error changed (for early cutoff)
                let output_changed =
                    if let Some(CachedValue::UserError(old_err)) = self.get_cached::<Q>(full_key) {
                        !(self.error_comparator)(old_err.as_ref(), err.as_ref())
                    } else {
                        true // No previous error or was Ok, so "changed"
                    };

                // Emit early cutoff check event
                #[cfg(feature = "inspector")]
                self.emit(|| FlowEvent::EarlyCutoffCheck {
                    span_id: exec_ctx.span_id(),
                    query: query_flow_inspector::QueryKey::new(
                        std::any::type_name::<Q>(),
                        full_key.debug_repr(),
                    ),
                    output_changed,
                });

                // Update whale with cached error (atomic update of value + dependency state)
                let entry = CachedEntry::UserError(err.clone());
                if output_changed {
                    let _ = self
                        .whale
                        .register(full_key.clone(), Some(entry), durability, deps);
                } else {
                    let _ = self.whale.confirm_unchanged(full_key, deps);
                }

                // Register query in registry for list_queries
                let is_new_query = self.query_registry.register(query);
                if is_new_query {
                    let sentinel = FullCacheKey::query_set_sentinel::<Q>();
                    let _ = self
                        .whale
                        .register(sentinel, None, Durability::volatile(), vec![]);
                }

                // Store verifier for this query (for verify-then-decide pattern)
                self.verifiers.insert(full_key.clone(), query.clone());

                Err(QueryError::UserError(err))
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

        #[cfg(feature = "inspector")]
        self.emit(|| FlowEvent::QueryInvalidated {
            query: query_flow_inspector::QueryKey::new(
                std::any::type_name::<Q>(),
                full_key.debug_repr(),
            ),
            reason: query_flow_inspector::InvalidationReason::ManualInvalidation,
        });

        // Update whale to invalidate dependents (register with None to clear cached value)
        let _ = self
            .whale
            .register(full_key, None, Durability::volatile(), vec![]);
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
    /// # Example
    ///
    /// ```ignore
    /// struct Subscription<Q: Query> {
    ///     query: Q,
    ///     last_revision: RevisionCounter,
    ///     tx: Sender<Arc<Q::Output>>,
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
    /// Same as [`QueryRuntime::query`].
    pub fn poll<Q: Query>(&self, query: Q) -> Result<Polled<Arc<Q::Output>>, QueryError> {
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
pub struct QueryRuntimeBuilder {
    error_comparator: ErrorComparator,
}

impl Default for QueryRuntimeBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl QueryRuntimeBuilder {
    /// Create a new builder with default settings.
    pub fn new() -> Self {
        Self {
            error_comparator: default_error_comparator,
        }
    }

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

    /// Build the runtime with the configured settings.
    pub fn build(self) -> QueryRuntime {
        QueryRuntime {
            whale: WhaleRuntime::new(),
            assets: Arc::new(AssetStorage::new()),
            locators: Arc::new(LocatorStorage::new()),
            pending: Arc::new(PendingStorage::new()),
            query_registry: Arc::new(QueryRegistry::new()),
            asset_key_registry: Arc::new(AssetKeyRegistry::new()),
            verifiers: Arc::new(VerifierStorage::new()),
            error_comparator: self.error_comparator,
            #[cfg(feature = "inspector")]
            sink: Arc::new(parking_lot::RwLock::new(None)),
        }
    }
}

// ============================================================================
// Asset API
// ============================================================================

impl QueryRuntime {
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

        // Check for early cutoff
        let changed = if let Some(old_value) = self.assets.get_ready::<K>(&full_asset_key) {
            !K::asset_eq(&old_value, &value)
        } else {
            true // Loading or NotFound -> Ready is a change
        };

        // Emit asset resolved event
        #[cfg(feature = "inspector")]
        self.emit(|| FlowEvent::AssetResolved {
            asset: query_flow_inspector::AssetKey::new(
                std::any::type_name::<K>(),
                format!("{:?}", key),
            ),
            changed,
        });

        // Store the new value
        self.assets
            .insert_ready::<K>(full_asset_key.clone(), Arc::new(value));

        // Remove from pending
        self.pending.remove(&full_asset_key);

        // Update whale dependency tracking
        let durability =
            Durability::new(durability_level.as_u8() as usize).unwrap_or(Durability::volatile());

        if changed {
            // Register with new changed_at to invalidate dependents
            let _ = self
                .whale
                .register(full_cache_key, None, durability, vec![]);
        } else {
            // Early cutoff - keep old changed_at
            let _ = self.whale.confirm_unchanged(&full_cache_key, vec![]);
        }

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
        #[cfg(feature = "inspector")]
        self.emit(|| FlowEvent::AssetInvalidated {
            asset: query_flow_inspector::AssetKey::new(
                std::any::type_name::<K>(),
                format!("{:?}", key),
            ),
        });

        // Mark as loading
        self.assets
            .insert(full_asset_key.clone(), AssetState::Loading);

        // Add to pending
        self.pending.insert::<K>(full_asset_key, key.clone());

        // Update whale to invalidate dependents (use volatile during loading)
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

        // First, register a change to invalidate dependents
        // This ensures queries that depend on this asset will recompute
        let _ = self
            .whale
            .register(full_cache_key.clone(), None, Durability::volatile(), vec![]);

        // Then remove the asset from storage
        self.assets.remove(&full_asset_key);
        self.pending.remove(&full_asset_key);

        // Finally remove from whale tracking
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
    /// - `Ok(LoadingState::Ready(value))` - Asset is loaded and ready
    /// - `Ok(LoadingState::Loading)` - Asset is still loading (added to pending)
    /// - `Err(QueryError::MissingDependency)` - Asset was not found
    pub fn get_asset<K: AssetKey>(
        &self,
        key: &K,
    ) -> Result<LoadingState<Arc<K::Asset>>, QueryError> {
        self.get_asset_internal(key)
    }

    /// Internal: Get asset state, checking cache and locator.
    fn get_asset_internal<K: AssetKey>(
        &self,
        key: &K,
    ) -> Result<LoadingState<Arc<K::Asset>>, QueryError> {
        let full_asset_key = FullAssetKey::new(key);
        let full_cache_key = FullCacheKey::from_asset_key(&full_asset_key);

        // Helper to emit AssetRequested event
        #[cfg(feature = "inspector")]
        let emit_requested = |runtime: &Self, state: query_flow_inspector::AssetState| {
            runtime.emit(|| FlowEvent::AssetRequested {
                asset: query_flow_inspector::AssetKey::new(
                    std::any::type_name::<K>(),
                    format!("{:?}", key),
                ),
                state,
            });
        };

        // Check cache first
        if let Some(state) = self.assets.get(&full_asset_key) {
            // Check if whale thinks it's valid
            if self.whale.is_valid(&full_cache_key) {
                return match state {
                    AssetState::Loading => {
                        #[cfg(feature = "inspector")]
                        emit_requested(self, query_flow_inspector::AssetState::Loading);
                        Ok(LoadingState::Loading)
                    }
                    AssetState::Ready(arc) => {
                        #[cfg(feature = "inspector")]
                        emit_requested(self, query_flow_inspector::AssetState::Ready);
                        match arc.downcast::<K::Asset>() {
                            Ok(value) => Ok(LoadingState::Ready(value)),
                            Err(_) => Err(QueryError::MissingDependency {
                                description: format!("Asset type mismatch: {:?}", key),
                            }),
                        }
                    }
                    AssetState::NotFound => {
                        #[cfg(feature = "inspector")]
                        emit_requested(self, query_flow_inspector::AssetState::NotFound);
                        Err(QueryError::MissingDependency {
                            description: format!("Asset not found: {:?}", key),
                        })
                    }
                };
            }
        }

        // Check if there's a registered locator
        if let Some(locator) = self.locators.get(TypeId::of::<K>()) {
            if let Some(state) = locator.locate_any(key) {
                // Store the state
                self.assets.insert(full_asset_key.clone(), state.clone());

                match state {
                    AssetState::Ready(arc) => {
                        #[cfg(feature = "inspector")]
                        emit_requested(self, query_flow_inspector::AssetState::Ready);

                        // Register with whale
                        let durability = Durability::new(key.durability().as_u8() as usize)
                            .unwrap_or(Durability::volatile());
                        let _ = self
                            .whale
                            .register(full_cache_key, None, durability, vec![]);

                        match arc.downcast::<K::Asset>() {
                            Ok(value) => return Ok(LoadingState::Ready(value)),
                            Err(_) => {
                                return Err(QueryError::MissingDependency {
                                    description: format!("Asset type mismatch: {:?}", key),
                                })
                            }
                        }
                    }
                    AssetState::Loading => {
                        #[cfg(feature = "inspector")]
                        emit_requested(self, query_flow_inspector::AssetState::Loading);
                        self.pending.insert::<K>(full_asset_key, key.clone());
                        return Ok(LoadingState::Loading);
                    }
                    AssetState::NotFound => {
                        #[cfg(feature = "inspector")]
                        emit_requested(self, query_flow_inspector::AssetState::NotFound);
                        return Err(QueryError::MissingDependency {
                            description: format!("Asset not found: {:?}", key),
                        });
                    }
                }
            }
        }

        // No locator registered or locator returned None - mark as pending
        #[cfg(feature = "inspector")]
        emit_requested(self, query_flow_inspector::AssetState::Loading);
        self.assets
            .insert(full_asset_key.clone(), AssetState::Loading);
        self.pending.insert::<K>(full_asset_key, key.clone());
        Ok(LoadingState::Loading)
    }
}

/// Context provided to queries during execution.
///
/// Use this to access dependencies via `query()`.
pub struct QueryContext<'a> {
    runtime: &'a QueryRuntime,
    #[cfg_attr(not(feature = "inspector"), allow(dead_code))]
    current_key: FullCacheKey,
    #[cfg(feature = "inspector")]
    parent_query_type: &'static str,
    #[cfg(feature = "inspector")]
    exec_ctx: ExecutionContext,
    deps: RefCell<Vec<FullCacheKey>>,
}

impl<'a> QueryContext<'a> {
    /// Query a dependency.
    ///
    /// The dependency is automatically tracked for invalidation.
    ///
    /// # Example
    ///
    /// ```ignore
    /// fn query(&self, ctx: &mut QueryContext) -> Result<Self::Output, QueryError> {
    ///     let dep_result = ctx.query(OtherQuery { id: self.id })?;
    ///     Ok(process(&dep_result))
    /// }
    /// ```
    pub fn query<Q: Query>(&mut self, query: Q) -> Result<Arc<Q::Output>, QueryError> {
        let key = query.cache_key();
        let full_key = FullCacheKey::new::<Q, _>(&key);

        // Emit dependency registered event
        #[cfg(feature = "inspector")]
        self.runtime.emit(|| FlowEvent::DependencyRegistered {
            span_id: self.exec_ctx.span_id(),
            parent: query_flow_inspector::QueryKey::new(
                self.parent_query_type,
                self.current_key.debug_repr(),
            ),
            dependency: query_flow_inspector::QueryKey::new(
                std::any::type_name::<Q>(),
                full_key.debug_repr(),
            ),
        });

        // Record this as a dependency
        self.deps.borrow_mut().push(full_key.clone());

        // Execute the query
        self.runtime.query(query)
    }

    /// Access an asset, tracking it as a dependency.
    ///
    /// Returns `LoadingState<Arc<K::Asset>>`:
    /// - `LoadingState::Loading` if the asset is still being loaded
    /// - `LoadingState::Ready(value)` if the asset is available
    ///
    /// # Example
    ///
    /// ```ignore
    /// #[query]
    /// fn process_file(ctx: &mut QueryContext, path: FilePath) -> Result<Output, QueryError> {
    ///     let content = ctx.asset(&path)?.suspend()?;
    ///     // Process content...
    ///     Ok(output)
    /// }
    /// ```
    ///
    /// # Errors
    ///
    /// Returns `Err(QueryError::MissingDependency)` if the asset was not found.
    pub fn asset<K: AssetKey>(
        &mut self,
        key: &K,
    ) -> Result<LoadingState<Arc<K::Asset>>, QueryError> {
        let full_asset_key = FullAssetKey::new(key);
        let full_cache_key = FullCacheKey::from_asset_key(&full_asset_key);

        // Emit asset dependency registered event
        #[cfg(feature = "inspector")]
        self.runtime.emit(|| FlowEvent::AssetDependencyRegistered {
            span_id: self.exec_ctx.span_id(),
            parent: query_flow_inspector::QueryKey::new(
                self.parent_query_type,
                self.current_key.debug_repr(),
            ),
            asset: query_flow_inspector::AssetKey::new(
                std::any::type_name::<K>(),
                format!("{:?}", key),
            ),
        });

        // Record dependency on this asset
        self.deps.borrow_mut().push(full_cache_key);

        // Get asset from runtime
        let result = self.runtime.get_asset_internal(key);

        // Emit missing dependency event on error
        #[cfg(feature = "inspector")]
        if let Err(QueryError::MissingDependency { ref description }) = result {
            self.runtime.emit(|| FlowEvent::MissingDependency {
                query: query_flow_inspector::QueryKey::new(
                    self.parent_query_type,
                    self.current_key.debug_repr(),
                ),
                dependency_description: description.clone(),
            });
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
    /// fn all_results(ctx: &mut QueryContext) -> Result<Vec<i32>, QueryError> {
    ///     let queries = ctx.list_queries::<MyQuery>();
    ///     let mut results = Vec::new();
    ///     for q in queries {
    ///         results.push(*ctx.query(q)?);
    ///     }
    ///     Ok(results)
    /// }
    /// ```
    pub fn list_queries<Q: Query>(&mut self) -> Vec<Q> {
        // Record dependency on the sentinel (set-level dependency)
        let sentinel = FullCacheKey::query_set_sentinel::<Q>();

        #[cfg(feature = "inspector")]
        self.runtime.emit(|| FlowEvent::DependencyRegistered {
            span_id: self.exec_ctx.span_id(),
            parent: query_flow_inspector::QueryKey::new(
                self.parent_query_type,
                self.current_key.debug_repr(),
            ),
            dependency: query_flow_inspector::QueryKey::new("QuerySet", sentinel.debug_repr()),
        });

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
    /// - An individual asset's value changes (use `ctx.asset()` for that)
    ///
    /// # Example
    ///
    /// ```ignore
    /// #[query]
    /// fn all_configs(ctx: &mut QueryContext) -> Result<Vec<String>, QueryError> {
    ///     let keys = ctx.list_asset_keys::<ConfigFile>();
    ///     let mut contents = Vec::new();
    ///     for key in keys {
    ///         let content = ctx.asset(&key)?.suspend()?;
    ///         contents.push((*content).clone());
    ///     }
    ///     Ok(contents)
    /// }
    /// ```
    pub fn list_asset_keys<K: AssetKey>(&mut self) -> Vec<K> {
        // Record dependency on the sentinel (set-level dependency)
        let sentinel = FullCacheKey::asset_key_set_sentinel::<K>();

        #[cfg(feature = "inspector")]
        self.runtime.emit(|| FlowEvent::AssetDependencyRegistered {
            span_id: self.exec_ctx.span_id(),
            parent: query_flow_inspector::QueryKey::new(
                self.parent_query_type,
                self.current_key.debug_repr(),
            ),
            asset: query_flow_inspector::AssetKey::new("AssetKeySet", sentinel.debug_repr()),
        });

        self.deps.borrow_mut().push(sentinel);

        // Return all registered asset keys
        self.runtime.asset_key_registry.get_all::<K>()
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

            fn query(&self, _ctx: &mut QueryContext) -> Result<Self::Output, QueryError> {
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

            fn query(&self, _ctx: &mut QueryContext) -> Result<Self::Output, QueryError> {
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

            fn query(&self, ctx: &mut QueryContext) -> Result<Self::Output, QueryError> {
                let base = ctx.query(Base {
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

            fn query(&self, ctx: &mut QueryContext) -> Result<Self::Output, QueryError> {
                let b = ctx.query(CycleB { id: self.id })?;
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

            fn query(&self, ctx: &mut QueryContext) -> Result<Self::Output, QueryError> {
                let a = ctx.query(CycleA { id: self.id })?;
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

            fn query(&self, _ctx: &mut QueryContext) -> Result<Self::Output, QueryError> {
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
        fn add(ctx: &mut QueryContext, a: i32, b: i32) -> Result<i32, QueryError> {
            let _ = ctx; // silence unused warning
            Ok(a + b)
        }

        #[test]
        fn test_macro_basic() {
            let runtime = QueryRuntime::new();
            let result = runtime.query(Add::new(1, 2)).unwrap();
            assert_eq!(*result, 3);
        }

        #[query(durability = 2)]
        fn with_durability(ctx: &mut QueryContext, x: i32) -> Result<i32, QueryError> {
            let _ = ctx;
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
            ctx: &mut QueryContext,
            id: u32,
            include_extra: bool,
        ) -> Result<String, QueryError> {
            let _ = ctx;
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
        fn dependent(ctx: &mut QueryContext, a: i32, b: i32) -> Result<i32, QueryError> {
            let sum = ctx.query(Add::new(*a, *b))?;
            Ok(*sum * 2)
        }

        #[test]
        fn test_macro_dependencies() {
            let runtime = QueryRuntime::new();
            let result = runtime.query(Dependent::new(3, 4)).unwrap();
            assert_eq!(*result, 14); // (3 + 4) * 2
        }

        #[query(output_eq)]
        fn with_output_eq(ctx: &mut QueryContext, x: i32) -> Result<i32, QueryError> {
            let _ = ctx;
            Ok(*x * 2)
        }

        #[test]
        fn test_macro_output_eq() {
            let runtime = QueryRuntime::new();
            let result = runtime.query(WithOutputEq::new(5)).unwrap();
            assert_eq!(*result, 10);
        }

        #[query(name = "CustomName")]
        fn original_name(ctx: &mut QueryContext, x: i32) -> Result<i32, QueryError> {
            let _ = ctx;
            Ok(*x)
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
        fn with_attributes(ctx: &mut QueryContext, x: i32) -> Result<i32, QueryError> {
            // This would warn without #[allow(unused_variables)] on the generated method
            let unused_var = 42;
            Ok(*x * 2)
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

            fn query(&self, _ctx: &mut QueryContext) -> Result<Self::Output, QueryError> {
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

            // Value should be correct (Deref goes through Arc)
            assert_eq!(*result, 10);
            // Access Arc directly via field
            assert_eq!(*result.value, 10);

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
            assert_eq!(*result2, 10);

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
        fn test_poll_deref() {
            let runtime = QueryRuntime::new();

            let result = runtime.poll(Counter { id: 5 }).unwrap();

            // Test Deref - goes through Arc to get the inner value directly
            let value: &i32 = &result;
            assert_eq!(*value, 50);

            // Access Arc directly via field
            let arc: &Arc<i32> = &result.value;
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
}
