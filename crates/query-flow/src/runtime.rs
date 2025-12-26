//! Query runtime and context.

use std::any::TypeId;
use std::cell::RefCell;
use std::sync::Arc;

use whale::{Durability, Runtime as WhaleRuntime};

use crate::asset::{AssetKey, AssetLocator, DurabilityLevel, FullAssetKey, PendingAsset};
use crate::key::FullCacheKey;
use crate::loading::LoadingState;
use crate::query::Query;
use crate::storage::{AssetState, AssetStorage, CacheStorage, LocatorStorage, PendingStorage};
use crate::QueryError;

#[cfg(feature = "inspector")]
use query_flow_inspector::{EventSink, FlowEvent, SpanId};

/// Number of durability levels (matches whale's default).
const DURABILITY_LEVELS: usize = 4;

// Thread-local query execution stack for cycle detection.
thread_local! {
    static QUERY_STACK: RefCell<Vec<FullCacheKey>> = const { RefCell::new(Vec::new()) };
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
    /// Whale runtime for dependency tracking
    whale: WhaleRuntime<FullCacheKey, (), DURABILITY_LEVELS>,
    /// Cache for query outputs
    cache: Arc<CacheStorage>,
    /// Asset cache and state storage
    assets: Arc<AssetStorage>,
    /// Registered asset locators
    locators: Arc<LocatorStorage>,
    /// Pending asset requests
    pending: Arc<PendingStorage>,
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
            cache: self.cache.clone(),
            assets: self.assets.clone(),
            locators: self.locators.clone(),
            pending: self.pending.clone(),
            #[cfg(feature = "inspector")]
            sink: self.sink.clone(),
        }
    }
}

impl QueryRuntime {
    /// Create a new query runtime.
    pub fn new() -> Self {
        Self {
            whale: WhaleRuntime::new(),
            cache: Arc::new(CacheStorage::new()),
            assets: Arc::new(AssetStorage::new()),
            locators: Arc::new(LocatorStorage::new()),
            pending: Arc::new(PendingStorage::new()),
            #[cfg(feature = "inspector")]
            sink: Arc::new(parking_lot::RwLock::new(None)),
        }
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
        let key = query.cache_key();
        let full_key = FullCacheKey::new::<Q, _>(&key);

        // Generate span ID and emit start event
        #[cfg(feature = "inspector")]
        let span_id = query_flow_inspector::new_span_id();
        #[cfg(feature = "inspector")]
        let start_time = std::time::Instant::now();
        #[cfg(feature = "inspector")]
        let query_key = query_flow_inspector::QueryKey::new(
            std::any::type_name::<Q>(),
            full_key.debug_repr(),
        );

        #[cfg(feature = "inspector")]
        self.emit(|| FlowEvent::QueryStart {
            span_id,
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
                span_id,
                query: query_key.clone(),
                result: query_flow_inspector::ExecutionResult::CycleDetected,
                duration: start_time.elapsed(),
            });

            return Err(QueryError::Cycle { path });
        }

        // Check if cached and valid
        if let Some(cached) = self.get_cached_if_valid::<Q>(&full_key) {
            #[cfg(feature = "inspector")]
            self.emit(|| FlowEvent::CacheCheck {
                span_id,
                query: query_key.clone(),
                valid: true,
            });

            #[cfg(feature = "inspector")]
            self.emit(|| FlowEvent::QueryEnd {
                span_id,
                query: query_key.clone(),
                result: query_flow_inspector::ExecutionResult::CacheHit,
                duration: start_time.elapsed(),
            });

            return Ok(cached);
        }

        #[cfg(feature = "inspector")]
        self.emit(|| FlowEvent::CacheCheck {
            span_id,
            query: query_key.clone(),
            valid: false,
        });

        // Execute the query with cycle tracking
        QUERY_STACK.with(|stack| {
            stack.borrow_mut().push(full_key.clone());
        });

        #[cfg(feature = "inspector")]
        let result = self.execute_query::<Q>(&query, &full_key, span_id);
        #[cfg(not(feature = "inspector"))]
        let result = self.execute_query::<Q>(&query, &full_key);

        QUERY_STACK.with(|stack| {
            stack.borrow_mut().pop();
        });

        // Emit end event
        #[cfg(feature = "inspector")]
        {
            let exec_result = match &result {
                Ok((_, true)) => query_flow_inspector::ExecutionResult::Changed,
                Ok((_, false)) => query_flow_inspector::ExecutionResult::Unchanged,
                Err(QueryError::Suspend) => query_flow_inspector::ExecutionResult::Suspended,
                Err(QueryError::Cycle { .. }) => {
                    query_flow_inspector::ExecutionResult::CycleDetected
                }
                Err(e) => query_flow_inspector::ExecutionResult::Error {
                    message: format!("{:?}", e),
                },
            };
            self.emit(|| FlowEvent::QueryEnd {
                span_id,
                query: query_key.clone(),
                result: exec_result,
                duration: start_time.elapsed(),
            });
        }

        result.map(|(output, _)| output)
    }

    /// Execute a query, caching the result if appropriate.
    ///
    /// Returns (output, output_changed) tuple for instrumentation.
    #[cfg(feature = "inspector")]
    fn execute_query<Q: Query>(
        &self,
        query: &Q,
        full_key: &FullCacheKey,
        span_id: SpanId,
    ) -> Result<(Arc<Q::Output>, bool), QueryError> {
        // Create context for this query execution
        let mut ctx = QueryContext {
            runtime: self,
            current_key: full_key.clone(),
            parent_query_type: std::any::type_name::<Q>(),
            span_id,
            deps: RefCell::new(Vec::new()),
        };

        // Execute the query
        let output = query.query(&mut ctx)?;
        let output = Arc::new(output);

        // Get collected dependencies
        let deps: Vec<FullCacheKey> = ctx.deps.borrow().clone();

        // Check if output changed (for early cutoff)
        let output_changed = if let Some(old) = self.cache.get::<Q>(full_key) {
            !Q::output_eq(&old, &output)
        } else {
            true // No previous value, so "changed"
        };

        // Emit early cutoff check event
        self.emit(|| FlowEvent::EarlyCutoffCheck {
            span_id,
            query: query_flow_inspector::QueryKey::new(
                std::any::type_name::<Q>(),
                full_key.debug_repr(),
            ),
            output_changed,
        });

        // Update cache
        self.cache.insert::<Q>(full_key.clone(), output.clone());

        // Update whale dependency tracking
        let durability =
            Durability::new(query.durability() as usize).unwrap_or(Durability::volatile());

        if output_changed {
            // Register with new changed_at
            let _ = self.whale.register(full_key.clone(), (), durability, deps);
        } else {
            // Early cutoff: keep old changed_at
            let _ = self.whale.confirm_unchanged(full_key, deps);
        }

        Ok((output, output_changed))
    }

    /// Execute a query, caching the result if appropriate.
    ///
    /// Returns (output, output_changed) tuple for instrumentation.
    #[cfg(not(feature = "inspector"))]
    fn execute_query<Q: Query>(
        &self,
        query: &Q,
        full_key: &FullCacheKey,
    ) -> Result<(Arc<Q::Output>, bool), QueryError> {
        // Create context for this query execution
        let mut ctx = QueryContext {
            runtime: self,
            current_key: full_key.clone(),
            deps: RefCell::new(Vec::new()),
        };

        // Execute the query
        let output = query.query(&mut ctx)?;
        let output = Arc::new(output);

        // Get collected dependencies
        let deps: Vec<FullCacheKey> = ctx.deps.borrow().clone();

        // Check if output changed (for early cutoff)
        let output_changed = if let Some(old) = self.cache.get::<Q>(full_key) {
            !Q::output_eq(&old, &output)
        } else {
            true // No previous value, so "changed"
        };

        // Update cache
        self.cache.insert::<Q>(full_key.clone(), output.clone());

        // Update whale dependency tracking
        let durability =
            Durability::new(query.durability() as usize).unwrap_or(Durability::volatile());

        if output_changed {
            // Register with new changed_at
            let _ = self.whale.register(full_key.clone(), (), durability, deps);
        } else {
            // Early cutoff: keep old changed_at
            let _ = self.whale.confirm_unchanged(full_key, deps);
        }

        Ok((output, output_changed))
    }

    /// Get cached value if it's still valid.
    fn get_cached_if_valid<Q: Query>(&self, full_key: &FullCacheKey) -> Option<Arc<Q::Output>> {
        // Check whale validity first
        if !self.whale.is_valid(full_key) {
            return None;
        }

        // Then check if we have the cached value
        self.cache.get::<Q>(full_key)
    }

    /// Invalidate a query, forcing recomputation on next access.
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

        self.cache.remove(&full_key);
        // Whale will detect invalidity via is_valid check
    }

    /// Clear all cached values.
    pub fn clear_cache(&self) {
        self.cache.clear();
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
        self.assets.insert_ready::<K>(full_asset_key.clone(), Arc::new(value));

        // Remove from pending
        self.pending.remove(&full_asset_key);

        // Update whale dependency tracking
        let durability = Durability::new(durability_level.as_u8() as usize)
            .unwrap_or(Durability::volatile());

        if changed {
            // Register with new changed_at to invalidate dependents
            let _ = self.whale.register(full_cache_key, (), durability, vec![]);
        } else {
            // Early cutoff - keep old changed_at
            let _ = self.whale.confirm_unchanged(&full_cache_key, vec![]);
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
        self.assets.insert(full_asset_key.clone(), AssetState::Loading);

        // Add to pending
        self.pending.insert::<K>(full_asset_key, key.clone());

        // Update whale to invalidate dependents (use volatile during loading)
        let _ = self.whale.register(full_cache_key, (), Durability::volatile(), vec![]);
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
        let _ = self.whale.register(full_cache_key.clone(), (), Durability::volatile(), vec![]);

        // Then remove the asset from storage
        self.assets.remove(&full_asset_key);
        self.pending.remove(&full_asset_key);

        // Finally remove from whale tracking
        self.whale.remove(&full_cache_key);
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
                        let _ = self.whale.register(full_cache_key, (), durability, vec![]);

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
        self.assets.insert(full_asset_key.clone(), AssetState::Loading);
        self.pending.insert::<K>(full_asset_key, key.clone());
        Ok(LoadingState::Loading)
    }
}

/// Context provided to queries during execution.
///
/// Use this to access dependencies via `query()`.
#[cfg(feature = "inspector")]
pub struct QueryContext<'a> {
    runtime: &'a QueryRuntime,
    current_key: FullCacheKey,
    parent_query_type: &'static str,
    span_id: SpanId,
    deps: RefCell<Vec<FullCacheKey>>,
}

/// Context provided to queries during execution.
///
/// Use this to access dependencies via `query()`.
#[cfg(not(feature = "inspector"))]
pub struct QueryContext<'a> {
    runtime: &'a QueryRuntime,
    #[allow(dead_code)]
    current_key: FullCacheKey,
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
            span_id: self.span_id,
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
            span_id: self.span_id,
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
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_query() {
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
        struct CycleA {
            id: i32,
        }

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
            let r1 = runtime
                .query(WithKeySelection::new(1, true))
                .unwrap();
            let r2 = runtime
                .query(WithKeySelection::new(1, false))
                .unwrap();

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
    }
}
