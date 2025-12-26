//! Query runtime and context.

use std::any::TypeId;
use std::cell::RefCell;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

use whale::{Durability, Runtime as WhaleRuntime};

use crate::key::FullCacheKey;
use crate::query::Query;
use crate::storage::{CacheStorage, LoadedStorage};
use crate::QueryError;

/// Number of durability levels (matches whale's default).
const DURABILITY_LEVELS: usize = 4;

// Thread-local query execution stack for cycle detection.
thread_local! {
    static QUERY_STACK: RefCell<Vec<FullCacheKey>> = RefCell::new(Vec::new());
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
    /// Storage for values loaded by background tasks
    loaded: Arc<LoadedStorage>,
    /// Sender for notifying when loaded values are ready
    notify: Arc<Notify>,
}

/// Simple notification mechanism for background task completion.
///
/// This is a placeholder for now - real async support would use
/// tokio::sync::Notify or similar.
struct Notify;

impl Default for Notify {
    fn default() -> Self {
        Self::new()
    }
}

impl Notify {
    fn new() -> Self {
        Self
    }

    #[allow(dead_code)]
    fn notify_waiters(&self) {
        // TODO: Implement proper notification when async feature is added
    }
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
            loaded: self.loaded.clone(),
            notify: self.notify.clone(),
        }
    }
}

impl QueryRuntime {
    /// Create a new query runtime.
    pub fn new() -> Self {
        Self {
            whale: WhaleRuntime::new(),
            cache: Arc::new(CacheStorage::new()),
            loaded: Arc::new(LoadedStorage::new()),
            notify: Arc::new(Notify::new()),
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

        // Check for cycles using thread-local stack
        let cycle_detected = QUERY_STACK.with(|stack| {
            let stack = stack.borrow();
            stack.iter().any(|k| k == &full_key)
        });

        if cycle_detected {
            let path = QUERY_STACK.with(|stack| {
                let stack = stack.borrow();
                let mut path: Vec<String> = stack.iter().map(|k| k.debug_repr().to_string()).collect();
                path.push(full_key.debug_repr().to_string());
                path
            });
            return Err(QueryError::Cycle { path });
        }

        // Check if cached and valid
        if let Some(cached) = self.get_cached_if_valid::<Q>(&full_key) {
            return Ok(cached);
        }

        // Execute the query with cycle tracking
        QUERY_STACK.with(|stack| {
            stack.borrow_mut().push(full_key.clone());
        });

        let result = self.execute_query(&query, &full_key);

        QUERY_STACK.with(|stack| {
            stack.borrow_mut().pop();
        });

        result
    }

    /// Execute a query, caching the result if appropriate.
    fn execute_query<Q: Query>(
        &self,
        query: &Q,
        full_key: &FullCacheKey,
    ) -> Result<Arc<Q::Output>, QueryError> {
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

        Ok(output)
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

    /// Get a loaded value from background task storage.
    pub(crate) fn get_loaded<T: Send + Sync + 'static, K: Hash>(
        &self,
        type_id: TypeId,
        key: &K,
    ) -> Option<Arc<T>> {
        let mut hasher = ahash::AHasher::default();
        key.hash(&mut hasher);
        let key_hash = hasher.finish();
        self.loaded.get::<T>(type_id, key_hash)
    }

    /// Store a loaded value and notify waiters.
    pub(crate) fn set_loaded<T: Send + Sync + 'static, K: Hash>(
        &self,
        type_id: TypeId,
        key: &K,
        value: T,
    ) {
        let mut hasher = ahash::AHasher::default();
        key.hash(&mut hasher);
        let key_hash = hasher.finish();
        self.loaded.insert::<T>(type_id, key_hash, Arc::new(value));
        self.notify.notify_waiters();
    }

    /// Invalidate a query, forcing recomputation on next access.
    pub fn invalidate<Q: Query>(&self, key: &Q::CacheKey) {
        let full_key = FullCacheKey::new::<Q, _>(key);
        self.cache.remove(&full_key);
        // Whale will detect invalidity via is_valid check
    }

    /// Clear all cached values.
    pub fn clear_cache(&self) {
        self.cache.clear();
    }
}

/// Context provided to queries during execution.
///
/// Use this to access dependencies via `query()`.
pub struct QueryContext<'a> {
    runtime: &'a QueryRuntime,
    #[allow(dead_code)] // Reserved for future use (e.g., for debugging, tracing)
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

        // Record this as a dependency
        self.deps.borrow_mut().push(full_key.clone());

        // Execute the query
        self.runtime.query(query)
    }

    /// Get a previously loaded value from a background task.
    ///
    /// Returns `None` if the value hasn't been loaded yet.
    pub fn get_loaded<T: Send + Sync + 'static, K: Hash>(&self, key: &K) -> Option<Arc<T>> {
        self.runtime.get_loaded::<T, K>(TypeId::of::<T>(), key)
    }

    /// Get access to the runtime for spawning background tasks.
    pub fn runtime(&self) -> &QueryRuntime {
        self.runtime
    }
}

/// Handle for spawning background loading tasks.
impl QueryRuntime {
    /// Spawn a background task that will load a value using a thread.
    ///
    /// When the task completes, the value will be stored and any suspended
    /// queries will be able to proceed on their next execution.
    ///
    /// # Example
    ///
    /// ```ignore
    /// fn query(&self, ctx: &mut QueryContext) -> Result<Self::Output, QueryError> {
    ///     // Check if already loaded
    ///     if let Some(content) = ctx.get_loaded::<String, _>(&self.path) {
    ///         return Ok((*content).clone());
    ///     }
    ///
    ///     // Spawn background loader
    ///     let runtime = ctx.runtime().clone();
    ///     let path = self.path.clone();
    ///     runtime.spawn_loader(&path, move || {
    ///         std::fs::read_to_string(&path).unwrap()
    ///     });
    ///
    ///     Err(QueryError::Suspend)
    /// }
    /// ```
    pub fn spawn_loader<T, K, F>(&self, key: &K, loader: F)
    where
        T: Send + Sync + 'static,
        K: Hash + Clone + Send + 'static,
        F: FnOnce() -> T + Send + 'static,
    {
        let runtime = self.clone();
        let type_id = TypeId::of::<T>();
        let key = key.clone();
        std::thread::spawn(move || {
            let value = loader();
            runtime.set_loaded::<T, K>(type_id, &key, value);
        });
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
