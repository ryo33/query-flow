//! Query trait definition.

use crate::key::Key;
use crate::runtime::QueryContext;
use crate::QueryError;

/// A query that can be executed and cached.
///
/// Queries are the fundamental unit of computation in query-flow. Each query:
/// - Has a cache key that uniquely identifies the computation
/// - Produces an output value
/// - Can depend on other queries via `QueryContext::query()`
///
/// # Sync by Design
///
/// The `query` method is intentionally synchronous. This avoids the "function
/// coloring" problem where async infects the entire call stack. For async
/// operations, use the suspense pattern with `LoadingState`.
///
/// # Error Handling
///
/// The `query` method returns `Result<Output, QueryError>` where:
/// - `QueryError` represents system errors (Suspend, Cycle, Cancelled)
/// - User domain errors should be wrapped in `Output`, e.g., `type Output = Result<T, MyError>`
///
/// This means fallible queries return `Ok(Ok(value))` on success and `Ok(Err(error))` on user error.
///
/// # Example
///
/// ```ignore
/// use query_flow::{Query, QueryContext, QueryError, Key};
///
/// // Simple infallible query
/// struct Add { a: i32, b: i32 }
///
/// impl Query for Add {
///     type CacheKey = (i32, i32);
///     type Output = i32;
///
///     fn cache_key(&self) -> Self::CacheKey {
///         (self.a, self.b)
///     }
///
///     fn query(&self, _ctx: &mut QueryContext) -> Result<Self::Output, QueryError> {
///         Ok(self.a + self.b)
///     }
/// }
///
/// // Fallible query with user errors
/// struct ParseInt { input: String }
///
/// impl Query for ParseInt {
///     type CacheKey = String;
///     type Output = Result<i32, std::num::ParseIntError>;
///
///     fn cache_key(&self) -> Self::CacheKey {
///         self.input.clone()
///     }
///
///     fn query(&self, _ctx: &mut QueryContext) -> Result<Self::Output, QueryError> {
///         Ok(self.input.parse())  // Ok(Ok(n)) or Ok(Err(parse_error))
///     }
/// }
/// ```
pub trait Query: Send + Sync + 'static {
    /// The cache key type for this query.
    ///
    /// Two queries with the same cache key are considered equivalent and
    /// will share cached results.
    type CacheKey: Key;

    /// The output type of this query.
    ///
    /// For fallible queries, use `Result<T, E>` here.
    type Output: Send + Sync + 'static;

    /// Get the cache key for this query instance.
    fn cache_key(&self) -> Self::CacheKey;

    /// Execute the query, returning the output or a system error.
    ///
    /// # Arguments
    ///
    /// * `ctx` - The query context for accessing dependencies
    ///
    /// # Returns
    ///
    /// * `Ok(output)` - Query completed successfully
    /// * `Err(QueryError::Suspend)` - Query is waiting for async loading
    /// * `Err(QueryError::Cycle)` - Dependency cycle detected
    fn query(&self, ctx: &mut QueryContext) -> Result<Self::Output, QueryError>;

    /// Whether this query should never be cached.
    ///
    /// If true, this query will always be re-executed. However, downstream
    /// queries that depend on this one can still be cached.
    ///
    /// Use cases:
    /// - Queries that read external state that changes frequently
    /// - Queries where caching overhead exceeds computation cost
    ///
    /// Default: `false` (queries are cached)
    fn never_cache(&self) -> bool {
        false
    }

    /// Durability hint for this query.
    ///
    /// Higher values indicate the query's output changes less frequently.
    /// This is used for optimization in the dependency tracking layer.
    ///
    /// - 0: Volatile (changes frequently)
    /// - Higher: More stable
    ///
    /// Default: `0` (volatile)
    fn durability(&self) -> u8 {
        0
    }

    /// Compare two outputs for equality (for early cutoff optimization).
    ///
    /// When a query is recomputed and the output is equal to the previous
    /// output, downstream queries can skip recomputation (early cutoff).
    ///
    /// Default: `false` (always propagate changes)
    ///
    /// Override this for queries where:
    /// - Output comparison is cheap
    /// - Output often doesn't change even when dependencies do
    fn output_eq(_old: &Self::Output, _new: &Self::Output) -> bool {
        false
    }
}
