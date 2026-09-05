//! Query trait definition.

use std::sync::Arc;

use crate::db::Db;
use crate::key::CacheKey;
use crate::QueryError;

/// A query that can be executed and cached.
///
/// Queries are the fundamental unit of computation in query-flow. Each query:
/// - Is itself the cache key (implements `Hash + Eq`)
/// - Produces an output value
/// - Can depend on other queries via `db.query()`
///
/// # Sync by Design
///
/// The `query` method is intentionally synchronous. This avoids the "function
/// coloring" problem where async infects the entire call stack. For async
/// operations, use the suspense pattern with `AssetLoadingState`.
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
/// ```
/// use std::sync::Arc;
///
/// use query_flow::{Query, Db, QueryError};
///
/// // Simple infallible query
/// #[derive(Clone, Debug, Hash, PartialEq, Eq)]
/// struct Add { a: i32, b: i32 }
///
/// impl Query for Add {
///     type Output = i32;
///
///     fn query(self, _db: &impl Db) -> Result<Arc<Self::Output>, QueryError> {
///         Ok(Arc::new(self.a + self.b))
///     }
///
///     fn output_eq(old: &Self::Output, new: &Self::Output) -> bool {
///         old == new
///     }
/// }
///
/// // Fallible query with user errors
/// #[derive(Clone, Debug, Hash, PartialEq, Eq)]
/// struct ParseInt { input: String }
///
/// impl Query for ParseInt {
///     type Output = Result<i32, std::num::ParseIntError>;
///
///     fn query(self, _db: &impl Db) -> Result<Arc<Self::Output>, QueryError> {
///         Ok(Arc::new(self.input.parse()))  // Ok(Arc(Ok(n))) or Ok(Arc(Err(parse_error)))
///     }
///
///     fn output_eq(old: &Self::Output, new: &Self::Output) -> bool {
///         old == new
///     }
/// }
/// ```
pub trait Query: CacheKey + Clone + Send + Sync + 'static {
    /// The output type of this query.
    ///
    /// For fallible queries, use `Result<T, E>` here.
    type Output: Send + Sync + 'static;

    /// Execute the query, returning the output wrapped in Arc or a system error.
    ///
    /// The result is wrapped in `Arc` for efficient sharing in the cache.
    /// Use the `#[query]` macro to automatically handle Arc wrapping.
    ///
    /// # Arguments
    ///
    /// * `db` - The database for accessing dependencies
    ///
    /// # Returns
    ///
    /// * `Ok(arc_output)` - Query completed successfully
    /// * `Err(QueryError::Suspend)` - Query is waiting for async loading
    /// * `Err(QueryError::Cycle)` - Dependency cycle detected
    fn query(self, db: &impl Db) -> Result<Arc<Self::Output>, QueryError>;

    /// Compare two outputs for equality (for early cutoff optimization).
    ///
    /// When a query is recomputed and the output is equal to the previous
    /// output, downstream queries can skip recomputation (early cutoff).
    ///
    /// The `#[query]` macro generates this using `PartialEq` by default.
    /// Use `output_eq = custom_fn` for types without `PartialEq`.
    fn output_eq(old: &Self::Output, new: &Self::Output) -> bool;
}

/// Convenience trait for query output types.
///
/// This trait combines the bounds needed for a type to be used as a query output:
/// `PartialEq + Send + Sync + 'static`.
///
/// - `PartialEq` is required for the default `output_eq` comparison (early cutoff optimization)
/// - `Send + Sync + 'static` allows the output to be cached and shared across threads
///
/// # When to Use
///
/// Use `QueryOutput` for generic type parameters that appear only in query output:
///
/// ```
/// use std::fmt::Display;
/// use std::str::FromStr;
///
/// use query_flow::{query, Db, QueryError, QueryOutput, QueryRuntime};
///
/// #[query]
/// fn parse<T: QueryOutput + FromStr>(db: &impl Db, text: String) -> Result<T, QueryError>
/// where
///     T::Err: Display,
/// {
///     let _ = db;
///     text.parse().map_err(|e| anyhow::anyhow!("{}", e).into())
/// }
///
/// let runtime = QueryRuntime::new();
/// assert_eq!(*runtime.query(Parse::<i32>::new("42".into())).unwrap(), 42);
/// assert_eq!(*runtime.query(Parse::<u64>::new("42".into())).unwrap(), 42u64);
/// ```
///
/// # When Not to Use
///
/// If you supply a custom comparator with `#[query(output_eq = path)]`, the output
/// does not need `PartialEq`. In that case, use raw bounds instead:
///
/// ```
/// use query_flow::{query, Db, QueryError, QueryRuntime};
///
/// // No `PartialEq` on `T`, so the comparator is supplied explicitly.
/// // Returning `false` disables early cutoff: dependents always recompute.
/// fn always_recompute<T>(_old: &T, _new: &T) -> bool {
///     false
/// }
///
/// #[query(output_eq = always_recompute)]
/// fn create<T: Default + Send + Sync + 'static>(db: &impl Db) -> Result<T, QueryError> {
///     let _ = db;
///     Ok(T::default())
/// }
///
/// let runtime = QueryRuntime::new();
/// assert_eq!(*runtime.query(Create::<i32>::new()).unwrap(), 0);
/// ```
pub trait QueryOutput: PartialEq + Send + Sync + 'static {}
impl<T: PartialEq + Send + Sync + 'static> QueryOutput for T {}
