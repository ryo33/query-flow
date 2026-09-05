//! Utility functions for output equality comparison in queries.
//!
//! These functions are designed to be used with the `#[query(output_eq = ...)]` attribute
//! when the output type is `Result<T, E>` and `E` does not implement `PartialEq`.

/// Compare only the `Ok` values. Returns `false` for any `Err` case,
/// causing downstream queries to be invalidated (recomputed).
///
/// # Example
/// ```
/// use query_flow::{query, Db, QueryError, QueryRuntime};
///
/// // Note: `MyError` deliberately has no `PartialEq`.
/// #[derive(Debug)]
/// struct MyError(String);
///
/// #[query(output_eq = query_flow::output_eq::ok_or_invalidate)]
/// fn my_query(db: &impl Db, succeed: bool) -> Result<Result<i32, MyError>, QueryError> {
///     let _ = db;
///     Ok(if succeed { Ok(1) } else { Err(MyError("boom".into())) })
/// }
///
/// let runtime = QueryRuntime::new();
/// assert!(matches!(*runtime.query(MyQuery::new(true)).unwrap(), Ok(1)));
/// assert!(matches!(*runtime.query(MyQuery::new(false)).unwrap(), Err(_)));
/// ```
pub fn ok_or_invalidate<T: PartialEq, E>(a: &Result<T, E>, b: &Result<T, E>) -> bool {
    match (a, b) {
        (Ok(a), Ok(b)) => a == b,
        _ => false,
    }
}

/// Compare `Ok` values for equality, treat all `Err` as equal.
///
/// Use this when you want to suppress downstream recomputation if both results are errors,
/// regardless of the error content.
///
/// # Example
/// ```
/// use query_flow::{query, Db, QueryError, QueryRuntime};
///
/// // Note: `MyError` deliberately has no `PartialEq`.
/// #[derive(Debug)]
/// struct MyError(String);
///
/// #[query(output_eq = query_flow::output_eq::ignore_err)]
/// fn my_query(db: &impl Db, succeed: bool) -> Result<Result<i32, MyError>, QueryError> {
///     let _ = db;
///     Ok(if succeed { Ok(1) } else { Err(MyError("boom".into())) })
/// }
///
/// let runtime = QueryRuntime::new();
/// assert!(matches!(*runtime.query(MyQuery::new(false)).unwrap(), Err(_)));
/// ```
pub fn ignore_err<T: PartialEq, E>(a: &Result<T, E>, b: &Result<T, E>) -> bool {
    match (a, b) {
        (Ok(a), Ok(b)) => a == b,
        (Err(_), Err(_)) => true,
        _ => false,
    }
}
