//! Query-Flow: A high-level query framework for incremental computation.
//!
//! Built on top of [`whale`], this crate provides a user-friendly API for defining
//! and executing queries with automatic caching and dependency tracking.
//!
//! # Key Features
//!
//! - **Async-agnostic queries**: Write sync query logic, run with sync or async runtime
//! - **Automatic caching**: Query results are cached and invalidated based on dependencies
//! - **Suspense pattern**: Handle async loading with `LoadingState` without coloring functions
//! - **Type-safe**: Per-query-type caching with compile-time guarantees
//! - **Early cutoff**: Skip downstream recomputation when values don't change
//!
//! # Example
//!
//! ```ignore
//! use query_flow::{query, QueryContext, QueryError, QueryRuntime};
//!
//! #[query]
//! fn add(ctx: &mut QueryContext, a: i32, b: i32) -> Result<i32, QueryError> {
//!     Ok(a + b)
//! }
//!
//! let runtime = QueryRuntime::new();
//! let result = runtime.query(Add::new(1, 2)).unwrap();
//! assert_eq!(*result, 3);
//! ```

// Allow the macro to reference query_flow types when used inside this crate
extern crate self as query_flow;

mod error;
mod key;
mod loading;
mod query;
mod runtime;
mod storage;

pub use error::QueryError;
pub use key::Key;
pub use loading::LoadingState;
pub use query::Query;
pub use query_flow_macros::query;
pub use runtime::{QueryContext, QueryRuntime};
