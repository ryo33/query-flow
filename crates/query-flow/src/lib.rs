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
//! use query_flow::{Query, QueryContext, QueryError, QueryRuntime};
//!
//! struct Add { a: i32, b: i32 }
//!
//! impl Query for Add {
//!     type CacheKey = (i32, i32);
//!     type Output = i32;
//!
//!     fn cache_key(&self) -> Self::CacheKey {
//!         (self.a, self.b)
//!     }
//!
//!     fn query(&self, _ctx: &mut QueryContext) -> Result<Self::Output, QueryError> {
//!         Ok(self.a + self.b)
//!     }
//! }
//!
//! let runtime = QueryRuntime::new();
//! let result = runtime.query(Add { a: 1, b: 2 }).unwrap();
//! assert_eq!(*result, 3);
//! ```

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
pub use runtime::{QueryContext, QueryRuntime};
