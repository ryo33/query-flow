//! Query-Flow: A high-level query framework for incremental computation.
//!
//! Built on top of [`whale`], this crate provides a user-friendly API for defining
//! and executing queries with automatic caching and dependency tracking.
//!
//! # Key Features
//!
//! - **Async-agnostic queries**: Write sync query logic, run with sync or async runtime
//! - **Automatic caching**: Query results are cached and invalidated based on dependencies
//! - **Suspense pattern**: Handle async loading with `AssetLoadingState` without coloring functions
//! - **Type-safe**: Per-query-type caching with compile-time guarantees
//! - **Early cutoff**: Skip downstream recomputation when values don't change
//! - **External GC support**: Build custom garbage collection strategies using the Tracer API
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
//!
//! # Garbage Collection
//!
//! Query-flow provides primitives for implementing custom GC strategies externally:
//!
//! - [`Tracer::on_query_key`] - Track query access for LRU/TTL algorithms
//! - [`QueryRuntime::query_keys`] - Enumerate all cached queries
//! - [`QueryRuntime::remove`] / [`QueryRuntime::remove_if_unused`] - Remove queries by [`FullCacheKey`]
//! - [`QueryRuntime::remove_query`] / [`QueryRuntime::remove_query_if_unused`] - Remove queries by typed key
//!
//! See the [`tracer`] module and GC methods on [`QueryRuntime`] for details.

// Allow the macro to reference query_flow types when used inside this crate
extern crate self as query_flow;

mod asset;
mod db;
mod error;
mod key;
mod loading;
pub mod output_eq;
mod query;
mod runtime;
mod storage;
pub mod tracer;

pub use asset::{AssetKey, AssetLocator, DurabilityLevel, LocateResult, PendingAsset};
pub use db::Db;
pub use error::{QueryError, QueryResultExt, TypedErr};
pub use key::{
    AssetCacheKey, AssetKeySetSentinelKey, CacheKey, FullCacheKey, QueryCacheKey,
    QuerySetSentinelKey,
};
pub use loading::AssetLoadingState;
pub use query::Query;
pub use query_flow_macros::{asset_key, asset_locator, query};
pub use runtime::{ErrorComparator, Polled, QueryContext, QueryRuntime, QueryRuntimeBuilder};
pub use tracer::{ExecutionResult, InvalidationReason, NoopTracer, SpanId, Tracer, TracerAssetState};

// Re-export RevisionCounter from whale for use with poll() and changed_at()
pub use whale::RevisionCounter;
