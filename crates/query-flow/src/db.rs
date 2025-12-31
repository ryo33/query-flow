//! Database trait for query execution.

use std::sync::Arc;

use crate::asset::AssetKey;
use crate::loading::AssetLoadingState;
use crate::query::Query;
use crate::QueryError;

/// Database trait that provides query execution and asset access.
///
/// This trait is implemented by both [`QueryRuntime`](crate::QueryRuntime) and
/// [`QueryContext`](crate::QueryContext), allowing queries to work with either.
///
/// - `QueryRuntime::query()` / `QueryRuntime::asset()`: No dependency tracking
/// - `QueryContext::query()` / `QueryContext::asset()`: With dependency tracking
pub trait Db {
    /// Execute a query, returning the cached result if available.
    fn query<Q: Query>(&self, query: Q) -> Result<Arc<Q::Output>, QueryError>;

    /// Access an asset by key.
    fn asset<K: AssetKey>(&self, key: K) -> Result<AssetLoadingState<K>, QueryError>;

    /// List all executed queries of a specific type.
    fn list_queries<Q: Query>(&self) -> Vec<Q>;

    /// List all resolved asset keys of a specific type.
    fn list_asset_keys<K: AssetKey>(&self) -> Vec<K>;
}
