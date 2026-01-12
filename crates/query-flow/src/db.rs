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
    ///
    /// Returns the asset value if ready, or `Err(QueryError::Suspend)` if still loading.
    /// Use this with the `?` operator for automatic suspension on loading.
    ///
    /// # Example
    ///
    /// ```ignore
    /// fn query(&self, db: &impl Db) -> Result<MyOutput, QueryError> {
    ///     let data = db.asset(key)?;  // Suspends if loading
    ///     Ok(process(&data))
    /// }
    /// ```
    fn asset<K: AssetKey>(&self, key: K) -> Result<Arc<K::Asset>, QueryError>;

    /// Access an asset's loading state by key.
    ///
    /// Unlike [`asset()`](Self::asset), this method returns the full loading state,
    /// allowing you to check if an asset is loading without triggering suspension.
    ///
    /// # Example
    ///
    /// ```ignore
    /// let state = db.asset_state(key)?;
    /// if state.is_loading() {
    ///     // Handle loading case explicitly
    /// } else {
    ///     let value = state.get().unwrap();
    /// }
    /// ```
    fn asset_state<K: AssetKey>(&self, key: K) -> Result<AssetLoadingState<K>, QueryError>;

    /// List all executed queries of a specific type.
    fn list_queries<Q: Query>(&self) -> Vec<Q>;

    /// List all resolved asset keys of a specific type.
    fn list_asset_keys<K: AssetKey>(&self) -> Vec<K>;
}
