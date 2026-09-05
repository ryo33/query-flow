//! Database trait for query execution.

use std::sync::Arc;

use crate::asset::AssetKey;
use crate::loading::AssetLoadingState;
use crate::query::Query;
use crate::QueryError;

/// Database trait that provides query execution and asset access.
///
/// This trait is implemented by both [`QueryRuntime`](crate::QueryRuntime) and
/// the internal `QueryContext`, allowing queries to work with either.
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
    /// ```
    /// use query_flow::{asset_key, query, Db, DurabilityLevel, QueryError, QueryRuntime};
    ///
    /// #[asset_key(asset = String)]
    /// struct SourceFile(String);
    ///
    /// #[query]
    /// fn line_count(db: &impl Db, name: String) -> Result<usize, QueryError> {
    ///     let text = db.asset(SourceFile(name))?; // Suspends if loading
    ///     Ok(text.lines().count())
    /// }
    ///
    /// let runtime = QueryRuntime::new();
    /// runtime.resolve_asset(
    ///     SourceFile("a".into()),
    ///     "one\ntwo\n".into(),
    ///     DurabilityLevel::Volatile,
    /// );
    /// assert_eq!(*runtime.query(LineCount::new("a".into())).unwrap(), 2);
    /// ```
    fn asset<K: AssetKey>(&self, key: K) -> Result<Arc<K::Asset>, QueryError>;

    /// Access an asset's loading state by key.
    ///
    /// Unlike [`asset()`](Self::asset), this method returns the full loading state,
    /// allowing you to check if an asset is loading without triggering suspension.
    ///
    /// # Example
    ///
    /// ```
    /// use query_flow::{asset_key, query, Db, DurabilityLevel, QueryError, QueryRuntime};
    ///
    /// #[asset_key(asset = String)]
    /// struct SourceFile(String);
    ///
    /// #[query]
    /// fn describe(db: &impl Db, name: String) -> Result<String, QueryError> {
    ///     let state = db.asset_state(SourceFile(name))?;
    ///     if state.is_loading() {
    ///         // Handle loading case explicitly, without suspending.
    ///         Ok("loading".to_string())
    ///     } else {
    ///         let value = state.get().unwrap();
    ///         Ok(format!("{} bytes", value.len()))
    ///     }
    /// }
    ///
    /// let runtime = QueryRuntime::new();
    /// runtime.resolve_asset(
    ///     SourceFile("a".into()),
    ///     "hello".into(),
    ///     DurabilityLevel::Volatile,
    /// );
    /// assert_eq!(*runtime.query(Describe::new("a".into())).unwrap(), "5 bytes");
    /// ```
    fn asset_state<K: AssetKey>(&self, key: K) -> Result<AssetLoadingState<K>, QueryError>;

    /// List all executed queries of a specific type.
    fn list_queries<Q: Query>(&self) -> Vec<Q>;

    /// List all resolved asset keys of a specific type.
    fn list_asset_keys<K: AssetKey>(&self) -> Vec<K>;
}
