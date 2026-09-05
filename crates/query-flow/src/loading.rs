//! Loading state for async resource handling.

use std::sync::Arc;

use crate::asset::{AssetKey, PendingAsset};
use crate::QueryError;

/// Loading state with asset key information for error reporting.
///
/// This is returned by [`Db::asset_state()`](crate::Db::asset_state) and provides
/// information about whether an asset is loading or ready.
///
/// For most use cases, prefer [`Db::asset()`](crate::Db::asset) which automatically
/// suspends on loading. Use `asset_state()` when you need to explicitly check
/// the loading state without triggering suspension.
///
/// # Example
///
/// ```
/// use query_flow::{asset_key, query, Db, DurabilityLevel, QueryError, QueryRuntime};
///
/// #[asset_key(asset = String)]
/// struct FilePath(String);
///
/// #[query]
/// fn process_file(db: &impl Db, path: FilePath) -> Result<usize, QueryError> {
///     // Most common: just use db.asset() which suspends automatically
///     let content = db.asset(path)?;
///     Ok(content.len())
/// }
///
/// #[query]
/// fn check_loading(db: &impl Db, path: FilePath) -> Result<bool, QueryError> {
///     // Use asset_state() when you need to check loading status explicitly
///     let state = db.asset_state(path)?;
///     Ok(state.is_loading())
/// }
///
/// let runtime = QueryRuntime::new();
/// runtime.resolve_asset(
///     FilePath("a".into()),
///     "hello".into(),
///     DurabilityLevel::Volatile,
/// );
/// assert_eq!(*runtime.query(ProcessFile::new(FilePath("a".into()))).unwrap(), 5);
/// assert!(!*runtime.query(CheckLoading::new(FilePath("a".into()))).unwrap());
/// ```
pub struct AssetLoadingState<K: AssetKey> {
    value: Option<Arc<K::Asset>>,
    key: K,
}

impl<K: AssetKey> AssetLoadingState<K> {
    /// Create a loading state (asset not yet available).
    pub fn loading(key: K) -> Self {
        Self { value: None, key }
    }

    /// Create a ready state with the asset value.
    pub fn ready(key: K, value: Arc<K::Asset>) -> Self {
        Self {
            value: Some(value),
            key,
        }
    }

    /// Check if the resource is still loading.
    pub fn is_loading(&self) -> bool {
        self.value.is_none()
    }

    /// Check if the resource is ready.
    pub fn is_ready(&self) -> bool {
        self.value.is_some()
    }

    /// Get the value if ready, None if loading.
    pub fn get(&self) -> Option<&Arc<K::Asset>> {
        self.value.as_ref()
    }

    /// Get the value if ready, None if loading (consuming version).
    pub fn into_inner(self) -> Option<Arc<K::Asset>> {
        self.value
    }

    /// Convert to Result - Loading becomes Err(QueryError::Suspend).
    ///
    /// This method is used internally by [`Db::asset()`](crate::Db::asset).
    /// You can also use it when working with [`Db::asset_state()`](crate::Db::asset_state).
    ///
    /// # Example
    ///
    /// ```
    /// use query_flow::{asset_key, query, Db, DurabilityLevel, QueryError, QueryRuntime};
    ///
    /// #[asset_key(asset = String)]
    /// struct FilePath(String);
    ///
    /// #[query]
    /// fn byte_len(db: &impl Db, path: FilePath) -> Result<usize, QueryError> {
    ///     // Preferred: use db.asset() directly
    ///     let data = db.asset(path.clone())?;
    ///
    ///     // Alternative: use asset_state() + suspend()
    ///     let state = db.asset_state(path)?;
    ///     let data2 = state.suspend()?;
    ///
    ///     assert_eq!(data, data2);
    ///     Ok(data.len())
    /// }
    ///
    /// let runtime = QueryRuntime::new();
    /// runtime.resolve_asset(
    ///     FilePath("a".into()),
    ///     "hello".into(),
    ///     DurabilityLevel::Volatile,
    /// );
    /// assert_eq!(*runtime.query(ByteLen::new(FilePath("a".into()))).unwrap(), 5);
    /// ```
    pub fn suspend(self) -> Result<Arc<K::Asset>, QueryError> {
        match self.value {
            None => Err(QueryError::Suspend {
                asset: PendingAsset::new(self.key),
            }),
            Some(v) => Ok(v),
        }
    }

    /// Get a reference to the key.
    pub fn key(&self) -> &K {
        &self.key
    }
}

impl<K: AssetKey> std::fmt::Debug for AssetLoadingState<K>
where
    K::Asset: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.value {
            None => write!(f, "AssetLoadingState::Loading({:?})", self.key),
            Some(v) => write!(f, "AssetLoadingState::Ready({:?}, {:?})", self.key, v),
        }
    }
}
