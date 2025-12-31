//! Loading state for async resource handling.

use std::sync::Arc;

use crate::asset::{AssetKey, PendingAsset};
use crate::QueryError;

/// Loading state with asset key information for error reporting.
///
/// This is returned by `ctx.asset()` and provides information about
/// whether an asset is loading or ready, along with the key for
/// error reporting on suspend.
///
/// # Example
///
/// ```ignore
/// #[query]
/// fn process_file(ctx: &mut QueryContext, path: FilePath) -> Result<Output, QueryError> {
///     let content = ctx.asset(path)?.suspend()?;
///     // Process content...
///     Ok(output)
/// }
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
    /// Use this with the `?` operator to propagate loading state upward.
    /// The returned error includes the asset key for debugging.
    ///
    /// # Example
    ///
    /// ```ignore
    /// fn query(&self, ctx: &mut QueryContext) -> Result<MyOutput, QueryError> {
    ///     let data = ctx.asset(key)?.suspend()?;
    ///     // `data` is guaranteed to be ready here
    ///     Ok(process(data))
    /// }
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
