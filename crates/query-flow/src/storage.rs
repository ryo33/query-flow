//! Type-erased cache storage for query results and assets.

use std::any::{Any, TypeId};
use std::sync::Arc;

use papaya::HashMap;

use crate::asset::{AssetKey, AssetLocator, FullAssetKey};
use crate::key::FullCacheKey;
use crate::query::Query;

/// Thread-safe, type-erased storage for cached query results.
///
/// Uses papaya's lock-free HashMap internally.
pub(crate) struct CacheStorage {
    /// Map from FullCacheKey to type-erased Arc<Output>
    entries: HashMap<FullCacheKey, Arc<dyn Any + Send + Sync>, ahash::RandomState>,
}

impl Default for CacheStorage {
    fn default() -> Self {
        Self::new()
    }
}

impl CacheStorage {
    /// Create a new empty cache storage.
    pub fn new() -> Self {
        Self {
            entries: HashMap::with_hasher(ahash::RandomState::new()),
        }
    }

    /// Get a cached value if present.
    ///
    /// Returns `None` if not cached or if type doesn't match.
    pub fn get<Q: Query>(&self, key: &FullCacheKey) -> Option<Arc<Q::Output>> {
        let pinned = self.entries.pin();
        pinned.get(key).and_then(|arc| {
            // Downcast from Any to the concrete type
            arc.clone().downcast::<Q::Output>().ok()
        })
    }

    /// Insert a value into the cache.
    pub fn insert<Q: Query>(&self, key: FullCacheKey, value: Arc<Q::Output>) {
        let pinned = self.entries.pin();
        pinned.insert(key, value as Arc<dyn Any + Send + Sync>);
    }

    /// Remove a value from the cache.
    pub fn remove(&self, key: &FullCacheKey) -> bool {
        let pinned = self.entries.pin();
        pinned.remove(key).is_some()
    }

    /// Clear all cached values.
    pub fn clear(&self) {
        let pinned = self.entries.pin();
        pinned.clear();
    }
}

/// Internal state of an asset in the cache.
#[derive(Clone)]
pub(crate) enum AssetState {
    /// Asset is being loaded.
    Loading,
    /// Asset is ready with the given value (type-erased).
    Ready(Arc<dyn Any + Send + Sync>),
    /// Asset could not be found.
    NotFound,
}

/// Thread-safe storage for cached asset values.
pub(crate) struct AssetStorage {
    /// Map from FullAssetKey to asset state
    entries: HashMap<FullAssetKey, AssetState, ahash::RandomState>,
}

impl Default for AssetStorage {
    fn default() -> Self {
        Self::new()
    }
}

impl AssetStorage {
    /// Create a new empty asset storage.
    pub fn new() -> Self {
        Self {
            entries: HashMap::with_hasher(ahash::RandomState::new()),
        }
    }

    /// Get a cached asset state if present.
    pub fn get(&self, key: &FullAssetKey) -> Option<AssetState> {
        let pinned = self.entries.pin();
        pinned.get(key).cloned()
    }

    /// Get a cached asset value if ready.
    pub fn get_ready<K: AssetKey>(&self, key: &FullAssetKey) -> Option<Arc<K::Asset>> {
        let pinned = self.entries.pin();
        pinned.get(key).and_then(|state| match state {
            AssetState::Ready(arc) => arc.clone().downcast::<K::Asset>().ok(),
            _ => None,
        })
    }

    /// Insert an asset state.
    pub fn insert(&self, key: FullAssetKey, state: AssetState) {
        let pinned = self.entries.pin();
        pinned.insert(key, state);
    }

    /// Insert a ready asset value.
    pub fn insert_ready<K: AssetKey>(&self, key: FullAssetKey, value: Arc<K::Asset>) {
        let pinned = self.entries.pin();
        pinned.insert(key, AssetState::Ready(value as Arc<dyn Any + Send + Sync>));
    }

    /// Remove an asset from the cache.
    pub fn remove(&self, key: &FullAssetKey) -> bool {
        let pinned = self.entries.pin();
        pinned.remove(key).is_some()
    }

    /// Clear all cached assets.
    #[allow(dead_code)]
    pub fn clear(&self) {
        let pinned = self.entries.pin();
        pinned.clear();
    }
}

/// Type-erased wrapper for asset locators.
pub(crate) trait AnyAssetLocator: Send + Sync + 'static {
    /// Locate an asset and return the state.
    ///
    /// This is type-erased - the concrete type handles the conversion.
    fn locate_any(&self, key: &dyn Any) -> Option<AssetState>;
}

/// Wrapper to make AssetLocator into AnyAssetLocator.
pub(crate) struct LocatorWrapper<K: AssetKey, L: AssetLocator<K>> {
    locator: L,
    _marker: std::marker::PhantomData<fn(K)>,
}

impl<K: AssetKey, L: AssetLocator<K>> LocatorWrapper<K, L> {
    pub fn new(locator: L) -> Self {
        Self {
            locator,
            _marker: std::marker::PhantomData,
        }
    }
}

impl<K: AssetKey, L: AssetLocator<K>> AnyAssetLocator for LocatorWrapper<K, L> {
    fn locate_any(&self, key: &dyn Any) -> Option<AssetState> {
        let key = key.downcast_ref::<K>()?;
        Some(match self.locator.locate(key) {
            crate::asset::LocateResult::Ready(value) => {
                AssetState::Ready(Arc::new(value) as Arc<dyn Any + Send + Sync>)
            }
            crate::asset::LocateResult::Pending => AssetState::Loading,
            crate::asset::LocateResult::NotFound => AssetState::NotFound,
        })
    }
}

/// Thread-safe storage for asset locators.
pub(crate) struct LocatorStorage {
    /// Map from AssetKey TypeId to type-erased locator
    locators: HashMap<TypeId, Arc<dyn AnyAssetLocator>, ahash::RandomState>,
}

impl Default for LocatorStorage {
    fn default() -> Self {
        Self::new()
    }
}

impl LocatorStorage {
    /// Create a new empty locator storage.
    pub fn new() -> Self {
        Self {
            locators: HashMap::with_hasher(ahash::RandomState::new()),
        }
    }

    /// Register a locator for a specific asset key type.
    pub fn insert<K: AssetKey, L: AssetLocator<K>>(&self, locator: L) {
        let pinned = self.locators.pin();
        pinned.insert(
            TypeId::of::<K>(),
            Arc::new(LocatorWrapper::<K, L>::new(locator)) as Arc<dyn AnyAssetLocator>,
        );
    }

    /// Get a locator for a specific asset key type.
    pub fn get(&self, key_type: TypeId) -> Option<Arc<dyn AnyAssetLocator>> {
        let pinned = self.locators.pin();
        pinned.get(&key_type).cloned()
    }
}

/// Thread-safe storage for pending asset requests.
pub(crate) struct PendingStorage {
    /// Map from FullAssetKey to type-erased key
    pending: HashMap<FullAssetKey, Arc<dyn Any + Send + Sync>, ahash::RandomState>,
}

impl Default for PendingStorage {
    fn default() -> Self {
        Self::new()
    }
}

impl PendingStorage {
    /// Create a new empty pending storage.
    pub fn new() -> Self {
        Self {
            pending: HashMap::with_hasher(ahash::RandomState::new()),
        }
    }

    /// Add a pending asset request.
    pub fn insert<K: AssetKey>(&self, full_key: FullAssetKey, key: K) {
        let pinned = self.pending.pin();
        pinned.insert(full_key, Arc::new(key) as Arc<dyn Any + Send + Sync>);
    }

    /// Remove a pending asset request.
    pub fn remove(&self, key: &FullAssetKey) -> bool {
        let pinned = self.pending.pin();
        pinned.remove(key).is_some()
    }

    /// Check if there are any pending assets.
    pub fn is_empty(&self) -> bool {
        let pinned = self.pending.pin();
        pinned.is_empty()
    }

    /// Get all pending assets of a specific type.
    pub fn get_of_type<K: AssetKey>(&self) -> Vec<K> {
        let pinned = self.pending.pin();
        let key_type = TypeId::of::<K>();
        pinned
            .iter()
            .filter(|(k, _)| k.key_type() == key_type)
            .filter_map(|(_, v)| v.downcast_ref::<K>().cloned())
            .collect()
    }

    /// Get all pending assets as PendingAsset.
    pub fn get_all(&self) -> Vec<crate::asset::PendingAsset> {
        let pinned = self.pending.pin();
        pinned
            .iter()
            .map(|(k, v)| crate::asset::PendingAsset::new_from_parts(k.key_type(), k.debug_repr(), v.clone()))
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cache_storage_basic() {
        struct TestQuery;
        impl Query for TestQuery {
            type CacheKey = u32;
            type Output = String;

            fn cache_key(&self) -> Self::CacheKey {
                42
            }

            fn query(
                &self,
                _ctx: &mut crate::runtime::QueryContext,
            ) -> Result<Self::Output, crate::QueryError> {
                Ok("hello".to_string())
            }

            fn output_eq(old: &Self::Output, new: &Self::Output) -> bool {
                old == new
            }
        }

        let storage = CacheStorage::new();
        let key = FullCacheKey::new::<TestQuery, _>(&42u32);

        // Initially empty
        assert!(storage.get::<TestQuery>(&key).is_none());

        // Insert and retrieve
        storage.insert::<TestQuery>(key.clone(), Arc::new("hello".to_string()));
        let result = storage.get::<TestQuery>(&key);
        assert!(result.is_some());
        assert_eq!(*result.unwrap(), "hello");

        // Remove
        assert!(storage.remove(&key));
        assert!(storage.get::<TestQuery>(&key).is_none());
    }
}
