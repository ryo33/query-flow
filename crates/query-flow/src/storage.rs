//! Type-erased cache storage for query results and assets.

use std::any::{Any, TypeId};
use std::hash::{Hash, Hasher};
use std::sync::Arc;

use papaya::HashMap;

use crate::asset::{AssetKey, AssetLocator, FullAssetKey};
use crate::key::FullCacheKey;
use crate::query::Query;

/// Cached query result (success or user error).
///
/// This is used internally to store both successful outputs and user errors
/// in the cache, enabling early cutoff optimization for error results.
#[derive(Clone)]
pub enum CachedValue<T> {
    /// Successful query output.
    Ok(T),
    /// User error from `QueryError::UserError`.
    UserError(Arc<anyhow::Error>),
}

/// Internal type-erased cache entry.
#[derive(Clone)]
pub(crate) enum CachedEntry {
    /// Successful output (type-erased).
    Ok(Arc<dyn Any + Send + Sync>),
    /// User error.
    UserError(Arc<anyhow::Error>),
}

/// Thread-safe, type-erased storage for cached query results.
///
/// Uses papaya's lock-free HashMap internally.
pub(crate) struct CacheStorage {
    /// Map from FullCacheKey to cached entry (Ok or UserError)
    entries: HashMap<FullCacheKey, CachedEntry, ahash::RandomState>,
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

    /// Get a cached entry (Ok or UserError) if present.
    pub fn get_cached<Q: Query>(&self, key: &FullCacheKey) -> Option<CachedValue<Arc<Q::Output>>> {
        let pinned = self.entries.pin();
        pinned.get(key).and_then(|entry| match entry {
            CachedEntry::Ok(arc) => arc
                .clone()
                .downcast::<Q::Output>()
                .ok()
                .map(CachedValue::Ok),
            CachedEntry::UserError(e) => Some(CachedValue::UserError(e.clone())),
        })
    }

    /// Insert an Ok value into the cache.
    pub fn insert_ok<Q: Query>(&self, key: FullCacheKey, value: Arc<Q::Output>) {
        let pinned = self.entries.pin();
        pinned.insert(key, CachedEntry::Ok(value as Arc<dyn Any + Send + Sync>));
    }

    /// Insert a UserError into the cache.
    pub fn insert_error(&self, key: FullCacheKey, error: Arc<anyhow::Error>) {
        let pinned = self.entries.pin();
        pinned.insert(key, CachedEntry::UserError(error));
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
            .map(|(k, v)| {
                crate::asset::PendingAsset::new_from_parts(k.key_type(), k.debug_repr(), v.clone())
            })
            .collect()
    }
}

/// Thread-safe registry for tracking query instances by type.
///
/// Used by `list_queries` to enumerate all registered queries of a specific type.
pub(crate) struct QueryRegistry {
    /// Map from Query TypeId to per-type registry
    entries: HashMap<TypeId, QueryTypeRegistry, ahash::RandomState>,
}

/// Per-type registry for queries.
struct QueryTypeRegistry {
    /// Map from key_hash to type-erased query instance
    queries: HashMap<u64, Arc<dyn Any + Send + Sync>, ahash::RandomState>,
}

impl Default for QueryRegistry {
    fn default() -> Self {
        Self::new()
    }
}

impl QueryRegistry {
    /// Create a new empty query registry.
    pub fn new() -> Self {
        Self {
            entries: HashMap::with_hasher(ahash::RandomState::new()),
        }
    }

    /// Register a query instance. Returns `true` if this was a new entry.
    pub fn register<Q: Query>(&self, query: &Q) -> bool {
        let type_id = TypeId::of::<Q>();
        let key = query.cache_key();
        let mut hasher = ahash::AHasher::default();
        key.hash(&mut hasher);
        let key_hash = hasher.finish();

        let entries_pinned = self.entries.pin();

        // Get or create the per-type registry
        if let Some(type_registry) = entries_pinned.get(&type_id) {
            let queries_pinned = type_registry.queries.pin();
            if queries_pinned.contains_key(&key_hash) {
                return false; // Already registered
            }
            queries_pinned.insert(
                key_hash,
                Arc::new(query.clone()) as Arc<dyn Any + Send + Sync>,
            );
            true
        } else {
            // Create new per-type registry
            let type_registry = QueryTypeRegistry {
                queries: HashMap::with_hasher(ahash::RandomState::new()),
            };
            type_registry.queries.pin().insert(
                key_hash,
                Arc::new(query.clone()) as Arc<dyn Any + Send + Sync>,
            );
            entries_pinned.insert(type_id, type_registry);
            true
        }
    }

    /// Get all query instances of type Q.
    pub fn get_all<Q: Query>(&self) -> Vec<Q> {
        let type_id = TypeId::of::<Q>();
        let entries_pinned = self.entries.pin();

        if let Some(type_registry) = entries_pinned.get(&type_id) {
            let queries_pinned = type_registry.queries.pin();
            queries_pinned
                .iter()
                .filter_map(|(_, arc)| arc.downcast_ref::<Q>().cloned())
                .collect()
        } else {
            Vec::new()
        }
    }
}

/// Thread-safe registry for tracking asset keys by type.
///
/// Used by `list_asset_keys` to enumerate all registered asset keys of a specific type.
pub(crate) struct AssetKeyRegistry {
    /// Map from AssetKey TypeId to per-type registry
    entries: HashMap<TypeId, AssetKeyTypeRegistry, ahash::RandomState>,
}

/// Per-type registry for asset keys.
struct AssetKeyTypeRegistry {
    /// Map from key_hash to type-erased asset key instance
    keys: HashMap<u64, Arc<dyn Any + Send + Sync>, ahash::RandomState>,
}

impl Default for AssetKeyRegistry {
    fn default() -> Self {
        Self::new()
    }
}

impl AssetKeyRegistry {
    /// Create a new empty asset key registry.
    pub fn new() -> Self {
        Self {
            entries: HashMap::with_hasher(ahash::RandomState::new()),
        }
    }

    /// Register an asset key. Returns `true` if this was a new entry.
    pub fn register<K: AssetKey>(&self, key: &K) -> bool {
        let type_id = TypeId::of::<K>();
        let mut hasher = ahash::AHasher::default();
        key.hash(&mut hasher);
        let key_hash = hasher.finish();

        let entries_pinned = self.entries.pin();

        if let Some(type_registry) = entries_pinned.get(&type_id) {
            let keys_pinned = type_registry.keys.pin();
            if keys_pinned.contains_key(&key_hash) {
                return false; // Already registered
            }
            keys_pinned.insert(
                key_hash,
                Arc::new(key.clone()) as Arc<dyn Any + Send + Sync>,
            );
            true
        } else {
            let type_registry = AssetKeyTypeRegistry {
                keys: HashMap::with_hasher(ahash::RandomState::new()),
            };
            type_registry.keys.pin().insert(
                key_hash,
                Arc::new(key.clone()) as Arc<dyn Any + Send + Sync>,
            );
            entries_pinned.insert(type_id, type_registry);
            true
        }
    }

    /// Get all asset keys of type K.
    pub fn get_all<K: AssetKey>(&self) -> Vec<K> {
        let type_id = TypeId::of::<K>();
        let entries_pinned = self.entries.pin();

        if let Some(type_registry) = entries_pinned.get(&type_id) {
            let keys_pinned = type_registry.keys.pin();
            keys_pinned
                .iter()
                .filter_map(|(_, arc)| arc.downcast_ref::<K>().cloned())
                .collect()
        } else {
            Vec::new()
        }
    }

    /// Remove an asset key. Returns `true` if it was present.
    pub fn remove<K: AssetKey>(&self, key: &K) -> bool {
        let type_id = TypeId::of::<K>();
        let mut hasher = ahash::AHasher::default();
        key.hash(&mut hasher);
        let key_hash = hasher.finish();

        let entries_pinned = self.entries.pin();

        if let Some(type_registry) = entries_pinned.get(&type_id) {
            let keys_pinned = type_registry.keys.pin();
            keys_pinned.remove(&key_hash).is_some()
        } else {
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cache_storage_basic() {
        #[derive(Clone)]
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
        assert!(storage.get_cached::<TestQuery>(&key).is_none());

        // Insert and retrieve
        storage.insert_ok::<TestQuery>(key.clone(), Arc::new("hello".to_string()));
        let result = storage.get_cached::<TestQuery>(&key);
        assert!(result.is_some());
        match result.unwrap() {
            CachedValue::Ok(v) => assert_eq!(*v, "hello"),
            CachedValue::UserError(_) => panic!("expected Ok"),
        }

        // Remove
        assert!(storage.remove(&key));
        assert!(storage.get_cached::<TestQuery>(&key).is_none());
    }
}
