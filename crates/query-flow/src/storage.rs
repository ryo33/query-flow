//! Type-erased cache storage for query results.

use std::any::{Any, TypeId};
use std::sync::Arc;

use papaya::HashMap;

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

/// Storage for pending background loads.
///
/// Maps cache keys to their loaded values (when complete).
pub(crate) struct LoadedStorage {
    /// Map from (TypeId, key_hash) to loaded value
    entries: HashMap<(TypeId, u64), Arc<dyn Any + Send + Sync>, ahash::RandomState>,
}

impl Default for LoadedStorage {
    fn default() -> Self {
        Self::new()
    }
}

impl LoadedStorage {
    /// Create a new empty loaded storage.
    pub fn new() -> Self {
        Self {
            entries: HashMap::with_hasher(ahash::RandomState::new()),
        }
    }

    /// Get a loaded value if present.
    pub fn get<T: Send + Sync + 'static>(&self, type_id: TypeId, key_hash: u64) -> Option<Arc<T>> {
        let pinned = self.entries.pin();
        pinned
            .get(&(type_id, key_hash))
            .and_then(|arc| arc.clone().downcast::<T>().ok())
    }

    /// Insert a loaded value.
    pub fn insert<T: Send + Sync + 'static>(&self, type_id: TypeId, key_hash: u64, value: Arc<T>) {
        let pinned = self.entries.pin();
        pinned.insert((type_id, key_hash), value as Arc<dyn Any + Send + Sync>);
    }

    /// Remove a loaded value.
    #[allow(dead_code)] // Reserved for future use (cache eviction)
    pub fn remove(&self, type_id: TypeId, key_hash: u64) -> bool {
        let pinned = self.entries.pin();
        pinned.remove(&(type_id, key_hash)).is_some()
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
