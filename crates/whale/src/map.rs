//! A sharded, lock-based concurrent hash map.
//!
//! This is the storage primitive used by whale's [`Runtime`](crate::Runtime).
//! It is deliberately simple: a fixed number of shards, each a
//! `std::sync::RwLock<HashMap>`, with the shard chosen from the key's hash.
//! There is no unsafe code and no dependency beyond `std` and `ahash`.
//!
//! See [`ShardedMap`] for the locking rules.

use std::borrow::Borrow;
use std::collections::HashMap;
use std::hash::Hash;
use std::sync::{PoisonError, RwLock, RwLockReadGuard, RwLockWriteGuard};

type Shard<K, V> = RwLock<HashMap<K, V, ahash::RandomState>>;

/// Default shard count: four per available core, computed once.
///
/// `available_parallelism` inspects cgroup limits on Linux and costs several
/// syscalls, so it must not run on every map construction.
fn default_shard_count() -> usize {
    static COUNT: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *COUNT.get_or_init(|| {
        std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(1)
            * 4
    })
}

/// A sharded hash map guarded by per-shard read/write locks.
///
/// # Locking rules
///
/// - Locks are held only for the duration of a single method call; no guard
///   escapes the map's API. Values are returned by clone, so `V` is expected
///   to be cheap to clone (typically an `Arc`).
/// - [`ShardedMap::with`], [`ShardedMap::for_each`], [`ShardedMap::compute`]
///   and [`ShardedMap::get_or_insert_with`] run their closure while holding a
///   shard lock. The closure must not call back into the same map.
pub struct ShardedMap<K, V> {
    shards: Box<[Shard<K, V>]>,
    hasher: ahash::RandomState,
    /// `log2(shards.len())`, used to pick the shard from the hash.
    shard_bits: u32,
}

impl<K, V> Default for ShardedMap<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> ShardedMap<K, V> {
    /// Create a map with a shard count derived from the available parallelism.
    pub fn new() -> Self {
        Self::with_shards(default_shard_count())
    }

    /// Create a map with at least `shards` shards (rounded up to a power of two,
    /// clamped to `[1, 1024]`).
    pub fn with_shards(shards: usize) -> Self {
        let count = shards.clamp(1, 1024).next_power_of_two();
        let hasher = ahash::RandomState::new();
        let shards = (0..count)
            .map(|_| RwLock::new(HashMap::with_hasher(hasher.clone())))
            .collect();
        Self {
            shards,
            hasher,
            shard_bits: count.trailing_zeros(),
        }
    }

    /// Number of shards.
    pub fn shard_count(&self) -> usize {
        self.shards.len()
    }

    fn shard_for<Q>(&self, key: &Q) -> &Shard<K, V>
    where
        K: Borrow<Q>,
        Q: Hash + ?Sized,
    {
        if self.shard_bits == 0 {
            return &self.shards[0];
        }
        let hash = self.hasher.hash_one(key);
        // The inner tables use the low bits of the same hash for bucket
        // selection and the top 7 bits as a tag, so take shard bits from
        // just below the tag to keep both well distributed within a shard.
        let idx = (hash >> (57 - self.shard_bits)) as usize & (self.shards.len() - 1);
        &self.shards[idx]
    }

    fn read(shard: &Shard<K, V>) -> RwLockReadGuard<'_, HashMap<K, V, ahash::RandomState>> {
        shard.read().unwrap_or_else(PoisonError::into_inner)
    }

    fn write(shard: &Shard<K, V>) -> RwLockWriteGuard<'_, HashMap<K, V, ahash::RandomState>> {
        shard.write().unwrap_or_else(PoisonError::into_inner)
    }

    /// Total number of entries. Takes each shard's read lock in turn, so the
    /// result is only a snapshot under concurrent modification.
    pub fn len(&self) -> usize {
        self.shards.iter().map(|s| Self::read(s).len()).sum()
    }

    /// Returns `true` if no shard has any entry.
    pub fn is_empty(&self) -> bool {
        self.shards.iter().all(|s| Self::read(s).is_empty())
    }

    /// Remove all entries.
    pub fn clear(&self) {
        for shard in self.shards.iter() {
            Self::write(shard).clear();
        }
    }
}

impl<K, V> ShardedMap<K, V>
where
    K: Hash + Eq,
{
    /// Returns `true` if the map contains `key`.
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        Self::read(self.shard_for(key)).contains_key(key)
    }

    /// Get a clone of the value for `key`.
    pub fn get<Q>(&self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
        V: Clone,
    {
        Self::read(self.shard_for(key)).get(key).cloned()
    }

    /// Run `f` on the value for `key` without cloning it, under the shard's read lock.
    ///
    /// `f` must not call back into this map.
    pub fn with<Q, R>(&self, key: &Q, f: impl FnOnce(&V) -> R) -> Option<R>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        Self::read(self.shard_for(key)).get(key).map(f)
    }

    /// Insert a value, returning the previous value if any.
    pub fn insert(&self, key: K, value: V) -> Option<V> {
        Self::write(self.shard_for(&key)).insert(key, value)
    }

    /// Remove the value for `key`, returning it if it was present.
    pub fn remove<Q>(&self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        Self::write(self.shard_for(key)).remove(key)
    }

    /// Get the value for `key`, inserting the value produced by `init` if absent.
    ///
    /// `init` runs at most once, under the shard's write lock, and only when the
    /// key is absent. Returns the value and whether it was newly inserted.
    pub fn get_or_insert_with(&self, key: K, init: impl FnOnce() -> V) -> (V, bool)
    where
        V: Clone,
    {
        let shard = self.shard_for(&key);
        if let Some(value) = Self::read(shard).get(&key) {
            return (value.clone(), false);
        }
        let mut guard = Self::write(shard);
        match guard.entry(key) {
            std::collections::hash_map::Entry::Occupied(e) => (e.get().clone(), false),
            std::collections::hash_map::Entry::Vacant(e) => (e.insert(init()).clone(), true),
        }
    }

    /// Atomically read-modify-write the entry for `key`.
    ///
    /// `f` receives the current entry (`None` if absent) and may replace it,
    /// clear it, or leave it as is. It runs exactly once, under the shard's
    /// write lock, so it must not call back into this map.
    pub fn compute<R>(&self, key: K, f: impl FnOnce(&mut Option<V>) -> R) -> R {
        let shard = self.shard_for(&key);
        let mut guard = Self::write(shard);
        let (key, mut slot) = match guard.remove_entry(&key) {
            Some((key, value)) => (key, Some(value)),
            None => (key, None),
        };
        let result = f(&mut slot);
        if let Some(value) = slot {
            guard.insert(key, value);
        }
        result
    }

    /// Snapshot of all keys.
    pub fn keys(&self) -> Vec<K>
    where
        K: Clone,
    {
        self.shards
            .iter()
            .flat_map(|s| Self::read(s).keys().cloned().collect::<Vec<_>>())
            .collect()
    }

    /// Snapshot of all values.
    pub fn values(&self) -> Vec<V>
    where
        V: Clone,
    {
        self.shards
            .iter()
            .flat_map(|s| Self::read(s).values().cloned().collect::<Vec<_>>())
            .collect()
    }

    /// Snapshot of all entries.
    pub fn entries(&self) -> Vec<(K, V)>
    where
        K: Clone,
        V: Clone,
    {
        self.shards
            .iter()
            .flat_map(|s| {
                Self::read(s)
                    .iter()
                    .map(|(k, v)| (k.clone(), v.clone()))
                    .collect::<Vec<_>>()
            })
            .collect()
    }

    /// Visit every entry under the owning shard's read lock.
    ///
    /// `f` must not call back into this map.
    pub fn for_each(&self, mut f: impl FnMut(&K, &V)) {
        for shard in self.shards.iter() {
            for (k, v) in Self::read(shard).iter() {
                f(k, v);
            }
        }
    }
}

impl<K, V> std::fmt::Debug for ShardedMap<K, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ShardedMap")
            .field("shards", &self.shards.len())
            .field("len", &self.len())
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    #[test]
    fn basic_operations() {
        let map: ShardedMap<u32, Arc<str>> = ShardedMap::with_shards(4);
        assert_eq!(map.shard_count(), 4);
        assert!(map.is_empty());

        assert!(map.insert(1, "a".into()).is_none());
        assert_eq!(map.insert(1, "b".into()).as_deref(), Some("a"));
        assert_eq!(map.get(&1).as_deref(), Some("b"));
        assert!(map.contains_key(&1));
        assert_eq!(map.len(), 1);

        assert_eq!(map.remove(&1).as_deref(), Some("b"));
        assert!(map.get(&1).is_none());
        assert!(map.is_empty());
    }

    #[test]
    fn single_shard() {
        let map: ShardedMap<u64, u64> = ShardedMap::with_shards(0);
        assert_eq!(map.shard_count(), 1);
        for i in 0..100 {
            map.insert(i, i * 2);
        }
        assert_eq!(map.len(), 100);
        assert_eq!(map.get(&42), Some(84));
    }

    #[test]
    fn get_or_insert_with_runs_init_once() {
        let map: ShardedMap<&str, Arc<u32>> = ShardedMap::new();
        let mut calls = 0;
        let (v, inserted) = map.get_or_insert_with("k", || {
            calls += 1;
            Arc::new(1)
        });
        assert!(inserted);
        assert_eq!(*v, 1);
        let (v, inserted) = map.get_or_insert_with("k", || {
            calls += 1;
            Arc::new(2)
        });
        assert!(!inserted);
        assert_eq!(*v, 1);
        assert_eq!(calls, 1);
    }

    #[test]
    fn compute_insert_update_remove() {
        let map: ShardedMap<&str, u32> = ShardedMap::new();

        let r = map.compute("k", |slot| {
            assert!(slot.is_none());
            *slot = Some(1);
            "inserted"
        });
        assert_eq!(r, "inserted");
        assert_eq!(map.get(&"k"), Some(1));

        map.compute("k", |slot| {
            *slot.as_mut().unwrap() += 1;
        });
        assert_eq!(map.get(&"k"), Some(2));

        map.compute("k", |slot| {
            *slot = None;
        });
        assert!(map.get(&"k").is_none());
    }

    #[test]
    fn snapshots_cover_all_shards() {
        let map: ShardedMap<u32, u32> = ShardedMap::with_shards(8);
        for i in 0..1000 {
            map.insert(i, i);
        }
        let mut keys = map.keys();
        keys.sort_unstable();
        assert_eq!(keys, (0..1000).collect::<Vec<_>>());
        assert_eq!(map.values().len(), 1000);
        assert_eq!(map.entries().len(), 1000);
        let mut count = 0;
        map.for_each(|k, v| {
            assert_eq!(k, v);
            count += 1;
        });
        assert_eq!(count, 1000);
        map.clear();
        assert!(map.is_empty());
    }

    #[test]
    fn concurrent_inserts_and_reads() {
        let map: Arc<ShardedMap<u64, u64>> = Arc::new(ShardedMap::new());
        let handles: Vec<_> = (0..8)
            .map(|t| {
                let map = map.clone();
                std::thread::spawn(move || {
                    for i in 0..1000u64 {
                        let key = t * 1000 + i;
                        map.insert(key, key);
                        assert_eq!(map.get(&key), Some(key));
                        map.compute(key, |slot| *slot.as_mut().unwrap() += 1);
                    }
                })
            })
            .collect();
        for h in handles {
            h.join().unwrap();
        }
        assert_eq!(map.len(), 8000);
        assert_eq!(map.get(&(3 * 1000 + 7)), Some(3 * 1000 + 8));
    }

    #[test]
    fn map_is_send_sync() {
        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<ShardedMap<u32, Arc<str>>>();
    }
}
