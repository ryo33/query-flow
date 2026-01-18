//! Key types for query caching.

use std::any::{Any, TypeId};
use std::fmt::Debug;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

use dyn_hash::DynHash;

/// Object-safe equality comparison.
///
/// This trait enables comparing two trait objects for equality
/// by downcasting and comparing the concrete types.
pub trait DynEq: Any {
    /// Compare self with another value for equality.
    ///
    /// Returns `true` if `other` is the same concrete type and equal to `self`.
    fn dyn_eq(&self, other: &dyn Any) -> bool;
}

impl<T: Eq + 'static> DynEq for T {
    fn dyn_eq(&self, other: &dyn Any) -> bool {
        other.downcast_ref::<T>().is_some_and(|o| self == o)
    }
}

/// Trait for types that can serve as cache keys.
///
/// This trait combines object-safe hashing, equality, and debug formatting.
/// It is automatically implemented for all types that implement
/// `Hash + Eq + Debug + Send + Sync + 'static`.
///
/// # Object Safety
///
/// This trait is object-safe, allowing `Arc<dyn CacheKey>` to be used
/// in hash maps and other collections.
pub trait CacheKey: DynHash + DynEq + Debug + Send + Sync {
    /// Get the key as `Any` for downcasting.
    fn as_any(&self) -> &dyn Any;
}

impl<T: Hash + Eq + Debug + Send + Sync + 'static> CacheKey for T {
    fn as_any(&self) -> &dyn Any {
        self
    }
}

// Enable Hash for dyn CacheKey using the dyn-hash crate
dyn_hash::hash_trait_object!(CacheKey);

/// The kind of cache key, used for type discrimination.
///
/// This allows different types of keys (queries, assets, sentinels)
/// to be distinguished even if they have the same underlying value.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum KeyKind {
    /// A query key, parameterized by the query type.
    Query(TypeId),
    /// An asset key, parameterized by the asset key type.
    Asset(TypeId),
    /// Sentinel for query set tracking (used by `list_queries`).
    QuerySetSentinel(TypeId),
    /// Sentinel for asset key set tracking (used by `list_asset_keys`).
    AssetKeySetSentinel(TypeId),
}

/// Full cache key that includes type discrimination and the actual key value.
///
/// This is the key type used internally by the runtime for all cache operations.
/// It combines:
/// - `KeyKind`: Distinguishes between queries, assets, and sentinels
/// - The actual key value: Stored as `Arc<dyn CacheKey>` for type erasure
///
/// # Design
///
/// Unlike the previous design, this does not pre-compute the hash or
/// allocate a debug string. Hash is computed on-demand via `dyn-hash`,
/// and debug representation uses the key's `Debug` implementation.
pub struct FullCacheKey {
    /// The kind and type of key
    kind: KeyKind,
    /// The actual key value, type-erased
    key: Arc<dyn CacheKey>,
}

impl FullCacheKey {
    /// Create a new full cache key for a query.
    ///
    /// The key is stored and can be downcast back to the original type.
    pub fn new<Q: 'static, K: CacheKey>(key: K) -> Self {
        Self {
            kind: KeyKind::Query(TypeId::of::<Q>()),
            key: Arc::new(key),
        }
    }

    /// Create a cache key for an asset.
    pub fn for_asset<K: CacheKey + 'static>(key: K) -> Self {
        Self {
            kind: KeyKind::Asset(TypeId::of::<K>()),
            key: Arc::new(key),
        }
    }

    /// Create a sentinel key representing "all queries of type Q".
    ///
    /// This is used by `list_queries` to track dependencies on the set of queries,
    /// rather than individual query values.
    pub fn query_set_sentinel<Q: 'static>() -> Self {
        Self {
            kind: KeyKind::QuerySetSentinel(TypeId::of::<Q>()),
            key: Arc::new(()),
        }
    }

    /// Create a sentinel key representing "all asset keys of type K".
    ///
    /// This is used by `list_asset_keys` to track dependencies on the set of asset keys,
    /// rather than individual asset values.
    pub fn asset_key_set_sentinel<K: 'static>() -> Self {
        Self {
            kind: KeyKind::AssetKeySetSentinel(TypeId::of::<K>()),
            key: Arc::new(()),
        }
    }

    /// Get the debug representation of this key.
    ///
    /// This is computed lazily from the key's `Debug` implementation.
    pub fn debug_repr(&self) -> String {
        format!("{:?}", self.key)
    }

    /// Get the kind of this key.
    pub fn kind(&self) -> KeyKind {
        self.kind
    }

    /// Downcast the key to its original type.
    ///
    /// Returns `None` if the key is not of type `K`.
    pub fn downcast<K: 'static>(&self) -> Option<&K> {
        self.key.as_any().downcast_ref()
    }

    /// Get a reference to the type-erased key.
    pub fn key(&self) -> &Arc<dyn CacheKey> {
        &self.key
    }
}

impl Clone for FullCacheKey {
    fn clone(&self) -> Self {
        Self {
            kind: self.kind,
            key: Arc::clone(&self.key),
        }
    }
}

impl Debug for FullCacheKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.kind {
            KeyKind::Query(_) => write!(f, "{:?}", self.key),
            KeyKind::Asset(_) => write!(f, "Asset({:?})", self.key),
            KeyKind::QuerySetSentinel(type_id) => write!(f, "QuerySet({:?})", type_id),
            KeyKind::AssetKeySetSentinel(type_id) => write!(f, "AssetKeySet({:?})", type_id),
        }
    }
}

impl Hash for FullCacheKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.kind.hash(state);
        self.key.hash(state);
    }
}

impl PartialEq for FullCacheKey {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind && self.key.dyn_eq(other.key.as_any())
    }
}

impl Eq for FullCacheKey {}
