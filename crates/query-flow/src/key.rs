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

    /// Get the type name for this key.
    fn type_name(&self) -> &'static str;
}

impl<T: Hash + Eq + Debug + Send + Sync + 'static> CacheKey for T {
    fn as_any(&self) -> &dyn Any {
        self
    }

    fn type_name(&self) -> &'static str {
        std::any::type_name::<T>()
    }
}

// Enable Hash for dyn CacheKey using the dyn-hash crate
dyn_hash::hash_trait_object!(CacheKey);

/// Cache key for a query.
///
/// Stores the query type and the query value as a type-erased `Arc<dyn CacheKey>`.
#[derive(Clone)]
pub struct QueryCacheKey {
    query_type: TypeId,
    key: Arc<dyn CacheKey>,
}

impl QueryCacheKey {
    /// Create a new query cache key.
    pub fn new<Q: CacheKey + 'static>(query: Q) -> Self {
        Self {
            query_type: TypeId::of::<Q>(),
            key: Arc::new(query),
        }
    }

    /// Get the debug representation of this key.
    pub fn debug_repr(&self) -> String {
        format!("{:?}", self.key)
    }

    /// Downcast the key to its original type.
    pub fn downcast<K: 'static>(&self) -> Option<&K> {
        self.key.as_any().downcast_ref()
    }

    /// Get the query type ID.
    pub fn query_type(&self) -> TypeId {
        self.query_type
    }

    /// Get a reference to the type-erased key.
    pub fn key(&self) -> &Arc<dyn CacheKey> {
        &self.key
    }

    /// Get the type name for this query key.
    pub fn type_name(&self) -> &'static str {
        self.key.type_name()
    }
}

impl Debug for QueryCacheKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.key)
    }
}

impl Hash for QueryCacheKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.query_type.hash(state);
        self.key.hash(state);
    }
}

impl PartialEq for QueryCacheKey {
    fn eq(&self, other: &Self) -> bool {
        self.query_type == other.query_type && self.key.dyn_eq(other.key.as_any())
    }
}

impl Eq for QueryCacheKey {}

/// Cache key for an asset.
///
/// Stores the asset key type and the key value as a type-erased `Arc<dyn CacheKey>`.
#[derive(Clone)]
pub struct AssetCacheKey {
    asset_key_type: TypeId,
    key: Arc<dyn CacheKey>,
}

impl AssetCacheKey {
    /// Create a new asset cache key.
    pub fn new<K: CacheKey + 'static>(key: K) -> Self {
        Self {
            asset_key_type: TypeId::of::<K>(),
            key: Arc::new(key),
        }
    }

    /// Get the debug representation of this key.
    pub fn debug_repr(&self) -> String {
        format!("{:?}", self.key)
    }

    /// Downcast the key to its original type.
    pub fn downcast<K: 'static>(&self) -> Option<&K> {
        self.key.as_any().downcast_ref()
    }

    /// Get the asset key type ID.
    pub fn asset_key_type(&self) -> TypeId {
        self.asset_key_type
    }

    /// Get a reference to the type-erased key.
    pub fn key(&self) -> &Arc<dyn CacheKey> {
        &self.key
    }

    /// Get the type name for this asset key.
    pub fn type_name(&self) -> &'static str {
        self.key.type_name()
    }
}

impl Debug for AssetCacheKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Asset({:?})", self.key)
    }
}

impl Hash for AssetCacheKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.asset_key_type.hash(state);
        self.key.hash(state);
    }
}

impl PartialEq for AssetCacheKey {
    fn eq(&self, other: &Self) -> bool {
        self.asset_key_type == other.asset_key_type && self.key.dyn_eq(other.key.as_any())
    }
}

impl Eq for AssetCacheKey {}

/// Sentinel for tracking all queries of a type.
///
/// Used by `list_queries` to track dependencies on the set of queries,
/// rather than individual query values.
#[derive(Clone, Copy)]
pub struct QuerySetSentinelKey {
    query_type: TypeId,
    type_name: &'static str,
}

impl QuerySetSentinelKey {
    /// Create a new query set sentinel key.
    pub fn new<Q: 'static>() -> Self {
        Self {
            query_type: TypeId::of::<Q>(),
            type_name: std::any::type_name::<Q>(),
        }
    }

    /// Get the query type ID.
    pub fn query_type(&self) -> TypeId {
        self.query_type
    }

    /// Get the type name for this query set sentinel.
    pub fn type_name(&self) -> &'static str {
        self.type_name
    }
}

impl Debug for QuerySetSentinelKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "QuerySet({:?})", self.query_type)
    }
}

impl Hash for QuerySetSentinelKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.query_type.hash(state);
    }
}

impl PartialEq for QuerySetSentinelKey {
    fn eq(&self, other: &Self) -> bool {
        self.query_type == other.query_type
    }
}

impl Eq for QuerySetSentinelKey {}

/// Sentinel for tracking all asset keys of a type.
///
/// Used by `list_asset_keys` to track dependencies on the set of asset keys,
/// rather than individual asset values.
#[derive(Clone, Copy)]
pub struct AssetKeySetSentinelKey {
    asset_key_type: TypeId,
    type_name: &'static str,
}

impl AssetKeySetSentinelKey {
    /// Create a new asset key set sentinel key.
    pub fn new<K: 'static>() -> Self {
        Self {
            asset_key_type: TypeId::of::<K>(),
            type_name: std::any::type_name::<K>(),
        }
    }

    /// Get the asset key type ID.
    pub fn asset_key_type(&self) -> TypeId {
        self.asset_key_type
    }

    /// Get the type name for this asset key set sentinel.
    pub fn type_name(&self) -> &'static str {
        self.type_name
    }
}

impl Debug for AssetKeySetSentinelKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "AssetKeySet({:?})", self.asset_key_type)
    }
}

impl Hash for AssetKeySetSentinelKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.asset_key_type.hash(state);
    }
}

impl PartialEq for AssetKeySetSentinelKey {
    fn eq(&self, other: &Self) -> bool {
        self.asset_key_type == other.asset_key_type
    }
}

impl Eq for AssetKeySetSentinelKey {}

/// Unified cache key for whale storage.
///
/// Used where all key kinds need to be handled together (whale, generic invalidation).
/// Each variant wraps a specific key type.
#[derive(Clone)]
pub enum FullCacheKey {
    /// A query key.
    Query(QueryCacheKey),
    /// An asset key.
    Asset(AssetCacheKey),
    /// Sentinel for query set tracking (used by `list_queries`).
    QuerySetSentinel(QuerySetSentinelKey),
    /// Sentinel for asset key set tracking (used by `list_asset_keys`).
    AssetKeySetSentinel(AssetKeySetSentinelKey),
}

impl FullCacheKey {
    /// Get the debug representation of this key.
    pub fn debug_repr(&self) -> String {
        match self {
            FullCacheKey::Query(k) => k.debug_repr(),
            FullCacheKey::Asset(k) => k.debug_repr(),
            FullCacheKey::QuerySetSentinel(k) => format!("{:?}", k),
            FullCacheKey::AssetKeySetSentinel(k) => format!("{:?}", k),
        }
    }

    /// Downcast the key to its original type.
    ///
    /// Returns `None` if the key is not of type `K`.
    pub fn downcast<K: 'static>(&self) -> Option<&K> {
        match self {
            FullCacheKey::Query(k) => k.downcast(),
            FullCacheKey::Asset(k) => k.downcast(),
            FullCacheKey::QuerySetSentinel(_) | FullCacheKey::AssetKeySetSentinel(_) => None,
        }
    }

    /// Get a reference to the type-erased key (for Query and Asset variants).
    pub fn key(&self) -> Option<&Arc<dyn CacheKey>> {
        match self {
            FullCacheKey::Query(k) => Some(k.key()),
            FullCacheKey::Asset(k) => Some(k.key()),
            FullCacheKey::QuerySetSentinel(_) | FullCacheKey::AssetKeySetSentinel(_) => None,
        }
    }

    /// Get the type name for this key.
    pub fn type_name(&self) -> &'static str {
        match self {
            FullCacheKey::Query(k) => k.type_name(),
            FullCacheKey::Asset(k) => k.type_name(),
            FullCacheKey::QuerySetSentinel(k) => k.type_name(),
            FullCacheKey::AssetKeySetSentinel(k) => k.type_name(),
        }
    }
}

impl Debug for FullCacheKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FullCacheKey::Query(k) => write!(f, "{:?}", k),
            FullCacheKey::Asset(k) => write!(f, "{:?}", k),
            FullCacheKey::QuerySetSentinel(k) => write!(f, "{:?}", k),
            FullCacheKey::AssetKeySetSentinel(k) => write!(f, "{:?}", k),
        }
    }
}

impl Hash for FullCacheKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        std::mem::discriminant(self).hash(state);
        match self {
            FullCacheKey::Query(k) => k.hash(state),
            FullCacheKey::Asset(k) => k.hash(state),
            FullCacheKey::QuerySetSentinel(k) => k.hash(state),
            FullCacheKey::AssetKeySetSentinel(k) => k.hash(state),
        }
    }
}

impl PartialEq for FullCacheKey {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (FullCacheKey::Query(a), FullCacheKey::Query(b)) => a == b,
            (FullCacheKey::Asset(a), FullCacheKey::Asset(b)) => a == b,
            (FullCacheKey::QuerySetSentinel(a), FullCacheKey::QuerySetSentinel(b)) => a == b,
            (FullCacheKey::AssetKeySetSentinel(a), FullCacheKey::AssetKeySetSentinel(b)) => a == b,
            _ => false,
        }
    }
}

impl Eq for FullCacheKey {}

impl From<QueryCacheKey> for FullCacheKey {
    fn from(key: QueryCacheKey) -> Self {
        FullCacheKey::Query(key)
    }
}

impl From<AssetCacheKey> for FullCacheKey {
    fn from(key: AssetCacheKey) -> Self {
        FullCacheKey::Asset(key)
    }
}

impl From<QuerySetSentinelKey> for FullCacheKey {
    fn from(key: QuerySetSentinelKey) -> Self {
        FullCacheKey::QuerySetSentinel(key)
    }
}

impl From<AssetKeySetSentinelKey> for FullCacheKey {
    fn from(key: AssetKeySetSentinelKey) -> Self {
        FullCacheKey::AssetKeySetSentinel(key)
    }
}

/// Convenience trait for types that can be used in query cache keys.
///
/// This trait combines all the bounds needed for a type to be used as a
/// field in a generic query struct: `Hash + Eq + Clone + Debug + Send + Sync + 'static`.
///
/// Use this trait bound on generic type parameters that appear in query fields.
/// For type parameters that only appear in the output, use `QueryOutput` instead.
pub trait Cachable: std::hash::Hash + Eq + Clone + std::fmt::Debug + Send + Sync + 'static {}
impl<T: std::hash::Hash + Eq + Clone + std::fmt::Debug + Send + Sync + 'static> Cachable for T {}
