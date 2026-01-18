//! Type-erased cache storage for query results and assets.

use std::any::{Any, TypeId};
use std::hash::Hasher;
use std::sync::Arc;

use papaya::HashMap;

use crate::asset::{AssetKey, AssetLocator, DurabilityLevel};
use crate::key::{AssetCacheKey, FullCacheKey};
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

/// Type-erased cache entry stored in whale's Node.data.
///
/// This is stored directly in the whale runtime's nodes for atomic
/// update of both cached value and dependency tracking state.
#[derive(Clone)]
pub enum CachedEntry {
    /// Successful query output (type-erased).
    Ok(Arc<dyn Any + Send + Sync>),
    /// User error from query.
    UserError(Arc<anyhow::Error>),
    /// Asset is ready with value (type-erased).
    AssetReady(Arc<dyn Any + Send + Sync>),
    /// Asset error (from locator or resolve_asset_error).
    ///
    /// Unlike query errors which use `UserError`, asset errors are stored
    /// separately to maintain distinct retrieval paths for queries and assets.
    AssetError(Arc<anyhow::Error>),
}

impl CachedEntry {
    /// Convert to typed [`CachedValue`] by downcasting.
    ///
    /// This is intended for query results only. Returns `None` for asset variants
    /// (`AssetReady`, `AssetError`) because queries and assets have distinct
    /// retrieval paths and type semantics:
    /// - Queries use `CachedValue<Arc<T>>` with `Ok`/`UserError` variants
    /// - Assets use dedicated methods like `to_asset_value()` or `to_asset_error()`
    pub fn to_cached_value<T: Send + Sync + 'static>(&self) -> Option<CachedValue<Arc<T>>> {
        match self {
            CachedEntry::Ok(arc) => arc.clone().downcast::<T>().ok().map(CachedValue::Ok),
            CachedEntry::UserError(e) => Some(CachedValue::UserError(e.clone())),
            CachedEntry::AssetReady(_) | CachedEntry::AssetError(_) => None,
        }
    }
}

/// Result of locating an asset (type-erased).
pub(crate) enum ErasedLocateResult {
    /// Asset is immediately available.
    Ready {
        value: Arc<dyn Any + Send + Sync>,
        durability: DurabilityLevel,
    },
    /// Asset needs to be loaded asynchronously.
    Pending,
}

/// Type-erased asset locator.
///
/// This wraps an `AssetLocator<K>` implementation and provides type-erased
/// access via monomorphized function pointers captured at registration time.
///
/// Three function pointers are stored:
/// - `locate_with_ctx_fn`: For calls from within a query (with dependency tracking on query)
/// - `locate_with_runtime_fn`: For direct calls from QueryRuntime (no tracking)
/// - `locate_with_locator_ctx_fn`: For locator-specific dependency tracking (deps on asset)
pub(crate) struct ErasedLocator<T: crate::Tracer> {
    /// The actual locator, type-erased.
    inner: Box<dyn Any + Send + Sync>,
    /// Locate function for LocatorContext calls (deps tracked on asset, not query).
    locate_with_locator_ctx_fn: DynAssetLocatorWithLocatorContext<T>,
}

type DynAssetLocatorWithLocatorContext<T> =
    fn(
        &dyn Any,
        &crate::runtime::LocatorContext<'_, T>,
        &dyn Any,
    ) -> Option<Result<ErasedLocateResult, crate::QueryError>>;

impl<T: crate::Tracer> ErasedLocator<T> {
    /// Create a new erased locator from a concrete implementation.
    pub fn new<K: AssetKey, L: AssetLocator<K>>(locator: L) -> Self {
        Self {
            inner: Box::new(locator),
            locate_with_locator_ctx_fn: erased_locate_with_locator_ctx::<K, L, T>,
        }
    }

    /// Attempt to locate an asset using LocatorContext (deps tracked on asset, not query).
    ///
    /// Returns `None` if the key type doesn't match.
    pub fn locate_with_locator_ctx(
        &self,
        locator_ctx: &crate::runtime::LocatorContext<'_, T>,
        key: &dyn Any,
    ) -> Option<Result<ErasedLocateResult, crate::QueryError>> {
        (self.locate_with_locator_ctx_fn)(&*self.inner, locator_ctx, key)
    }
}

/// Monomorphized locate function for LocatorContext calls.
/// Dependencies are tracked on the asset itself, not the calling query.
fn erased_locate_with_locator_ctx<K: AssetKey, L: AssetLocator<K>, T: crate::Tracer>(
    locator: &dyn Any,
    locator_ctx: &crate::runtime::LocatorContext<'_, T>,
    key: &dyn Any,
) -> Option<Result<ErasedLocateResult, crate::QueryError>> {
    let locator = locator.downcast_ref::<L>()?;
    let key = key.downcast_ref::<K>()?;
    Some(locator.locate(locator_ctx, key).map(|result| match result {
        crate::asset::LocateResult::Ready { value, durability } => ErasedLocateResult::Ready {
            value: Arc::new(value) as Arc<dyn Any + Send + Sync>,
            durability,
        },
        crate::asset::LocateResult::Pending => ErasedLocateResult::Pending,
    }))
}

/// Thread-safe storage for asset locators.
pub(crate) struct LocatorStorage<T: crate::Tracer> {
    /// Map from AssetKey TypeId to type-erased locator
    locators: HashMap<TypeId, ErasedLocator<T>, ahash::RandomState>,
}

impl<T: crate::Tracer> Default for LocatorStorage<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: crate::Tracer> LocatorStorage<T> {
    /// Create a new empty locator storage.
    pub fn new() -> Self {
        Self {
            locators: HashMap::with_hasher(ahash::RandomState::new()),
        }
    }

    /// Register a locator for a specific asset key type.
    pub fn insert<K: AssetKey, L: AssetLocator<K>>(&self, locator: L) {
        let pinned = self.locators.pin();
        pinned.insert(TypeId::of::<K>(), ErasedLocator::new::<K, L>(locator));
    }

    /// Attempt to locate an asset using the registered locator (with LocatorContext).
    ///
    /// This variant tracks dependencies on the asset itself, not the calling query.
    /// Returns `None` if no locator is registered for the key type or if the key
    /// type doesn't match.
    pub fn locate_with_locator_ctx(
        &self,
        key_type: TypeId,
        locator_ctx: &crate::runtime::LocatorContext<'_, T>,
        key: &dyn Any,
    ) -> Option<Result<ErasedLocateResult, crate::QueryError>> {
        let pinned = self.locators.pin();
        pinned
            .get(&key_type)
            .and_then(|locator| locator.locate_with_locator_ctx(locator_ctx, key))
    }
}

/// Thread-safe storage for pending asset requests.
pub(crate) struct PendingStorage {
    /// Map from AssetCacheKey to type-erased key
    pending: HashMap<AssetCacheKey, Arc<dyn Any + Send + Sync>, ahash::RandomState>,
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
    pub fn insert<K: AssetKey>(&self, asset_key: AssetCacheKey, key: K) {
        let pinned = self.pending.pin();
        pinned.insert(asset_key, Arc::new(key) as Arc<dyn Any + Send + Sync>);
    }

    /// Remove a pending asset request.
    pub fn remove(&self, key: &AssetCacheKey) -> bool {
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
            .filter(|(k, _)| k.asset_key_type() == key_type)
            .filter_map(|(_, v)| v.downcast_ref::<K>().cloned())
            .collect()
    }

    /// Get all pending assets as PendingAsset.
    pub fn get_all(&self) -> Vec<crate::asset::PendingAsset> {
        let pinned = self.pending.pin();
        pinned
            .iter()
            .map(|(k, v)| {
                crate::asset::PendingAsset::new_from_parts(
                    k.asset_key_type(),
                    &k.debug_repr(),
                    v.clone(),
                )
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
        // Hash the query itself since it's now the cache key
        let mut hasher = ahash::AHasher::default();
        query.dyn_hash(&mut hasher);
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

    /// Remove a query from the registry. Returns `true` if it was present.
    pub fn remove<Q: Query>(&self, query: &Q) -> bool {
        let type_id = TypeId::of::<Q>();
        let mut hasher = ahash::AHasher::default();
        query.dyn_hash(&mut hasher);
        let key_hash = hasher.finish();

        let entries_pinned = self.entries.pin();

        if let Some(type_registry) = entries_pinned.get(&type_id) {
            let queries_pinned = type_registry.queries.pin();
            queries_pinned.remove(&key_hash).is_some()
        } else {
            false
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
        key.dyn_hash(&mut hasher);
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
        key.dyn_hash(&mut hasher);
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

/// Trait for type-erased query verification.
///
/// Allows re-executing a query to verify it hasn't changed.
pub(crate) trait AnyVerifier: Send + Sync + 'static {
    /// Verify the query by re-executing it.
    /// The runtime is passed as `&dyn Any` and will be downcast to the correct type.
    fn verify(&self, runtime: &dyn std::any::Any) -> Result<(), crate::QueryError>;
}

/// Concrete verifier for a specific query type.
pub(crate) struct QueryVerifier<Q: Query, T: crate::Tracer> {
    query: Q,
    _marker: std::marker::PhantomData<T>,
}

impl<Q: Query, T: crate::Tracer> QueryVerifier<Q, T> {
    pub fn new(query: Q) -> Self {
        Self {
            query,
            _marker: std::marker::PhantomData,
        }
    }
}

impl<Q: Query, T: crate::Tracer + 'static> AnyVerifier for QueryVerifier<Q, T> {
    fn verify(&self, runtime: &dyn std::any::Any) -> Result<(), crate::QueryError> {
        // Downcast to the correct runtime type
        if let Some(runtime) = runtime.downcast_ref::<crate::QueryRuntime<T>>() {
            match runtime.query(self.query.clone()) {
                Ok(_) => Ok(()),
                // UserError is a valid cached result, verification succeeded
                Err(crate::QueryError::UserError(_)) => Ok(()),
                // System errors mean verification failed
                Err(e) => Err(e),
            }
        } else {
            // This should never happen if used correctly
            Ok(())
        }
    }
}

/// Concrete verifier for a specific asset type.
///
/// Re-accesses the asset to trigger locator re-execution if the asset's
/// dependencies have changed. Uses early cutoff: if the asset value is
/// unchanged, changed_at stays the same and dependent queries won't re-run.
pub(crate) struct AssetVerifier<K: AssetKey, T: crate::Tracer> {
    key: K,
    _marker: std::marker::PhantomData<T>,
}

impl<K: AssetKey, T: crate::Tracer> AssetVerifier<K, T> {
    pub fn new(key: K) -> Self {
        Self {
            key,
            _marker: std::marker::PhantomData,
        }
    }
}

impl<K: AssetKey, T: crate::Tracer + 'static> AnyVerifier for AssetVerifier<K, T> {
    fn verify(&self, runtime: &dyn std::any::Any) -> Result<(), crate::QueryError> {
        // Downcast to the correct runtime type
        if let Some(runtime) = runtime.downcast_ref::<crate::QueryRuntime<T>>() {
            // Re-access the asset, which triggers locator if asset's deps are invalid
            match runtime.get_asset(self.key.clone()) {
                Ok(_) => Ok(()),
                // UserError is a valid cached result, verification succeeded
                Err(crate::QueryError::UserError(_)) => Ok(()),
                // System errors mean verification failed
                Err(e) => Err(e),
            }
        } else {
            // This should never happen if used correctly
            Ok(())
        }
    }
}

/// Thread-safe storage for query verifiers.
///
/// Verifiers can re-execute queries to verify they haven't changed.
/// Used by the "verify-then-decide" pattern to verify dependencies before
/// deciding whether to recompute a dependent query.
pub(crate) struct VerifierStorage {
    /// Map from FullCacheKey to verifier
    verifiers: HashMap<FullCacheKey, Arc<dyn AnyVerifier>, ahash::RandomState>,
}

impl Default for VerifierStorage {
    fn default() -> Self {
        Self::new()
    }
}

impl VerifierStorage {
    /// Create a new empty verifier storage.
    pub fn new() -> Self {
        Self {
            verifiers: HashMap::with_hasher(ahash::RandomState::new()),
        }
    }

    /// Register a verifier for a query.
    pub fn insert<Q: Query, T: crate::Tracer + 'static>(&self, key: FullCacheKey, query: Q) {
        let pinned = self.verifiers.pin();
        pinned.insert(key, Arc::new(QueryVerifier::<Q, T>::new(query)));
    }

    /// Register a verifier for an asset.
    pub fn insert_asset<K: AssetKey, T: crate::Tracer + 'static>(
        &self,
        key: FullCacheKey,
        asset_key: K,
    ) {
        let pinned = self.verifiers.pin();
        pinned.insert(key, Arc::new(AssetVerifier::<K, T>::new(asset_key)));
    }

    /// Get a verifier for a query key.
    pub fn get(&self, key: &FullCacheKey) -> Option<Arc<dyn AnyVerifier>> {
        let pinned = self.verifiers.pin();
        pinned.get(key).cloned()
    }

    /// Remove a verifier.
    pub fn remove(&self, key: &FullCacheKey) -> bool {
        let pinned = self.verifiers.pin();
        pinned.remove(key).is_some()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cached_entry_to_cached_value() {
        // Test Ok variant
        let entry = CachedEntry::Ok(Arc::new("hello".to_string()) as Arc<dyn Any + Send + Sync>);
        let result: Option<CachedValue<Arc<String>>> = entry.to_cached_value();
        assert!(result.is_some());
        match result.unwrap() {
            CachedValue::Ok(v) => assert_eq!(*v, "hello"),
            CachedValue::UserError(_) => panic!("expected Ok"),
        }

        // Test UserError variant
        let err = Arc::new(anyhow::anyhow!("test error"));
        let entry = CachedEntry::UserError(err.clone());
        let result: Option<CachedValue<Arc<String>>> = entry.to_cached_value();
        assert!(result.is_some());
        match result.unwrap() {
            CachedValue::Ok(_) => panic!("expected UserError"),
            CachedValue::UserError(e) => assert_eq!(e.to_string(), "test error"),
        }

        // Test type mismatch (Ok with wrong type)
        let entry = CachedEntry::Ok(Arc::new(42i32) as Arc<dyn Any + Send + Sync>);
        let result: Option<CachedValue<Arc<String>>> = entry.to_cached_value();
        assert!(result.is_none()); // downcast fails
    }
}
