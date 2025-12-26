//! Asset types for external resources.
//!
//! Assets are external inputs (files, network resources, etc.) that:
//! - Are always leaves in the dependency graph (no dependencies)
//! - May need IO to load
//! - Loading differs by platform (filesystem locally, network/memory in playground)
//! - Can be depended upon by queries with proper dependency tracking

use std::any::{Any, TypeId};
use std::fmt::Debug;
use std::sync::Arc;

use crate::key::Key;

/// Named durability levels for assets and queries.
///
/// Higher values indicate the data changes less frequently.
/// This is used for optimization in the dependency tracking layer.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
#[repr(u8)]
pub enum DurabilityLevel {
    /// Changes frequently (live feeds, real-time data).
    #[default]
    Volatile = 0,
    /// Stable within a session.
    Session = 1,
    /// Changes rarely.
    Stable = 2,
    /// Never changes (bundled assets, constants).
    Constant = 3,
}

impl DurabilityLevel {
    /// Convert to u8 for whale integration.
    pub fn as_u8(self) -> u8 {
        self as u8
    }
}

/// Trait for asset keys that map to loadable assets.
///
/// Asset keys identify external resources (files, URLs, etc.) and define
/// the type of asset they load. Assets are leaf nodes in the dependency
/// graph - they have no dependencies but can be depended upon by queries.
///
/// # Example
///
/// ```ignore
/// use query_flow::{asset_key, AssetKey, DurabilityLevel};
///
/// #[asset_key(asset = String)]
/// pub struct ConfigFile(pub PathBuf);
///
/// #[asset_key(asset = String, durability = constant)]
/// pub struct BundledFile(pub PathBuf);
///
/// // Or manually:
/// pub struct TextureId(pub u32);
///
/// impl AssetKey for TextureId {
///     type Asset = ImageData;
///
///     fn asset_eq(old: &Self::Asset, new: &Self::Asset) -> bool {
///         old.bytes == new.bytes
///     }
///
///     fn durability(&self) -> DurabilityLevel {
///         DurabilityLevel::Constant
///     }
/// }
/// ```
pub trait AssetKey: Key + 'static {
    /// The asset type this key loads.
    type Asset: Send + Sync + 'static;

    /// Compare two asset values for equality (for early cutoff).
    ///
    /// When an asset is re-resolved with the same value, dependent queries
    /// can skip recomputation (early cutoff).
    fn asset_eq(old: &Self::Asset, new: &Self::Asset) -> bool;

    /// Durability level for this asset type.
    ///
    /// Higher values indicate the asset changes less frequently.
    /// Default: `Volatile` (changes frequently).
    fn durability(&self) -> DurabilityLevel {
        DurabilityLevel::Volatile
    }
}

/// Result of locating an asset.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LocateResult<A> {
    /// Asset is immediately available (e.g., from memory cache).
    Ready(A),
    /// Asset needs to be loaded asynchronously.
    /// The runtime will track this as a pending request.
    Pending,
    /// Asset does not exist or cannot be located.
    NotFound,
}

/// Trait for locating and loading assets.
///
/// Implement this trait to define how assets are found for a given key type.
/// Different locators can be registered for different platforms:
/// - Filesystem locator for desktop
/// - Network locator for web/playground
/// - Memory locator for testing
///
/// # Example
///
/// ```ignore
/// struct FileSystemLocator {
///     base_path: PathBuf,
/// }
///
/// impl AssetLocator<FilePath> for FileSystemLocator {
///     fn locate(&self, key: &FilePath) -> LocateResult<String> {
///         // For sync IO, could read directly:
///         // let path = self.base_path.join(&key.0);
///         // match std::fs::read_to_string(&path) {
///         //     Ok(content) => LocateResult::Ready(content),
///         //     Err(_) => LocateResult::NotFound,
///         // }
///
///         // For async IO, return Pending:
///         LocateResult::Pending
///     }
/// }
/// ```
pub trait AssetLocator<K: AssetKey>: Send + Sync + 'static {
    /// Attempt to locate an asset for the given key.
    ///
    /// This method should be fast and non-blocking:
    /// - Return `Ready(value)` if the asset is immediately available
    /// - Return `Pending` if the asset needs async loading
    /// - Return `NotFound` if the asset cannot be found
    ///
    /// For assets requiring IO, typically return `Pending` and let the user
    /// fetch the asset externally, then call `runtime.resolve_asset()`.
    fn locate(&self, key: &K) -> LocateResult<K::Asset>;
}

/// A pending asset request that needs to be resolved.
pub struct PendingAsset {
    /// Type-erased key for the asset (stored as Arc for efficient cloning)
    key: Arc<dyn Any + Send + Sync>,
    /// Type ID of the AssetKey type
    key_type: TypeId,
    /// Debug representation
    debug_repr: String,
}

impl PendingAsset {
    /// Create a new pending asset.
    #[allow(dead_code)] // Reserved for direct construction if needed
    pub(crate) fn new<K: AssetKey>(key: K) -> Self {
        Self {
            debug_repr: format!("{:?}", key),
            key_type: TypeId::of::<K>(),
            key: Arc::new(key),
        }
    }

    /// Create from pre-computed parts (used by PendingStorage).
    pub(crate) fn new_from_parts(
        key_type: TypeId,
        debug_repr: &str,
        key: Arc<dyn Any + Send + Sync>,
    ) -> Self {
        Self {
            key_type,
            debug_repr: debug_repr.to_string(),
            key,
        }
    }

    /// Downcast the key to its concrete type.
    pub fn key<K: AssetKey>(&self) -> Option<&K> {
        if self.key_type == TypeId::of::<K>() {
            self.key.downcast_ref()
        } else {
            None
        }
    }

    /// Check if this pending asset is for the given key type.
    pub fn is<K: AssetKey>(&self) -> bool {
        self.key_type == TypeId::of::<K>()
    }

    /// Get the TypeId of the key type.
    pub fn key_type(&self) -> TypeId {
        self.key_type
    }

    /// Get debug representation.
    pub fn debug_repr(&self) -> &str {
        &self.debug_repr
    }
}

impl Debug for PendingAsset {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "PendingAsset({})", self.debug_repr)
    }
}

/// Full cache key for assets (includes AssetKey type information).
///
/// This is similar to `FullCacheKey` for queries but marks the entry
/// as an asset in the dependency graph.
#[derive(Clone)]
pub(crate) struct FullAssetKey {
    /// Type ID of the AssetKey type
    key_type: TypeId,
    /// Hash of the key value
    key_hash: u64,
    /// Debug representation
    debug_repr: Arc<str>,
}

impl FullAssetKey {
    /// Create a new full asset key.
    pub fn new<K: AssetKey>(key: &K) -> Self {
        use std::hash::Hasher;
        let mut hasher = ahash::AHasher::default();
        key.hash(&mut hasher);
        let key_hash = hasher.finish();

        Self {
            key_type: TypeId::of::<K>(),
            key_hash,
            debug_repr: Arc::from(format!("Asset:{}({:?})", std::any::type_name::<K>(), key)),
        }
    }

    /// Get debug representation for error messages.
    pub fn debug_repr(&self) -> &str {
        &self.debug_repr
    }

    /// Get the key type.
    pub fn key_type(&self) -> TypeId {
        self.key_type
    }

    /// Get the key hash.
    pub fn key_hash(&self) -> u64 {
        self.key_hash
    }
}

impl Debug for FullAssetKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.debug_repr)
    }
}

impl std::hash::Hash for FullAssetKey {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.key_type.hash(state);
        self.key_hash.hash(state);
    }
}

impl PartialEq for FullAssetKey {
    fn eq(&self, other: &Self) -> bool {
        self.key_type == other.key_type && self.key_hash == other.key_hash
    }
}

impl Eq for FullAssetKey {}
