//! Key types for query caching.

use std::any::TypeId;
use std::fmt::Debug;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

/// Trait for query cache keys.
///
/// Cache keys must be hashable, comparable, cloneable, and thread-safe.
pub trait Key: Hash + Eq + Clone + Send + Sync + Debug + 'static {}

// Blanket implementation for all types that satisfy the bounds
impl<T> Key for T where T: Hash + Eq + Clone + Send + Sync + Debug + 'static {}

/// Internal full cache key that includes query type information.
///
/// This prevents collisions between different query types that might
/// have the same `CacheKey` type (e.g., both use `u32`).
#[derive(Clone)]
pub(crate) struct FullCacheKey {
    /// Type ID of the query
    query_type: TypeId,
    /// Hash of the user's cache key
    key_hash: u64,
    /// Debug representation for error messages
    debug_repr: Arc<str>,
}

impl FullCacheKey {
    /// Create a new full cache key.
    pub fn new<Q: 'static, K: Key>(key: &K) -> Self {
        let mut hasher = ahash::AHasher::default();
        key.hash(&mut hasher);
        let key_hash = hasher.finish();

        Self {
            query_type: TypeId::of::<Q>(),
            key_hash,
            debug_repr: Arc::from(format!("{}({:?})", std::any::type_name::<Q>(), key)),
        }
    }

    /// Get debug representation for error messages.
    pub fn debug_repr(&self) -> &str {
        &self.debug_repr
    }
}

impl Debug for FullCacheKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.debug_repr)
    }
}

impl Hash for FullCacheKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.query_type.hash(state);
        self.key_hash.hash(state);
    }
}

impl PartialEq for FullCacheKey {
    fn eq(&self, other: &Self) -> bool {
        self.query_type == other.query_type && self.key_hash == other.key_hash
    }
}

impl Eq for FullCacheKey {}
