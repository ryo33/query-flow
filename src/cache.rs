use std::collections::BTreeSet;

use crate::{
    dependency::Dependencies,
    id::{CacheId, CtxId, Version},
    rc::CfgRc,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CacheState<T> {
    pub lock: LockState,
    pub version: Version,
    // No reference count here because it never shared.
    pub data: T,
    pub deps: CfgRc<Dependencies>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReturnedCache<T: ?Sized> {
    pub id: CacheId,
    pub deps: CfgRc<Dependencies>,
    pub ret: CfgRc<T>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LockState {
    /// Locking the cache for checking invalidation with `StorageState`.
    CheckingInvalidation {
        waiters: Vec<CtxId>,
    },
    Initializing {
        by: CtxId,
    },
    Updating {
        by: CtxId,
        /// Dependencies that are changed
        cause: InvalidationReason,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InvalidationReason {
    MaybeChanged,
    ChangedDirectDependencies { cache_ids: BTreeSet<CacheId> },
}

// #[derive(Debug, Clone, PartialEq, Eq, Hash)]
// pub enum Cache<T> {
