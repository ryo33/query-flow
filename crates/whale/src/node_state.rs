//! Internal, concurrently mutable node storage.
//!
//! [`NodeState`] is what the runtime actually stores. The hot fields that
//! validity checks read (`verified_at`, `changed_at`, `durability`, `level`)
//! are atomics, so readers never take a lock. The structural fields (`data`,
//! `dependencies`, `dependents`) live behind a read/write lock; writers hold
//! it for the duration of one update, which also serializes writes to the
//! atomics so a locked reader sees a consistent node.
//!
//! The public, plain-data [`Node`] is produced on demand by [`NodeState::snapshot`].

use std::sync::atomic::{AtomicU32, AtomicU64, AtomicUsize, Ordering};
use std::sync::{PoisonError, RwLock, RwLockReadGuard, RwLockWriteGuard};

use crate::node::{Dependencies, Dependents, Node};
use crate::revision::{Durability, RevisionCounter};

/// Structural fields, updated as a unit under [`NodeState::write`].
pub(crate) struct NodeInner<K, T> {
    pub data: T,
    pub dependencies: Dependencies<K>,
    pub dependents: Dependents<K>,
    /// Set when the node is removed from the map. A writer that obtained the
    /// node before the removal must not update it; it retries through the map.
    pub detached: bool,
}

/// Concurrently accessible node.
pub(crate) struct NodeState<K, T, const N: usize> {
    id: K,
    verified_at: AtomicU64,
    changed_at: AtomicU64,
    durability: AtomicUsize,
    level: AtomicU32,
    inner: RwLock<NodeInner<K, T>>,
}

impl<K, T, const N: usize> NodeState<K, T, N> {
    pub fn new(
        id: K,
        data: T,
        durability: Durability<N>,
        verified_at: RevisionCounter,
        changed_at: RevisionCounter,
        level: u32,
        dependencies: Dependencies<K>,
    ) -> Self {
        Self {
            id,
            verified_at: AtomicU64::new(verified_at),
            changed_at: AtomicU64::new(changed_at),
            durability: AtomicUsize::new(durability.value()),
            level: AtomicU32::new(level),
            inner: RwLock::new(NodeInner {
                data,
                dependencies,
                dependents: Dependents::default(),
                detached: false,
            }),
        }
    }

    #[inline]
    pub fn verified_at(&self) -> RevisionCounter {
        self.verified_at.load(Ordering::Acquire)
    }

    #[inline]
    pub fn changed_at(&self) -> RevisionCounter {
        self.changed_at.load(Ordering::Acquire)
    }

    #[inline]
    pub fn durability(&self) -> Durability<N> {
        Durability::new(self.durability.load(Ordering::Acquire)).unwrap_or(Durability::volatile())
    }

    #[inline]
    pub fn level(&self) -> u32 {
        self.level.load(Ordering::Acquire)
    }

    /// Lock the structural fields for reading. Excludes writers, so the
    /// atomic fields are stable for the duration of the guard.
    ///
    /// A poisoned lock is recovered rather than propagated: a panic inside a
    /// user callback must not take the whole runtime down with it.
    #[inline]
    pub fn read(&self) -> RwLockReadGuard<'_, NodeInner<K, T>> {
        self.inner.read().unwrap_or_else(PoisonError::into_inner)
    }

    /// Lock the structural fields for writing. Writers of the atomic fields
    /// must hold this lock, so that readers observe a consistent node.
    #[inline]
    pub fn write(&self) -> RwLockWriteGuard<'_, NodeInner<K, T>> {
        self.inner.write().unwrap_or_else(PoisonError::into_inner)
    }

    /// Set durability and level. Caller must hold [`Self::write`].
    #[inline]
    pub fn set_meta(&self, durability: Durability<N>, level: u32) {
        self.durability.store(durability.value(), Ordering::Release);
        self.level.store(level, Ordering::Release);
    }

    /// Set `changed_at`. Caller must hold [`Self::write`].
    #[inline]
    pub fn set_changed_at(&self, rev: RevisionCounter) {
        self.changed_at.store(rev, Ordering::Release);
    }

    /// Set `verified_at`. Caller must hold [`Self::write`].
    #[inline]
    pub fn set_verified_at(&self, rev: RevisionCounter) {
        self.verified_at.store(rev, Ordering::Release);
    }

    /// Raise `verified_at` to `rev` if it is higher (monotonic).
    ///
    /// Caller must hold [`Self::read`] or [`Self::write`]: `fetch_max` commutes
    /// with itself, so concurrent readers may all do this, but durability must
    /// not change underneath.
    #[inline]
    pub fn raise_verified_at(&self, rev: RevisionCounter) {
        self.verified_at.fetch_max(rev, Ordering::AcqRel);
    }
}

impl<K, T, const N: usize> NodeState<K, T, N>
where
    K: Clone,
    T: Clone,
{
    /// Produce a consistent plain-data copy of this node.
    pub fn snapshot(&self) -> Node<K, T, N> {
        self.snapshot_with(&self.read())
    }

    /// Produce a plain-data copy using an already held guard.
    pub fn snapshot_with(&self, inner: &NodeInner<K, T>) -> Node<K, T, N> {
        Node {
            id: self.id.clone(),
            data: inner.data.clone(),
            durability: self.durability(),
            verified_at: self.verified_at(),
            changed_at: self.changed_at(),
            level: self.level(),
            dependencies: inner.dependencies.clone(),
            dependents: inner.dependents.clone(),
        }
    }

    /// Clone only the user data together with `changed_at`.
    pub fn data_and_changed_at(&self) -> (T, RevisionCounter) {
        let inner = self.read();
        (inner.data.clone(), self.changed_at())
    }
}
