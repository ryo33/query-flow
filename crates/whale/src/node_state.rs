//! Internal, concurrently mutable node storage.
//!
//! [`NodeState`] is what the runtime actually stores. The hot fields that
//! validity checks read (`verified_at`, `changed_at`, `durability`, `level`)
//! are atomics, so readers never take a lock. The structural fields (`data`,
//! `dependencies`, `dependents`) live behind a small mutex that writers hold
//! for the duration of one update, which also serializes writes to the
//! atomics so a locked reader sees a consistent node.
//!
//! The public, plain-data [`Node`] is produced on demand by [`NodeState::snapshot`].

use std::sync::atomic::{AtomicU32, AtomicU64, AtomicUsize, Ordering};
use std::sync::{Mutex, MutexGuard, PoisonError};

use crate::node::{Dependencies, Dependents, Node};
use crate::revision::{Durability, RevisionCounter};

/// Structural fields, updated as a unit under [`NodeState::lock`].
pub(crate) struct NodeInner<K, T> {
    pub data: T,
    pub dependencies: Dependencies<K>,
    pub dependents: Dependents<K>,
}

/// Concurrently accessible node.
pub(crate) struct NodeState<K, T, const N: usize> {
    id: K,
    verified_at: AtomicU64,
    changed_at: AtomicU64,
    durability: AtomicUsize,
    level: AtomicU32,
    inner: Mutex<NodeInner<K, T>>,
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
            inner: Mutex::new(NodeInner {
                data,
                dependencies,
                dependents: Dependents::default(),
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

    /// Lock the structural fields. Writers of the atomic fields must hold this
    /// lock too, so that [`Self::snapshot`] observes a consistent node.
    ///
    /// A poisoned lock is recovered rather than propagated: a panic inside a
    /// user callback must not take the whole runtime down with it.
    #[inline]
    pub fn lock(&self) -> MutexGuard<'_, NodeInner<K, T>> {
        self.inner.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// Set durability and level. Caller must hold [`Self::lock`].
    #[inline]
    pub fn set_meta(&self, durability: Durability<N>, level: u32) {
        self.durability.store(durability.value(), Ordering::Release);
        self.level.store(level, Ordering::Release);
    }

    /// Set `changed_at`. Caller must hold [`Self::lock`].
    #[inline]
    pub fn set_changed_at(&self, rev: RevisionCounter) {
        self.changed_at.store(rev, Ordering::Release);
    }

    /// Set `verified_at`. Caller must hold [`Self::lock`].
    #[inline]
    pub fn set_verified_at(&self, rev: RevisionCounter) {
        self.verified_at.store(rev, Ordering::Release);
    }

    /// Raise `verified_at` to `rev` if it is higher (monotonic). Caller must hold [`Self::lock`].
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
        let inner = self.lock();
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
        let inner = self.lock();
        (inner.data.clone(), self.changed_at())
    }
}
