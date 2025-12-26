//! Revision and Durability types for the Whale incremental computation system.
//!
//! This module provides the foundational types for tracking revisions
//! at different durability levels, following the Lean4 formal specification.

use std::sync::atomic::{AtomicU64, Ordering};

/// Revision counter type - monotonically increasing counter for tracking changes.
pub type RevisionCounter = u64;

/// Durability level: 0 = most volatile, N-1 = most stable.
///
/// A node's durability determines which revision counter(s) are used to track
/// its validity. Lower durability levels change more frequently.
///
/// # Invariant
/// A node's durability must not exceed the minimum durability of its dependencies.
/// This ensures that a node doesn't promise to be more stable than its sources.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Durability<const N: usize>(usize);

impl<const N: usize> Durability<N> {
    /// Create a new durability level.
    ///
    /// Returns `None` if `level >= N`.
    #[inline]
    pub const fn new(level: usize) -> Option<Self> {
        if level < N {
            Some(Self(level))
        } else {
            None
        }
    }

    /// Get the numeric value of this durability level.
    #[inline]
    pub const fn value(&self) -> usize {
        self.0
    }

    /// Most volatile durability level (0).
    #[inline]
    pub const fn volatile() -> Self {
        Self(0)
    }

    /// Most stable durability level (N-1).
    #[inline]
    pub const fn stable() -> Self {
        Self(N - 1)
    }

    /// Get the minimum of two durability levels.
    #[inline]
    pub fn min(self, other: Self) -> Self {
        if self.0 <= other.0 {
            self
        } else {
            other
        }
    }
}

/// Revision snapshot: array of counters indexed by durability level.
///
/// `revision[d]` is the counter for durability level `d`.
/// When a node at durability D changes, we increment `revision[0..=D]`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Revision<const N: usize> {
    counters: [RevisionCounter; N],
}

// Manual serde implementation to handle const generic arrays
#[cfg(feature = "serde")]
impl<const N: usize> serde::Serialize for Revision<N> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.counters.as_slice().serialize(serializer)
    }
}

#[cfg(feature = "serde")]
impl<'de, const N: usize> serde::Deserialize<'de> for Revision<N> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let vec: Vec<RevisionCounter> = Vec::deserialize(deserializer)?;
        if vec.len() != N {
            return Err(serde::de::Error::custom(format!(
                "expected {} elements, got {}",
                N,
                vec.len()
            )));
        }
        let mut counters = [0; N];
        counters.copy_from_slice(&vec);
        Ok(Self { counters })
    }
}

impl<const N: usize> Default for Revision<N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const N: usize> Revision<N> {
    /// Create a new revision with all counters at 0.
    #[inline]
    pub const fn new() -> Self {
        Self { counters: [0; N] }
    }

    /// Get the revision counter for durability level `d`.
    #[inline]
    pub fn get(&self, d: Durability<N>) -> RevisionCounter {
        self.counters[d.0]
    }

    /// Set the revision counter for durability level `d`.
    #[inline]
    pub fn set(&mut self, d: Durability<N>, value: RevisionCounter) {
        self.counters[d.0] = value;
    }

    /// Get mutable reference to the underlying counters array.
    #[inline]
    pub fn counters_mut(&mut self) -> &mut [RevisionCounter; N] {
        &mut self.counters
    }
}

/// Atomic revision counters for concurrent access.
///
/// This structure holds per-durability-level revision counters that can be
/// atomically incremented. Per the specification, when incrementing at level D,
/// we must also increment all levels 0..=D.
pub struct AtomicRevision<const N: usize> {
    counters: [AtomicU64; N],
}

impl<const N: usize> Default for AtomicRevision<N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const N: usize> AtomicRevision<N> {
    /// Create new atomic revision with all counters at 0.
    pub fn new() -> Self {
        Self {
            counters: std::array::from_fn(|_| AtomicU64::new(0)),
        }
    }

    /// Get current revision counter for durability level `d`.
    #[inline]
    pub fn get(&self, d: Durability<N>) -> RevisionCounter {
        self.counters[d.0].load(Ordering::Acquire)
    }

    /// Increment revision at durability level `d` and all lower levels (0..=d).
    ///
    /// Per specification: "for i in 0..=D: revision[i].fetch_add(1, AcqRel)"
    ///
    /// Returns the new revision counter at level `d`.
    pub fn increment(&self, d: Durability<N>) -> RevisionCounter {
        let mut new_rev = 0;
        for i in 0..=d.0 {
            new_rev = self.counters[i].fetch_add(1, Ordering::AcqRel) + 1;
        }
        new_rev
    }

    /// Take a snapshot of the current revision state.
    pub fn snapshot(&self) -> Revision<N> {
        let mut counters = [0; N];
        for (dst, src) in counters.iter_mut().zip(self.counters.iter()) {
            *dst = src.load(Ordering::Acquire);
        }
        Revision { counters }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_durability_creation() {
        let d: Option<Durability<3>> = Durability::new(0);
        assert!(d.is_some());
        assert_eq!(d.unwrap().value(), 0);

        let d: Option<Durability<3>> = Durability::new(2);
        assert!(d.is_some());
        assert_eq!(d.unwrap().value(), 2);

        let d: Option<Durability<3>> = Durability::new(3);
        assert!(d.is_none());
    }

    #[test]
    fn test_durability_volatile_stable() {
        let volatile: Durability<3> = Durability::volatile();
        assert_eq!(volatile.value(), 0);

        let stable: Durability<3> = Durability::stable();
        assert_eq!(stable.value(), 2);
    }

    #[test]
    fn test_durability_min() {
        let d0: Durability<3> = Durability::new(0).unwrap();
        let d1: Durability<3> = Durability::new(1).unwrap();
        let d2: Durability<3> = Durability::new(2).unwrap();

        assert_eq!(d0.min(d1), d0);
        assert_eq!(d1.min(d0), d0);
        assert_eq!(d1.min(d2), d1);
    }

    #[test]
    fn test_revision_operations() {
        let mut rev: Revision<3> = Revision::new();
        let d1: Durability<3> = Durability::new(1).unwrap();

        assert_eq!(rev.get(d1), 0);
        rev.set(d1, 42);
        assert_eq!(rev.get(d1), 42);
    }

    #[test]
    fn test_atomic_revision_increment() {
        let atomic: AtomicRevision<3> = AtomicRevision::new();
        let d0: Durability<3> = Durability::new(0).unwrap();
        let d1: Durability<3> = Durability::new(1).unwrap();
        let d2: Durability<3> = Durability::new(2).unwrap();

        // Increment at level 0 - only level 0 should increase
        let new_rev = atomic.increment(d0);
        assert_eq!(new_rev, 1);
        assert_eq!(atomic.get(d0), 1);
        assert_eq!(atomic.get(d1), 0);
        assert_eq!(atomic.get(d2), 0);

        // Increment at level 2 - levels 0, 1, 2 should all increase
        let new_rev = atomic.increment(d2);
        assert_eq!(new_rev, 1); // d2 goes from 0 to 1
        assert_eq!(atomic.get(d0), 2); // d0 goes from 1 to 2
        assert_eq!(atomic.get(d1), 1); // d1 goes from 0 to 1
        assert_eq!(atomic.get(d2), 1); // d2 goes from 0 to 1
    }

    #[test]
    fn test_atomic_revision_snapshot() {
        let atomic: AtomicRevision<3> = AtomicRevision::new();
        let d1: Durability<3> = Durability::new(1).unwrap();

        atomic.increment(d1);

        let snapshot = atomic.snapshot();
        assert_eq!(snapshot.get(Durability::new(0).unwrap()), 1);
        assert_eq!(snapshot.get(Durability::new(1).unwrap()), 1);
        assert_eq!(snapshot.get(Durability::new(2).unwrap()), 0);
    }
}
