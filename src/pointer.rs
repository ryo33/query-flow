/// Version is a monotonically increasing number when a result of a query is changed. Note that this does not increase one by one.
///
/// This does not implement `PartialOrd` and `Ord` because it is not comparable across different queries.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Version(pub u64);

/// Pointer is a pair of query identifier and `Version`.
///
/// This is used to identify a specific version of a query.
///
/// # Examples
///
/// ```
/// # use whale::{Pointer, Version};
/// let p1 = Pointer {
///     query_id: 1,
///     version: Version(5),
/// };
/// let p2 = Pointer {
///     query_id: 1,
///     version: Version(10),
/// };
/// assert!(p1.has_influence_on_update(p2));
/// assert!(!p2.has_influence_on_update(p1));
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Pointer<I> {
    /// K is a unique identifier for a query.
    pub query_id: I,
    /// Version is a monotonically increasing number when a result of a query is changed. Note that this does not increase one by one.
    pub version: Version,
}

/// A revision pointer is a pair of `Pointer` and `InvalidationRevision`.
///
/// This is used to identify a specific precise version of a query that is incremented when it is invalidated.
///
/// # Examples
///
/// ```
/// # use whale::{RevisionPointer, Pointer, Version, InvalidationRevision};
/// let p1 = RevisionPointer {
///     pointer: Pointer {
///         query_id: 1,
///         version: Version(5),
///     },
///     invalidation_revision: InvalidationRevision(2),
/// };
///
/// let p2 = RevisionPointer {
///     pointer: Pointer {
///         query_id: 1,
///         version: Version(5),
///     },
///     invalidation_revision: InvalidationRevision(3),
/// };
///
/// assert!(p1.can_restore(&p2));
/// assert!(!p2.can_restore(&p1));
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
// Important! This does not have `reason` because it is unknown at some point, and it is not needed for equality check.
pub struct RevisionPointer<I> {
    /// Pointer is a pair of `K` and `Version`.
    pub pointer: Pointer<I>,
    /// InvalidationRevision is a query-local monotonically increasing number.
    pub invalidation_revision: InvalidationRevision,
}

impl<I: PartialEq> RevisionPointer<I> {
    /// Returns true if this pointer can be uninvalidated by the other pointer.
    pub fn can_restore(&self, other: &Self) -> bool {
        self.pointer == other.pointer
            && self.invalidation_revision.0 <= other.invalidation_revision.0
    }

    /// Returns true if this pointer is older than the other pointer both in version and invalidation revision.
    pub fn has_newer_version_or_revision(&self, other: Self) -> bool {
        assert!(self.pointer.query_id == other.pointer.query_id);
        self.pointer.version > other.pointer.version
            || self.invalidation_revision > other.invalidation_revision
    }
}

impl<I: PartialEq> Pointer<I> {
    /// Returns true if this pointer should be invalidated if the other pointer is updated.
    pub fn has_influence_on_update(&self, update: Self) -> bool {
        assert!(self.query_id == update.query_id);
        self.version.0 <= update.version.0
    }
}

/// InvalidationRevision is a query-local monotonically increasing number.
///
/// This is used to identify a specific revision of a query that is incremented when it is invalidated.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct InvalidationRevision(pub u64);
