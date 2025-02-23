use crate::RevisionPointer;

/// Invalidation is a record why a query is invalidated.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Invalidation<I> {
    /// Source is the pointer that causes this query to be invalidated.
    pub source: RevisionPointer<I>,
    /// Revision pointer to a dependency that is invalidated.
    pub dependency: RevisionPointer<I>,
    /// Reason is the reason why this query is invalidated.
    pub reason: InvalidationReason,
}

impl<I> Invalidation<I> {
    /// Create a new invalidation as source.
    pub fn new_source(source: RevisionPointer<I>, reason: InvalidationReason) -> Self
    where
        I: Clone,
    {
        Self {
            source: source.clone(),
            dependency: source,
            reason,
        }
    }
}

/// InvalidatedReason is a reason why a query is invalidated.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum InvalidationReason {
    /// Invalidated is a reason why a query is invalidated by another query is invalidated.
    DependencyInvalidated,
    /// NewVersion is a reason why a query is invalidated by a new version of another query.
    NewVersion,
    /// Removed is a reason why a query is invalidated by the removal of another query.
    Removed,
}
