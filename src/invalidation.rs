use crate::RevisionPointer;

/// Invalidation is a record why a query is invalidated.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Invalidation {
    /// Source is the pointer that causes this query to be invalidated.
    pub source: RevisionPointer,
    /// Revision pointer to a dependency that is invalidated.
    pub dependency: RevisionPointer,
    /// Reason is the reason why this query is invalidated.
    pub reason: InvalidationReason,
}

impl Invalidation {
    /// Create a new invalidation as source.
    pub fn new_source(source: RevisionPointer, reason: InvalidationReason) -> Self {
        Self {
            source,
            dependency: source,
            reason,
        }
    }
}

/// InvalidatedReason is a reason why a query is invalidated.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum InvalidationReason {
    /// Invalidated is a reason why a query is invalidated by another query is invalidated.
    DependencyInvalidated,
    /// NewVersion is a reason why a query is invalidated by a new version of another query.
    NewVersion,
    /// Removed is a reason why a query is invalidated by the removal of another query.
    Removed,
}
