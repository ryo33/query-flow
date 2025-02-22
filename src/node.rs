use std::sync::Arc;

use crate::{Invalidation, InvalidationRevision, Pointer, QueryId, RevisionPointer, Version};

/// Node is a data structure that represents a state of a query, and it is managed by the runtime.
///
/// Clone is cheap as vectors are wrapped by `Arc`.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Node {
    /// QueryId is a unique identifier for a query.
    pub id: QueryId,
    /// Version is a monotonically increasing number when a result of a query is changed. Note that this does not increase one by one.
    pub version: Version,
    /// InvalidationRevision is a query-local monotonically increasing number.
    pub invalidation_revision: InvalidationRevision,
    /// Dependencies is a list of pointers to the queries that this query depends on.
    pub dependencies: Dependencies,
    /// Dependents is a list of pointers to the queries that depend on this query.
    pub dependents: Dependents,
    /// Invalidations is a list of revision pointers that invalidate this query.
    pub invalidations: Invalidations,
}

impl Node {
    /// Get a pointer to this query.
    pub fn pointer(&self) -> Pointer {
        Pointer {
            query_id: self.id,
            version: self.version,
        }
    }

    /// Get a revision pointer to this query.
    pub fn revision_pointer(&self) -> RevisionPointer {
        RevisionPointer {
            pointer: self.pointer(),
            invalidation_revision: self.invalidation_revision,
        }
    }

    /// Returns true if this query is invalidated.
    pub fn is_invalidated(&self) -> bool {
        !self.invalidations.is_empty()
    }

    /// Remove an invalidator from this query.
    #[must_use]
    pub fn remove_invalidation(&self, invalidator: RevisionPointer) -> Option<Self> {
        if self
            .invalidations
            .iter()
            .any(|i| i.dependency.can_restore(&invalidator))
        {
            let mut node = self.clone();
            node.invalidations = node.invalidations.remove_uninvalidated(invalidator);
            Some(node)
        } else {
            None
        }
    }

    /// Extend invalidations with a list of revision pointers.
    pub fn add_invalidations(&mut self, with: Vec<Invalidation>) {
        let mut invalidations = Vec::clone(&self.invalidations.0);
        invalidations.extend(with);
        self.invalidations = Invalidations(Arc::new(invalidations));
    }

    /// Update the version of a dependency.
    #[must_use]
    pub fn update_version_reference(
        &self,
        previous: RevisionPointer,
        new: RevisionPointer,
    ) -> Self {
        let mut dependencies = Vec::clone(&self.dependencies.0);
        for dependency in dependencies.iter_mut().filter(|p| **p == previous.pointer) {
            *dependency = new.pointer;
        }
        let mut invalidations = Vec::clone(&self.invalidations.0);
        for invalidation in invalidations
            .iter_mut()
            .filter(|i| i.dependency == previous)
        {
            invalidation.dependency = new;
        }
        Self {
            dependencies: Dependencies(Arc::new(dependencies)),
            invalidations: Invalidations(Arc::new(invalidations)),
            ..self.clone()
        }
    }

    /// Returns true if dependents may be updated from the other old node.
    pub fn has_updated_version_or_dependents_from(&self, other: &Self) -> bool {
        // If the version is same and the length of the dependents is same, the dependents are the same because dependents are increasing only and never updated.
        self.version != other.version || self.dependents.len() != other.dependents.len()
    }
}

/// Dependencies is a list of pointers to the queries that this query depends on.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Dependencies(Arc<Vec<Pointer>>);

impl Dependencies {
    /// New dependencies from a list of pointers.
    pub fn new(pointers: Vec<Pointer>) -> Self {
        Dependencies(Arc::new(pointers))
    }

    /// Returns true if this query should be invalidated if the other query is updated.
    pub fn should_be_invalidated_by(&self, update: Pointer) -> bool {
        self.0
            .iter()
            .any(|p| p.query_id == update.query_id && p.has_influence_on_update(update))
    }

    /// Returns true if there are no dependents.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Returns the number of dependents.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Iterate over the dependents.
    pub fn iter(&self) -> impl Iterator<Item = Pointer> + '_ {
        self.0.iter().cloned()
    }
}

impl FromIterator<Pointer> for Dependencies {
    fn from_iter<T: IntoIterator<Item = Pointer>>(iter: T) -> Self {
        Dependencies(Arc::new(iter.into_iter().collect()))
    }
}

/// Dependents is a list of pointers to the queries that depend on this query.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Dependents(Arc<Vec<Pointer>>);

impl Dependents {
    #[must_use]
    /// Returns a new dependents with the pointer added.
    pub(crate) fn added(&self, pointer: Pointer) -> Self {
        let mut dependents = Vec::clone(&self.0);
        if let Some(existing) = dependents
            .iter_mut()
            .find(|p| p.query_id == pointer.query_id)
        {
            existing.version = pointer.version;
        } else {
            dependents.push(pointer);
        }
        Dependents(Arc::new(dependents))
    }

    /// Returns true if there are no dependents.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Returns the number of dependents.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Iterate over the dependents.
    pub fn iter(&self) -> impl Iterator<Item = Pointer> + '_ {
        self.0.iter().cloned()
    }
}

impl FromIterator<Pointer> for Dependents {
    fn from_iter<T: IntoIterator<Item = Pointer>>(iter: T) -> Self {
        Dependents(Arc::new(iter.into_iter().collect()))
    }
}

/// Invalidations is a list of precise pointers that cause this query to be invalidated.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Invalidations(Arc<Vec<Invalidation>>);

impl FromIterator<Invalidation> for Invalidations {
    fn from_iter<T: IntoIterator<Item = Invalidation>>(iter: T) -> Self {
        Invalidations(Arc::new(iter.into_iter().collect()))
    }
}

impl Invalidations {
    /// Returns true if there are no invalidations.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Returns the number of invalidations.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Push an invalidation to the list.
    #[must_use]
    pub fn pushed(&self, invalidation: Invalidation) -> Self {
        let mut invalidations = Vec::clone(&self.0);
        invalidations.push(invalidation);
        Invalidations(Arc::new(invalidations))
    }

    /// Remove an invalidator from the invalidations.
    #[must_use]
    pub fn remove_uninvalidated(&self, pointer: RevisionPointer) -> Self {
        let mut invalidations = Vec::clone(&self.0);
        invalidations.retain(|i| !i.dependency.can_restore(&pointer));
        Invalidations(Arc::new(invalidations))
    }

    /// Iterate over the invalidations.
    pub fn iter(&self) -> impl Iterator<Item = Invalidation> + '_ {
        self.0.iter().cloned()
    }
}
