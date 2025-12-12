use std::sync::Arc;

use crate::{Invalidation, InvalidationRevision, Pointer, RevisionPointer, Version};

/// Node is a data structure that represents a state of a query, and it is managed by the runtime.
///
/// Clone is cheap as vectors are wrapped by `Arc`.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Node<K, T> {
    /// K is a unique identifier for a query.
    pub id: K,
    /// A user-provided data for this node. This should be cheap to clone.
    pub data: T,
    /// Version is a monotonically increasing number when a result of a query is changed. Note that this does not increase one by one.
    pub version: Version,
    /// InvalidationRevision is a query-local monotonically increasing number.
    pub invalidation_revision: InvalidationRevision,
    /// Dependencies is a list of pointers to the queries that this query depends on.
    pub dependencies: Dependencies<K>,
    /// Dependents is a list of pointers to the queries that depend on this query.
    pub dependents: Dependents<K>,
    /// Invalidations is a list of revision pointers that invalidate this query.
    pub invalidations: Invalidations<K>,
}

impl<K, T> Node<K, T>
where
    K: Clone + PartialEq + Eq + std::hash::Hash,
    T: Clone,
{
    /// Get a pointer to this query.
    pub fn pointer(&self) -> Pointer<K> {
        Pointer {
            query_id: self.id.clone(),
            version: self.version,
        }
    }

    /// Get a revision pointer to this query.
    pub fn revision_pointer(&self) -> RevisionPointer<K> {
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
    pub fn remove_invalidation(&self, invalidator: RevisionPointer<K>) -> Option<Self> {
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
    pub fn add_invalidations(&mut self, with: Vec<Invalidation<K>>) {
        let mut invalidations = Vec::clone(&self.invalidations.0);
        invalidations.extend(with);
        self.invalidations = Invalidations(Arc::new(invalidations));
    }

    /// Update the version of a dependency.
    #[must_use]
    pub fn update_version_reference(
        &self,
        previous: RevisionPointer<K>,
        new: RevisionPointer<K>,
    ) -> Self {
        let mut dependencies = Vec::clone(&self.dependencies.0);
        for dependency in dependencies.iter_mut().filter(|p| **p == previous.pointer) {
            *dependency = new.pointer.clone();
        }
        let mut invalidations = Vec::clone(&self.invalidations.0);
        for invalidation in invalidations
            .iter_mut()
            .filter(|i| i.dependency == previous)
        {
            invalidation.dependency = new.clone();
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
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Dependencies<K>(Arc<Vec<Pointer<K>>>);

impl<K> Dependencies<K>
where
    K: Clone + PartialEq,
{
    /// New dependencies from a list of pointers.
    pub fn new(pointers: Vec<Pointer<K>>) -> Self {
        Dependencies(Arc::new(pointers))
    }

    /// Returns true if this query should be invalidated if the other query is updated.
    pub fn should_be_invalidated_by(&self, update: Pointer<K>) -> bool {
        self.0
            .iter()
            .any(|p| p.query_id == update.query_id && p.has_influence_on_update(update.clone()))
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
    pub fn iter(&self) -> impl Iterator<Item = &Pointer<K>> + '_ {
        self.0.iter()
    }
}

impl<K> FromIterator<Pointer<K>> for Dependencies<K> {
    fn from_iter<T: IntoIterator<Item = Pointer<K>>>(iter: T) -> Self {
        Dependencies(Arc::new(iter.into_iter().collect()))
    }
}

/// Dependents is a list of pointers to the queries that depend on this query.
#[derive(Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Dependents<I>(Arc<Vec<Pointer<I>>>);

impl<K> Dependents<K>
where
    K: Clone + PartialEq,
{
    #[must_use]
    /// Returns a new dependents with the pointer added.
    pub(crate) fn added(&self, pointer: Pointer<K>) -> Self {
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
    pub fn iter(&self) -> impl Iterator<Item = &Pointer<K>> + '_ {
        self.0.iter()
    }
}

impl<K> Default for Dependents<K> {
    fn default() -> Self {
        Dependents(Default::default())
    }
}

impl<K> Clone for Dependents<K> {
    fn clone(&self) -> Self {
        Dependents(self.0.clone())
    }
}

impl<K> FromIterator<Pointer<K>> for Dependents<K> {
    fn from_iter<T: IntoIterator<Item = Pointer<K>>>(iter: T) -> Self {
        Dependents(Arc::new(iter.into_iter().collect()))
    }
}

/// Invalidations is a list of precise pointers that cause this query to be invalidated.
#[derive(Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Invalidations<K>(Arc<Vec<Invalidation<K>>>);

impl<K> Default for Invalidations<K> {
    fn default() -> Self {
        Invalidations(Default::default())
    }
}

impl<K> Clone for Invalidations<K> {
    fn clone(&self) -> Self {
        Invalidations(self.0.clone())
    }
}

impl<K> FromIterator<Invalidation<K>> for Invalidations<K> {
    fn from_iter<T: IntoIterator<Item = Invalidation<K>>>(iter: T) -> Self {
        Invalidations(Arc::new(iter.into_iter().collect()))
    }
}

impl<K> Invalidations<K>
where
    K: Clone + PartialEq,
{
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
    pub fn pushed(&self, invalidation: Invalidation<K>) -> Self {
        let mut invalidations = Vec::clone(&self.0);
        invalidations.push(invalidation);
        Invalidations(Arc::new(invalidations))
    }

    /// Remove an invalidator from the invalidations.
    #[must_use]
    pub fn remove_uninvalidated(&self, pointer: RevisionPointer<K>) -> Self {
        let mut invalidations = Vec::clone(&self.0);
        invalidations.retain(|i| !i.dependency.can_restore(&pointer));
        Invalidations(Arc::new(invalidations))
    }

    /// Iterate over the invalidations.
    pub fn iter(&self) -> impl Iterator<Item = &Invalidation<K>> + '_ {
        self.0.iter()
    }
}
