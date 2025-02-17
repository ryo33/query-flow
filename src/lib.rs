#![deny(missing_docs)]
#![doc = include_str!("../README.md")]

use std::sync::{
    atomic::{AtomicU64, Ordering},
    Arc,
};

use papaya::{Compute, HashMap, Operation};

#[derive(Debug, Default, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
/// Runtime is a data structure that manages the all state of the dependency tracking system.
///
/// This is cheap to clone, so you can pass it around by just cloning it.
pub struct Runtime {
    nodes: Arc<HashMap<QueryId, Node, ahash::RandomState>>,
    next_version: Arc<AtomicU64>,
}

#[test]
fn test_send_sync() {
    fn assert_send<T: Send>() {}
    fn assert_sync<T: Sync>() {}
    assert_send::<Runtime>();
    assert_sync::<Runtime>();
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
/// QueryId is a unique identifier for a query.
pub struct QueryId(pub u64);

/// Version is a monotonically increasing number when a result of a query is changed. Note that this does not increase one by one.
///
/// This does not implement `PartialOrd` and `Ord` because it is not comparable across different queries.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Version(pub u64);

/// Pointer is a pair of `QueryId` and `Version`.
///
/// This is used to identify a specific version of a query.
///
/// # Examples
///
/// ```
/// # use whale::{Pointer, QueryId, Version};
/// let p1 = Pointer {
///     query_id: QueryId(1),
///     version: Version(5),
/// };
/// let p2 = Pointer {
///     query_id: QueryId(1),
///     version: Version(10),
/// };
/// assert!(p1.older_than(p2));
/// assert!(!p2.older_than(p1));
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Pointer {
    /// QueryId is a unique identifier for a query.
    pub query_id: QueryId,
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
/// # use whale::{RevisionPointer, Pointer, QueryId, Version, InvalidationRevision};
/// let p1 = RevisionPointer {
///     pointer: Pointer {
///         query_id: QueryId(1),
///         version: Version(5),
///     },
///     invalidation_revision: InvalidationRevision(2),
/// };
///
/// let p2 = RevisionPointer {
///     pointer: Pointer {
///         query_id: QueryId(1),
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
pub struct RevisionPointer {
    /// Pointer is a pair of `QueryId` and `Version`.
    pub pointer: Pointer,
    /// InvalidationRevision is a query-local monotonically increasing number.
    pub invalidation_revision: InvalidationRevision,
}

impl RevisionPointer {
    /// Returns true if this pointer can be uninvalidated by the other pointer.
    pub fn can_restore(&self, other: &Self) -> bool {
        self.pointer == other.pointer
            && self.invalidation_revision.0 <= other.invalidation_revision.0
    }
}

impl Pointer {
    /// Returns true if this pointer should be invalidated if the other pointer is updated.
    pub fn older_than(&self, update: Self) -> bool {
        if self.query_id != update.query_id {
            return false;
        }
        // depends on updated version or more old version
        self.version.0 <= update.version.0
    }
}

/// InvalidationRevision is a query-local monotonically increasing number.
///
/// This is used to identify a specific revision of a query that is incremented when it is invalidated.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct InvalidationRevision(pub u64);

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
            .any(|i| i.pointer.can_restore(&invalidator))
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
        for invalidation in invalidations.iter_mut().filter(|i| i.pointer == previous) {
            invalidation.pointer = new;
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
    /// Returns true if this query should be invalidated if the other query is updated.
    pub fn should_be_invalidated_by(&self, update: Pointer) -> bool {
        self.0.iter().any(|p| p.older_than(update))
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

/// Invalidation is a record why a query is invalidated.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Invalidation {
    /// Source is the pointer that causes this query to be invalidated.
    pub source: RevisionPointer,
    /// Revision pointer to a dependency that is invalidated.
    pub pointer: RevisionPointer,
    /// Reason is the reason why this query is invalidated.
    pub reason: InvalidationReason,
}

impl Invalidation {
    /// Create a new invalidation as source.
    pub fn new_source(source: RevisionPointer, reason: InvalidationReason) -> Self {
        Self {
            source,
            pointer: source,
            reason,
        }
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
        invalidations.retain(|i| !i.pointer.can_restore(&pointer));
        Invalidations(Arc::new(invalidations))
    }

    /// Iterate over the invalidations.
    pub fn iter(&self) -> impl Iterator<Item = Invalidation> + '_ {
        self.0.iter().cloned()
    }
}

/// QueryRegistrationResult is a result of registering a new version.
pub struct QueryRegistrationResult {
    /// Node is the new node after registering a new version.
    pub node: Node,
    /// Previous version of the node.
    pub old_node: Option<Node>,
}

impl QueryRegistrationResult {
    /// Returns true if the node is invalidated or the old node has dependents.
    pub fn has_invalidation_effects(&self) -> bool {
        self.node.is_invalidated()
            || self
                .old_node
                .as_ref()
                .map(|n| !n.dependents.is_empty())
                .unwrap_or(false)
    }
}

/// QueryRemovalResult is a result of `Runtime::remove`.
pub struct QueryRemovalResult {
    /// Removed is the node that is removed.
    pub removed: Option<Node>,
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

impl Runtime {
    /// Create a new runtime.
    pub fn new() -> Self {
        Default::default()
    }

    /// Get the node for a query.
    ///
    /// This may read a not invalidated node while processing a new version of dependencies or removing a node.
    pub fn get(&self, query_id: QueryId) -> Option<Node> {
        self.nodes.pin().get(&query_id).cloned()
    }

    /// Iterate over all nodes.
    pub fn keys(&self) -> Vec<QueryId> {
        self.nodes.pin().keys().cloned().collect()
    }

    /// Remove a node from the runtime. If the node is returned and has dependents, you should update them.
    #[must_use]
    pub fn remove(&self, query_id: QueryId) -> QueryRemovalResult {
        let removed = self.nodes.pin().remove(&query_id).cloned();
        if let Some(removed) = &removed {
            for dependent in removed.dependents.0.iter().cloned() {
                self.invalidate(
                    dependent,
                    Invalidation::new_source(
                        removed.revision_pointer(),
                        InvalidationReason::Removed,
                    ),
                );
            }
        }
        QueryRemovalResult { removed }
    }

    /// Uninvalidate a specific revision pointer.
    pub fn uninvalidate(&self, revision_pointer: RevisionPointer) {
        let pinned = self.nodes.pin();
        enum AbortReason {
            NotFound,
            AlreadyUpdated,
            MoreInvalidated,
            AlreadyUninvalidated,
        }
        let result = pinned.compute(revision_pointer.pointer.query_id, |node| {
            let Some((_, node)) = node else {
                return Operation::Abort(AbortReason::NotFound);
            };
            if !node.is_invalidated() {
                return Operation::Abort(AbortReason::AlreadyUninvalidated);
            }
            if node.version != revision_pointer.pointer.version {
                return Operation::Abort(AbortReason::AlreadyUpdated);
            }
            if node.invalidation_revision.0 > revision_pointer.invalidation_revision.0 {
                return Operation::Abort(AbortReason::MoreInvalidated);
            }
            let mut node = node.clone();
            node.invalidations = Default::default();
            // This does not increase the invalidation version.
            Operation::Insert(node)
        });
        match result {
            Compute::Inserted(_, _) => unreachable!(),
            Compute::Updated {
                old: (_, old),
                new: _,
            } => {
                // Recursively uninvalidate dependents if they were invalidated by this node
                for dependent in old.dependents.iter() {
                    self.remove_invalidator(dependent, revision_pointer);
                }
            }
            Compute::Removed(_, _) => unreachable!(),
            Compute::Aborted(_) => {}
        }
    }

    /// Remove an invalidator from a specific pointer.
    pub fn remove_invalidator(&self, pointer: Pointer, invalidator: RevisionPointer) {
        let pinned = self.nodes.pin();
        let result = pinned.compute(pointer.query_id, |node| {
            let Some((_, node)) = node else {
                return Operation::Abort(());
            };
            if node.version != pointer.version {
                return Operation::Abort(());
            }
            if !node.is_invalidated() {
                return Operation::Abort(());
            }
            if let Some(node) = node.remove_invalidation(invalidator) {
                Operation::Insert(node)
            } else {
                Operation::Abort(())
            }
        });
        match result {
            Compute::Inserted(_, _) => unreachable!(),
            Compute::Updated {
                old: (_, old),
                new: (_, new),
            } => {
                if !new.is_invalidated() {
                    // recursively uninvalidate dependents
                    for dependent in new.dependents.iter() {
                        self.remove_invalidator(dependent, old.revision_pointer());
                    }
                }
            }
            Compute::Removed(_, _) => unreachable!(),
            Compute::Aborted(_) => {}
        }
    }

    /// Detect a cycle in the dependency graph.
    pub fn has_cycle(&self, query_id: QueryId) -> bool {
        let mut set = ahash::HashSet::default();
        self.has_cycle_with_set(query_id, &mut set)
    }

    /// Detect a cycle in the dependency graph with a set.
    pub fn has_cycle_with_set(&self, query_id: QueryId, set: &mut ahash::HashSet<QueryId>) -> bool {
        if set.contains(&query_id) {
            return true;
        }
        set.insert(query_id);
        for dependency in self.get(query_id).unwrap().dependencies.0.iter().cloned() {
            if self.has_cycle_with_set(dependency.query_id, set) {
                return true;
            }
        }
        false
    }

    /// Remove a query if it is not depended by any other queries. This is useful for garbage collection.
    pub fn remove_if_unused(&self, query_id: QueryId) -> Option<Node> {
        let pinned = self.nodes.pin();
        let result = pinned.compute(query_id, |node| {
            let Some((_, node)) = node else {
                return Operation::Abort(());
            };
            if node.dependents.0.is_empty() {
                Operation::Remove
            } else {
                Operation::Abort(())
            }
        });
        match result {
            Compute::Inserted(_, _) => unreachable!(),
            Compute::Updated { .. } => unreachable!(),
            Compute::Removed(_, node) => Some(node.clone()),
            Compute::Aborted(_) => None,
        }
    }

    /// Recursively invalidate a specific version of a query, and returns the pointers of the invalidated nodes.
    pub fn invalidate(&self, pointer: Pointer, invalidation: Invalidation) {
        if invalidation.source.pointer == pointer {
            eprintln!("cyclic dependency detected on {:?}", pointer);
            return;
        }
        let pinned = self.nodes.pin();
        let result = pinned.compute(pointer.query_id, |node| {
            let Some((_, node)) = node else {
                return Operation::Abort(());
            };
            if node.pointer().older_than(pointer) {
                let mut node = node.clone();
                node.invalidations = node.invalidations.pushed(invalidation);
                node.invalidation_revision.0 += 1;
                Operation::Insert(node)
            } else {
                Operation::Abort(())
            }
        });
        match result {
            Compute::Inserted(_, _) => unreachable!(),
            Compute::Updated {
                old: _,
                new: (_, node),
            } => {
                // Recursively invalidate dependents
                for dependent in node.dependents.iter() {
                    self.invalidate(
                        dependent,
                        Invalidation {
                            source: invalidation.source,
                            pointer: node.revision_pointer(),
                            reason: InvalidationReason::DependencyInvalidated,
                        },
                    );
                }
            }
            Compute::Removed(_, _) => unreachable!(),
            Compute::Aborted(_) => {}
        }
    }

    /// Register a new version for a query. If the previous version is returned, you should update all dependents.
    #[must_use]
    pub fn register(
        &self,
        query_id: QueryId,
        dependencies: Vec<Pointer>,
    ) -> QueryRegistrationResult {
        let dependencies = Dependencies(Arc::new(dependencies));
        let (new_node, old_node) = self.create_new_version(query_id, dependencies.clone());

        // At this point, other threads may be read this version without invalidated state before checking if it is invalidated.

        // Register dependents
        // While registering dependents, other threads may be update or invalidate those dependencies, so we need to collect all invalidated dependencies for this caller.
        let invalidations = self.update_dependency_graph(new_node.pointer(), dependencies);
        let new_node = self
            .extend_invalidations(new_node.pointer(), invalidations)
            .unwrap_or(new_node);

        if let Some(old_node) = &old_node {
            // Recursively invalidate old dependents
            for dependent in old_node.dependents.iter() {
                self.invalidate(
                    dependent,
                    Invalidation::new_source(
                        new_node.revision_pointer(),
                        InvalidationReason::NewVersion,
                    ),
                );
            }
        }

        QueryRegistrationResult {
            node: new_node,
            old_node,
        }
    }

    /// Register a new version for a query that has no change. So, dependents are not invalidated.
    ///
    /// This returns invalidated pointers that are invalidated when the dependencies are updated.
    pub fn update_dependencies(
        &self,
        query_id: QueryId,
        dependencies: Vec<Pointer>,
    ) -> QueryRegistrationResult {
        let dependencies = Dependencies(Arc::new(dependencies));
        let (new_node, old_node) = self.create_new_version(query_id, dependencies.clone());

        // At this point, other threads may be read this version without invalidated state before checking if it is invalidated.

        // Register dependents
        // While registering dependents, other threads may be update or invalidate those dependencies, so we need to collect all invalidated dependencies for this caller.
        let invalidations = self.update_dependency_graph(new_node.pointer(), dependencies);
        let new_node = self
            .extend_invalidations(new_node.pointer(), invalidations)
            .unwrap_or(new_node);

        if let Some(old_node) = &old_node {
            for dependent in old_node.dependents.0.iter().cloned() {
                self.update_dependency_version(
                    dependent,
                    old_node.revision_pointer(),
                    new_node.revision_pointer(),
                );
                if new_node.is_invalidated() {
                    self.invalidate(
                        dependent,
                        Invalidation::new_source(
                            new_node.revision_pointer(),
                            InvalidationReason::DependencyInvalidated,
                        ),
                    );
                }
            }
        }
        QueryRegistrationResult {
            node: new_node,
            old_node,
        }
    }

    #[must_use]
    fn create_new_version(
        &self,
        query_id: QueryId,
        dependencies: Dependencies,
    ) -> (Node, Option<Node>) {
        // Register the new version
        enum InsertAbortReason {
            AlreadyOld,
        }
        let pinned = self.nodes.pin();
        let result = pinned.compute(query_id, |previous| {
            let version = Version(self.next_version.fetch_add(1, Ordering::Relaxed));
            if let Some((_, node)) = previous {
                if node.version.0 >= version.0 {
                    return Operation::Abort(InsertAbortReason::AlreadyOld);
                }
            }

            Operation::Insert(Node {
                id: query_id,
                version,
                dependencies: dependencies.clone(),
                dependents: Default::default(),
                invalidation_revision: Default::default(),
                invalidations: Default::default(),
            })
        });

        match result {
            Compute::Inserted(_key, new) => (new.clone(), None),
            Compute::Updated {
                old: (_, old),
                new: (_, new),
            } => (new.clone(), Some(old.clone())),
            Compute::Removed(_, _) => unreachable!(),
            Compute::Aborted(InsertAbortReason::AlreadyOld) => unreachable!(
                "version is calculated within atomic computation, so latter version should be always newer"
            ),
        }
    }

    /// Update dependencies for a query atomically
    #[must_use]
    fn update_dependency_graph(
        &self,
        pointer: Pointer,
        dependencies: Dependencies,
    ) -> Vec<Invalidation> {
        let mut invalidations = vec![];
        for dependency in dependencies.0.iter().cloned() {
            enum AbortReason {
                NotFound,
                AlreadyInvalidated(Invalidation),
                AlreadyUpdated(Invalidation),
            }
            let pinned = self.nodes.pin();
            let result = pinned.compute(dependency.query_id, |node| {
                let Some((_, node)) = node else {
                    return Operation::Abort(AbortReason::NotFound);
                };
                if node.version != dependency.version {
                    assert!(node.version.0 > dependency.version.0);
                    return Operation::Abort(AbortReason::AlreadyUpdated(
                        Invalidation::new_source(
                            node.revision_pointer(),
                            InvalidationReason::NewVersion,
                        ),
                    ));
                }
                if node.is_invalidated() {
                    return Operation::Abort(AbortReason::AlreadyInvalidated(
                        Invalidation::new_source(
                            node.revision_pointer(),
                            InvalidationReason::DependencyInvalidated,
                        ),
                    ));
                }
                let mut node = node.clone();
                node.dependents = node.dependents.added(pointer);
                Operation::Insert(node)
            });
            match result {
                Compute::Inserted(_, _) => {}
                Compute::Updated { .. } => {}
                Compute::Removed(_, _) => {}
                Compute::Aborted(AbortReason::NotFound) => {}
                Compute::Aborted(AbortReason::AlreadyInvalidated(invalidation)) => {
                    invalidations.push(invalidation);
                }
                Compute::Aborted(AbortReason::AlreadyUpdated(invalidation)) => {
                    invalidations.push(invalidation);
                }
            }
        }
        invalidations
    }

    /// Extend invalidations to a node, and returns the new node.
    #[must_use]
    fn extend_invalidations(
        &self,
        pointer: Pointer,
        invalidations: Vec<Invalidation>,
    ) -> Option<Node> {
        if !invalidations.is_empty() {
            let pinned = self.nodes.pin();
            let result = pinned.compute(pointer.query_id, |node| {
                let Some((_, node)) = node else {
                    return Operation::Abort(());
                };
                if node.version != pointer.version {
                    return Operation::Abort(());
                }
                let mut node = node.clone();
                node.add_invalidations(invalidations.clone());
                Operation::Insert(node)
            });
            match result {
                Compute::Inserted(_, _) => unreachable!(),
                Compute::Updated {
                    old: _,
                    new: (_, new),
                } => {
                    return Some(new.clone());
                }
                Compute::Removed(_, _) => unreachable!(),
                Compute::Aborted(_) => {}
            }
        }
        None
    }

    fn update_dependency_version(
        &self,
        pointer: Pointer,
        previous: RevisionPointer,
        new: RevisionPointer,
    ) {
        let pinned = self.nodes.pin();
        pinned.update(pointer.query_id, |node| {
            node.update_version_reference(previous, new)
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Test basic node creation and versioning
    #[test]
    fn test_basic_registration() {
        let rt = Runtime::new();
        let id = QueryId(1);

        // First registration
        let result = rt.register(id, vec![]);
        assert_eq!(result.node.id, id);
        assert_eq!(result.node.version.0, 0);
        assert!(result.old_node.is_none());

        // Second registration should increment version
        let result2 = rt.register(id, vec![]);
        assert_eq!(result2.node.version.0, 1);
        assert_eq!(result2.old_node, Some(result.node));
    }

    // Test dependency tracking basics
    #[test]
    fn test_dependency_management() {
        let rt = Runtime::new();
        let a = QueryId(1);
        let b = QueryId(2);

        // b depends on a
        let result = rt.register(a, vec![]);
        let b_result = rt.register(b, vec![result.node.pointer()]);

        // Verify dependency tracking
        let a_node = rt.get(a).unwrap();
        assert_eq!(
            a_node.dependents,
            Dependents::from_iter([b_result.node.pointer()])
        );
        assert_eq!(
            b_result.node.dependencies,
            Dependencies::from_iter([a_node.pointer()])
        );
    }

    // Test basic invalidation flow
    #[test]
    fn test_dependency_invalidation() {
        let rt = Runtime::new();
        let a = QueryId(1);
        let b = QueryId(2);

        // Setup initial state
        let result = rt.register(a, vec![]);
        let _ = rt.register(b, vec![result.node.pointer()]);

        // Update a to invalidate b
        let a_update = rt.register(a, vec![]);
        let b_node = rt.get(b).unwrap();
        assert_eq!(
            b_node.invalidations,
            Invalidations::from_iter([Invalidation {
                source: a_update.node.revision_pointer(),
                pointer: a_update.node.revision_pointer(),
                reason: InvalidationReason::NewVersion,
            }])
        );
    }

    // Test removal invalidation
    #[test]
    fn test_removal_invalidation() {
        let rt = Runtime::new();
        let a = QueryId(1);
        let b = QueryId(2);

        let result = rt.register(a, vec![]);
        let _ = rt.register(b, vec![result.node.pointer()]);

        // Remove a and check b invalidation
        let removal = rt.remove(a);
        assert!(removal.removed.is_some());
        let b_node = rt.get(b).unwrap();
        assert!(b_node.is_invalidated());
        assert_eq!(
            b_node.invalidations,
            Invalidations::from_iter([Invalidation {
                source: result.node.revision_pointer(),
                pointer: result.node.revision_pointer(),
                reason: InvalidationReason::Removed,
            }])
        );
    }

    // Test dependency chain invalidation
    #[test]
    fn test_transitive_invalidation() {
        let rt = Runtime::new();
        let a = QueryId(1);
        let b = QueryId(2);
        let c = QueryId(3);

        let result = rt.register(a, vec![]);
        let b_result = rt.register(b, vec![result.node.pointer()]);
        let _ = rt.register(c, vec![b_result.node.pointer()]);

        // Update a should invalidate both b and c
        let a_new = rt.register(a, vec![]).node;
        let b_node = rt.get(b).unwrap();
        let c_node = rt.get(c).unwrap();
        assert!(b_node.is_invalidated());
        assert!(c_node.is_invalidated());
        assert_eq!(
            b_node.invalidations,
            Invalidations::from_iter([Invalidation::new_source(
                a_new.revision_pointer(),
                InvalidationReason::NewVersion
            )])
        );
        assert_eq!(
            c_node.invalidations,
            Invalidations::from_iter([Invalidation {
                source: a_new.revision_pointer(),
                pointer: b_node.revision_pointer(),
                reason: InvalidationReason::DependencyInvalidated,
            }])
        );
    }

    // Test cycle detection
    #[test]
    fn test_cycle_detection() {
        let rt = Runtime::new();
        let a = QueryId(1);
        let b = QueryId(2);

        let a_result = rt.register(a, vec![]);
        let b_result = rt.register(b, vec![a_result.node.pointer()]);
        let _ = rt.register(a, vec![b_result.node.pointer()]).node;

        assert!(rt.has_cycle(a));
        assert!(rt.has_cycle(b));
    }

    // loop invalidation in b, c, and d, but a triggers the invalidation.
    #[test]
    fn test_cyclic_invalidation_from_outer_source() {
        let rt = Runtime::new();
        let a = QueryId(1);
        let b = QueryId(2);
        let c = QueryId(3);
        let d = QueryId(4);

        let a_result = rt.register(a, vec![]);
        let b_result = rt.register(b, vec![a_result.node.pointer()]);
        let c_result = rt.register(c, vec![b_result.node.pointer()]);
        let d_result = rt.register(d, vec![c_result.node.pointer()]);
        let b_result = rt.register(b, vec![a_result.node.pointer(), d_result.node.pointer()]);

        let a_new = rt.register(a, vec![]).node;

        let b_node = rt.get(b).unwrap();
        let c_node = rt.get(c).unwrap();
        let d_node = rt.get(d).unwrap();
        assert!(b_node.is_invalidated());
        assert!(c_node.is_invalidated());
        assert!(d_node.is_invalidated());
        assert_eq!(
            b_node.invalidations,
            Invalidations::from_iter([Invalidation::new_source(
                a_new.revision_pointer(),
                InvalidationReason::NewVersion,
            )])
        );
        assert_eq!(
            c_node.invalidations,
            Invalidations::from_iter([Invalidation::new_source(
                b_result.node.revision_pointer(),
                InvalidationReason::NewVersion,
            )])
        );
        assert_eq!(
            d_node.invalidations,
            Invalidations::from_iter([Invalidation {
                source: b_result.node.revision_pointer(),
                pointer: c_node.revision_pointer(),
                reason: InvalidationReason::DependencyInvalidated,
            }])
        );
    }

    // Test concurrent invalidations
    #[test]
    fn test_multiple_invalidation_paths() {
        let rt = Runtime::new();
        let a = QueryId(1);
        let b = QueryId(2);
        let c = QueryId(3);

        let a_result = rt.register(a, vec![]);
        let b_result = rt.register(b, vec![a_result.node.pointer()]);
        let _ = rt.register(c, vec![a_result.node.pointer(), b_result.node.pointer()]);

        let a_new = rt.register(a, vec![]).node;
        let b_node = rt.get(b).unwrap();
        let c_node = rt.get(c).unwrap();
        assert_eq!(
            c_node.invalidations,
            Invalidations::from_iter([
                Invalidation {
                    source: a_new.revision_pointer(),
                    pointer: b_node.revision_pointer(),
                    reason: InvalidationReason::DependencyInvalidated,
                },
                Invalidation {
                    source: a_new.revision_pointer(),
                    pointer: a_new.revision_pointer(),
                    reason: InvalidationReason::NewVersion,
                },
            ])
        );
    }

    #[tokio::test]
    async fn test_concurrent_updates() {
        let rt = Arc::new(Runtime::new());
        let id = QueryId(1);

        let handles: Vec<_> = (0..100)
            .map(|_| {
                let rt = rt.clone();
                tokio::spawn(async move {
                    let _ = rt.register(id, vec![]);
                })
            })
            .collect();

        for handle in handles {
            handle.await.unwrap();
        }

        let node = rt.get(id).unwrap();
        assert!(node.version.0 == 99); // Changed from exact equality to >= since we might have retries
    }

    // Test garbage collection of unused nodes
    #[test]
    fn test_remove_if_unused() {
        let rt = Runtime::new();
        let a = QueryId(1);
        let b = QueryId(2);

        // a with no dependencies
        let _ = rt.register(a, vec![]);
        assert!(rt.remove_if_unused(a).is_some());

        // b depends on a
        let QueryRegistrationResult { node, .. } = rt.register(a, vec![]);
        let _ = rt.register(b, vec![node.pointer()]);
        assert!(rt.remove_if_unused(a).is_none());
    }

    // Test dependency version updates
    #[test]
    fn test_dependency_version_update() {
        let rt = Runtime::new();
        let a = QueryId(1);
        let b = QueryId(2);

        // Initial version
        let a1 = rt.register(a, vec![]).node;
        let _b1 = rt.register(b, vec![a1.pointer()]).node;

        // Update a
        let a2 = rt.register(a, vec![]).node;

        // Update b's dependencies
        let b2 = rt.update_dependencies(b, vec![a2.pointer()]).node;
        assert_eq!(
            b2.dependencies.iter().next().unwrap().version.0,
            a2.version.0
        );
    }

    // Test complex dependency graph (diamond shape)
    #[test]
    fn test_diamond_dependency() {
        let rt = Runtime::new();
        let a = QueryId(1);
        let b = QueryId(2);
        let c = QueryId(3);
        let d = QueryId(4);

        let a_result = rt.register(a, vec![]);
        let b_result = rt.register(b, vec![a_result.node.pointer()]);
        let c_result = rt.register(c, vec![a_result.node.pointer()]);
        let _ = rt.register(d, vec![b_result.node.pointer(), c_result.node.pointer()]);

        // Update a should invalidate all
        let a_new = rt.register(a, vec![]).node;
        let b_node = rt.get(b).unwrap();
        let c_node = rt.get(c).unwrap();
        assert!(b_node.is_invalidated());
        assert!(c_node.is_invalidated());
        assert_eq!(
            rt.get(d).unwrap().invalidations,
            Invalidations::from_iter([
                Invalidation {
                    source: a_new.revision_pointer(),
                    pointer: b_node.revision_pointer(),
                    reason: InvalidationReason::DependencyInvalidated,
                },
                Invalidation {
                    source: a_new.revision_pointer(),
                    pointer: c_node.revision_pointer(),
                    reason: InvalidationReason::DependencyInvalidated,
                },
            ])
        );
    }

    // Test un-invalidation process
    #[test]
    fn test_uninvalidation() {
        let rt = Runtime::new();
        let a = QueryId(1);
        let b = QueryId(2);

        // Create dependency
        let a_node = rt.register(a, vec![]).node;
        let _b_node = rt.register(b, vec![a_node.pointer()]).node;

        // Invalidate b by updating a and get the new revision pointer
        let a_new = rt.register(a, vec![]).node;
        let b_node = rt.get(b).unwrap();
        assert!(b_node.is_invalidated());

        // Remove the invalidator from b's invalidations using the source pointer
        rt.remove_invalidator(b_node.pointer(), a_new.revision_pointer());
        assert!(!rt.get(b).unwrap().is_invalidated());
    }

    #[test]
    fn test_uninvalidation_reinvalidates_since_invalidator_has_new_version() {
        let rt = Runtime::new();
        let a = QueryId(1);
        let b = QueryId(2);

        let a_result = rt.register(a, vec![]);
        let _b_result = rt.register(b, vec![a_result.node.pointer()]);

        let a_new1 = rt.register(a, vec![]).node;
        let a_new2 = rt.register(a, vec![]).node;

        let b_node = rt.get(b).unwrap();
        assert!(b_node.is_invalidated());
        assert_eq!(
            b_node.invalidations,
            Invalidations::from_iter([Invalidation::new_source(
                a_new1.revision_pointer(),
                InvalidationReason::NewVersion,
            )])
        );
        rt.remove_invalidator(b_node.pointer(), a_new1.revision_pointer());
        assert!(rt.get(b).unwrap().is_invalidated());
        assert_eq!(
            rt.get(b).unwrap().invalidations,
            Invalidations::from_iter([Invalidation::new_source(
                a_new2.revision_pointer(),
                InvalidationReason::NewVersion,
            )])
        );
    }

    // Test concurrent invalidations and updates
    #[tokio::test]
    async fn test_concurrent_invalidations() {
        let rt = Arc::new(Runtime::new());
        let a = QueryId(1);
        let b = QueryId(2);

        let a_node = rt.register(a, vec![]).node;
        let _ = rt.register(b, vec![a_node.pointer()]);
        let a_new = rt.register(a, vec![]).node;

        let handles: Vec<_> = (0..50)
            .map(|_| {
                let rt = rt.clone();
                tokio::spawn(async move {
                    let _ = rt.register(a, vec![]);
                })
            })
            .collect();

        for handle in handles {
            handle.await.unwrap();
        }

        let b_node = rt.get(b).unwrap();
        assert!(b_node.is_invalidated());
        // a invalidated 50 times, but only the first one is registered. because new version does not have a dependent of b. It's fine because removing this invalidator makes b invalidated again because a is not the latest.
        assert_eq!(
            b_node.invalidations,
            Invalidations::from_iter([Invalidation {
                source: a_new.revision_pointer(),
                pointer: a_new.revision_pointer(),
                reason: InvalidationReason::NewVersion,
            }])
        );
    }

    // Test node removal with dependents
    #[test]
    fn test_removal_with_dependents() {
        let rt = Runtime::new();
        let a = QueryId(1);
        let b = QueryId(2);

        let a_result = rt.register(a, vec![]);
        let _b_result = rt.register(b, vec![a_result.node.pointer()]);

        let removal = rt.remove(a);
        assert!(removal.removed.is_some());
        assert_eq!(
            rt.get(b).unwrap().invalidations,
            Invalidations::from_iter([Invalidation {
                source: a_result.node.revision_pointer(),
                pointer: a_result.node.revision_pointer(),
                reason: InvalidationReason::Removed,
            }])
        );
    }
}
