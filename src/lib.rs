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
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Pointer {
    /// QueryId is a unique identifier for a query.
    pub query_id: QueryId,
    /// Version is a monotonically increasing number when a result of a query is changed. Note that this does not increase one by one.
    pub version: Version,
}

/// A precise pointer is a pair of `Pointer` and `InvalidationRevision`.
///
/// This is used to identify a specific precise version of a query that is incremented when it is invalidated.
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
    pub fn depends_on(&self, update: Self) -> bool {
        if self.query_id != update.query_id {
            return false;
        }
        // depends on updated version or more old version
        self.version.0 <= update.version.0
    }
}

/// InvalidationRevision is a query-local monotonically increasing number.
///
/// This is used to identify a specific precise version of a query that is incremented when it is invalidated.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct InvalidationRevision(pub u64);

/// Node is a data structure that represents a state of a query, and it is managed by the runtime.
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
    /// Invalidations is a list of precise pointers that invalidate this query.
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

    /// Get a precise pointer to this query.
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
            .any(|(i, _)| i.can_restore(&invalidator))
        {
            let mut node = self.clone();
            node.invalidations = node.invalidations.remove_uninvalidated(invalidator);
            Some(node)
        } else {
            None
        }
    }

    /// Extend invalidations with a list of precise pointers.
    pub fn add_invalidations(&mut self, with: Vec<(RevisionPointer, InvalidationReason)>) {
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
            .filter(|(i, _reason)| i == &previous)
        {
            *invalidation = (new, InvalidationReason::Invalidated);
        }
        Self {
            dependencies: Dependencies(Arc::new(dependencies)),
            invalidations: Invalidations(Arc::new(invalidations)),
            ..self.clone()
        }
    }
}

/// Dependencies is a list of pointers to the queries that this query depends on.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Dependencies(Arc<Vec<Pointer>>);

impl Dependencies {
    /// Returns true if this query should be invalidated if the other query is updated.
    pub fn should_be_invalidated_by(&self, update: Pointer) -> bool {
        self.0.iter().any(|p| p.depends_on(update))
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
}

/// Invalidations is a list of precise pointers that cause this query to be invalidated.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Invalidations(Arc<Vec<(RevisionPointer, InvalidationReason)>>);

impl Invalidations {
    /// Returns true if this query is not invalidated.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Push a precise pointer to the invalidations.
    #[must_use]
    pub fn pushed(&self, pointer: RevisionPointer, reason: InvalidationReason) -> Self {
        let mut invalidations = Vec::clone(&self.0);
        invalidations.push((pointer, reason));
        Invalidations(Arc::new(invalidations))
    }

    /// Remove an invalidator from the invalidations.
    #[must_use]
    pub fn remove_uninvalidated(&self, pointer: RevisionPointer) -> Self {
        let mut invalidations = Vec::clone(&self.0);
        invalidations.retain(|(i, _)| !i.can_restore(&pointer));
        Invalidations(Arc::new(invalidations))
    }

    /// Iterate over the invalidations.
    pub fn iter(&self) -> impl Iterator<Item = (RevisionPointer, InvalidationReason)> + '_ {
        self.0.iter().cloned()
    }
}

/// QueryRegistrationResult is a result of registering a new version.
pub struct QueryRegistrationResult {
    /// Node is the new node after registering a new version.
    pub node: Node,
    /// Previous version of the node.
    pub old_node: Option<Node>,
    /// Invalidated is a list of pointers to the queries that are invalidated by the new version.
    pub invalidated: Vec<Pointer>,
}

/// QueryRemovalResult is a result of `Runtime::remove`.
pub struct QueryRemovalResult {
    /// Removed is the node that is removed.
    pub removed: Option<Node>,
    /// Invalidated is a list of pointers to the queries that are invalidated by the removal.
    pub invalidated: Vec<Pointer>,
}

/// InvalidatedReason is a reason why a query is invalidated.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum InvalidationReason {
    /// Invalidated is a reason why a query is invalidated by another query is invalidated.
    Invalidated,
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
        let mut invalidated = vec![];
        if let Some(removed) = &removed {
            for dependent in removed.dependents.0.iter().cloned() {
                let pinned = self.nodes.pin();
                let result = pinned.compute(dependent.query_id, |node| {
                    let Some((_, node)) = node else {
                        return Operation::Abort(());
                    };
                    node.dependents
                        .0
                        .iter()
                        .any(|p| p.depends_on(removed.pointer()));
                    let mut node = node.clone();
                    node.invalidations = node
                        .invalidations
                        .pushed(removed.revision_pointer(), InvalidationReason::Removed);
                    Operation::Insert(node)
                });
                match result {
                    Compute::Inserted(_, _) => {
                        unreachable!("should be aborted if it doesn't exist")
                    }
                    Compute::Updated {
                        old: _,
                        new: (_, node),
                    } => {
                        // at here new and old are the same pointer
                        invalidated.push(node.pointer());
                    }
                    Compute::Removed(_, _) => unreachable!(),
                    Compute::Aborted(_) => {}
                }
            }
        }
        QueryRemovalResult {
            removed,
            invalidated: vec![],
        }
    }

    /// Uninvalidate a specific precise pointer.
    pub fn uninvalidate(&self, precise_pointer: RevisionPointer) {
        let pinned = self.nodes.pin();
        enum AbortReason {
            NotFound,
            AlreadyUpdated,
            MoreInvalidated,
            AlreadyUninvalidated,
        }
        let result = pinned.compute(precise_pointer.pointer.query_id, |node| {
            let Some((_, node)) = node else {
                return Operation::Abort(AbortReason::NotFound);
            };
            if !node.is_invalidated() {
                return Operation::Abort(AbortReason::AlreadyUninvalidated);
            }
            if node.version != precise_pointer.pointer.version {
                return Operation::Abort(AbortReason::AlreadyUpdated);
            }
            if node.invalidation_revision.0 > precise_pointer.invalidation_revision.0 {
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
                for dependent in old.dependents.0.iter().cloned() {
                    self.remove_invalidator(dependent, precise_pointer);
                }
            }
            Compute::Removed(_, _) => unreachable!(),
            Compute::Aborted(_) => {}
        }
    }

    /// Remove an invalidator from a specific pointer.
    ///
    /// This function should never infinite loop while cyclic dependency, since if all possible invalidators are removed, the recursion will be aborted.
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
                    for dependent in new.dependents.0.iter().cloned() {
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
    ///
    /// This should not hang though called with a cyclic dependency, since if all nodes in the cycle are invalidated, the recursion will be aborted.
    #[must_use]
    pub fn invalidate(
        &self,
        node: Pointer,
        precise_pointer: RevisionPointer,
        reason: InvalidationReason,
    ) -> Vec<Pointer> {
        let mut invalidated = vec![];
        let pinned = self.nodes.pin();
        let result = pinned.compute(node.query_id, |node| {
            let Some((_, node)) = node else {
                return Operation::Abort(());
            };
            if node.pointer().depends_on(node.pointer()) {
                let mut node = node.clone();
                node.invalidations = node.invalidations.pushed(precise_pointer, reason);
                node.invalidation_revision.0 += 1;
                Operation::Insert(node)
            } else {
                Operation::Abort(())
            }
        });
        match result {
            Compute::Inserted(_, _) => unreachable!(),
            Compute::Updated {
                old: (_, old),
                new: (_, node),
            } => {
                // This if is important to avoid infinite recursion on cyclic dependency.
                if !old.is_invalidated() {
                    // recursively invalidate dependents
                    for dependents in node.dependents.0.iter().cloned() {
                        invalidated.extend(self.invalidate(
                            dependents,
                            node.revision_pointer(),
                            InvalidationReason::Invalidated,
                        ));
                    }
                }
            }
            Compute::Removed(_, _) => unreachable!(),
            Compute::Aborted(_) => {}
        }
        invalidated
    }

    /// Register a new version for a query. If the previous version is returned, you should update all dependents.
    ///
    /// This should not hang though called with a cyclic dependency, since if all nodes in the cycle are invalidated, the recursion will be aborted.
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

        let mut newly_invalidated = if new_node.is_invalidated() {
            vec![new_node.pointer()]
        } else {
            vec![]
        };

        if let Some(old_node) = &old_node {
            // Recursively invalidate and collect old dependents
            for dependent in old_node.dependents.0.iter().cloned() {
                newly_invalidated.extend(self.invalidate(
                    dependent,
                    old_node.revision_pointer(),
                    InvalidationReason::NewVersion,
                ));
            }
        }

        QueryRegistrationResult {
            node: new_node,
            old_node,
            invalidated: newly_invalidated,
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

        let mut invalidated = if new_node.is_invalidated() {
            vec![new_node.pointer()]
        } else {
            vec![]
        };

        if let Some(old_node) = &old_node {
            for dependent in old_node.dependents.0.iter().cloned() {
                self.update_dependency_version(
                    dependent,
                    old_node.revision_pointer(),
                    new_node.revision_pointer(),
                );
                if new_node.is_invalidated() {
                    invalidated.extend(self.invalidate(
                        dependent,
                        new_node.revision_pointer(),
                        InvalidationReason::Invalidated,
                    ));
                }
            }
        }
        QueryRegistrationResult {
            node: new_node,
            old_node,
            invalidated,
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

    /// Register a query as a dependents to each dependency, and find invalidations.
    #[must_use]
    fn update_dependency_graph(
        &self,
        pointer: Pointer,
        dependencies: Dependencies,
    ) -> Vec<(RevisionPointer, InvalidationReason)> {
        let mut invalidations = vec![];
        for dependency in dependencies.0.iter().cloned() {
            enum AbortReason {
                NotFound,
                AlreadyInvalidated(RevisionPointer),
                AlreadyUpdated(RevisionPointer),
            }
            let pinned = self.nodes.pin();
            let result = pinned.compute(dependency.query_id, |node| {
                let Some((_, node)) = node else {
                    return Operation::Abort(AbortReason::NotFound);
                };
                if node.version != dependency.version {
                    assert!(node.version.0 > dependency.version.0);
                    return Operation::Abort(AbortReason::AlreadyUpdated(node.revision_pointer()));
                }
                if node.is_invalidated() {
                    return Operation::Abort(AbortReason::AlreadyInvalidated(
                        node.revision_pointer(),
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
                Compute::Aborted(AbortReason::AlreadyInvalidated(invalidator)) => {
                    invalidations.push((invalidator, InvalidationReason::Invalidated));
                }
                Compute::Aborted(AbortReason::AlreadyUpdated(invalidator)) => {
                    invalidations.push((invalidator, InvalidationReason::NewVersion));
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
        invalidations: Vec<(RevisionPointer, InvalidationReason)>,
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
