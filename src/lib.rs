use std::sync::{
    atomic::{AtomicU64, Ordering},
    Arc,
};

use papaya::{Compute, HashMap, Operation};

#[derive(Debug, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Runtime {
    nodes: HashMap<QueryId, Node, ahash::RandomState>,
    next_version: AtomicU64,
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

pub struct QueryId(pub u64);

/// Version is a monotonically increasing number. This does not implement `PartialOrd` and `Ord` because it is not comparable across different queries.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Version(pub u64);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Pointer {
    pub query_id: QueryId,
    pub version: Version,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
// Important! This does not have `reason` because it is unknown at some point, and it is not needed for equality check.
pub struct PrecisePointer {
    pub pointer: Pointer,
    pub invalidation_version: InvalidationVersion,
}

impl PrecisePointer {
    /// Returns true if this pointer can be uninvalidated by the other pointer.
    pub fn can_be_uninvalidated(&self, other: &Self) -> bool {
        self.pointer == other.pointer && self.invalidation_version.0 <= other.invalidation_version.0
    }
}

impl Pointer {
    /// Returns true if this pointer should be invalidated if the other pointer is updated.
    pub fn should_be_invalidated_by(&self, update: Self) -> bool {
        if self.query_id != update.query_id {
            return false;
        }
        // depends on updated version or more old version
        self.version.0 <= update.version.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct InvalidationVersion(pub u64);

#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Node {
    pub id: QueryId,
    pub version: Version,
    pub invalidation_version: InvalidationVersion,
    pub dependencies: Dependencies,
    pub dependents: Dependents,
    pub invalidated_by: Vec<(PrecisePointer, InvalidatedReason)>,
}

impl Node {
    pub fn pointer(&self) -> Pointer {
        Pointer {
            query_id: self.id,
            version: self.version,
        }
    }

    pub fn presise_pointer(&self) -> PrecisePointer {
        PrecisePointer {
            pointer: self.pointer(),
            invalidation_version: self.invalidation_version,
        }
    }

    pub fn is_invalidated(&self) -> bool {
        !self.invalidated_by.is_empty()
    }

    pub fn remove_invalidator(&self, invalidator: PrecisePointer) -> Option<Self> {
        if self
            .invalidated_by
            .iter()
            .any(|(i, _)| i.can_be_uninvalidated(&invalidator))
        {
            let mut node = self.clone();
            node.invalidated_by
                .retain(|(i, _)| !i.can_be_uninvalidated(&invalidator));
            Some(node)
        } else {
            None
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Dependencies(pub Arc<Vec<Pointer>>);

impl Dependencies {
    pub fn should_be_invalidated_by(&self, update: Pointer) -> bool {
        self.0.iter().any(|p| p.should_be_invalidated_by(update))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Dependents(pub Arc<Vec<Pointer>>);

impl Dependents {
    #[must_use]
    pub(crate) fn updated(&self, pointer: Pointer) -> Self {
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

pub struct Dependency {
    pub query_id: QueryId,
    pub version: Version,
}

pub struct RegisterNewVersionResult {
    pub version: Version,
    pub node: Node,
    pub invalidated: Vec<Pointer>,
}

pub struct RemoveResult {
    pub removed: Option<Node>,
    pub invalidated: Vec<Pointer>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum InvalidatedReason {
    Invalidated,
    NewVersion,
    Removed,
}

impl Runtime {
    pub fn new() -> Self {
        Default::default()
    }

    /// Get the node for a query.
    ///
    /// This may read a not invalidated node while processing a new version of dependencies or removing a node.
    pub fn get(&self, query_id: QueryId) -> Option<Node> {
        self.nodes.pin().get(&query_id).cloned()
    }

    /// Remove a node from the runtime. If the node is returned and has dependents, you should update them.
    #[must_use]
    pub fn remove(&self, query_id: QueryId) -> RemoveResult {
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
                        .any(|p| p.should_be_invalidated_by(removed.pointer()));
                    let mut node = node.clone();
                    node.invalidated_by
                        .push((removed.presise_pointer(), InvalidatedReason::Removed));
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
        RemoveResult {
            removed,
            invalidated: vec![],
        }
    }

    pub fn uninvalidate(&self, precise_pointer: PrecisePointer) {
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
            if node.invalidation_version.0 > precise_pointer.invalidation_version.0 {
                return Operation::Abort(AbortReason::MoreInvalidated);
            }
            let mut node = node.clone();
            node.invalidated_by = vec![];
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

    pub fn remove_invalidator(&self, pointer: Pointer, invalidator: PrecisePointer) {
        let pinned = self.nodes.pin();
        let result = pinned.compute(pointer.query_id, |node| {
            let Some((_, node)) = node else {
                return Operation::Abort(());
            };
            if node.version != pointer.version {
                return Operation::Abort(());
            }
            if let Some(node) = node.remove_invalidator(invalidator) {
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
                        self.remove_invalidator(dependent, old.presise_pointer());
                    }
                }
            }
            Compute::Removed(_, _) => unreachable!(),
            Compute::Aborted(_) => {}
        }
    }

    pub fn detect_cycle(&self, query_id: QueryId) -> bool {
        let mut set = ahash::HashSet::default();
        self.detect_cycle_with_set(query_id, &mut set)
    }

    pub fn detect_cycle_with_set(
        &self,
        query_id: QueryId,
        set: &mut ahash::HashSet<QueryId>,
    ) -> bool {
        if set.contains(&query_id) {
            return true;
        }
        set.insert(query_id);
        for dependency in self.get(query_id).unwrap().dependencies.0.iter().cloned() {
            if self.detect_cycle_with_set(dependency.query_id, set) {
                return true;
            }
        }
        false
    }

    /// Free a query if it is not depended by any other queries. This is useful for garbage collection.
    pub fn free_if_not_depended(&self, query_id: QueryId) -> Option<Node> {
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

    /// Recursively invalidate a specific version of a query, and returns the pointers of the invalidated nodes including the query itself.
    ///
    /// This should not hang though called with a cyclic dependency, since if all nodes in the cycle are invalidated, the recursion will be aborted.
    #[must_use]
    pub fn invalidate(
        &self,
        node: Pointer,
        reason: (PrecisePointer, InvalidatedReason),
    ) -> Vec<Pointer> {
        let mut invalidated = vec![];
        let pinned = self.nodes.pin();
        let result = pinned.compute(node.query_id, |node| {
            let Some((_, node)) = node else {
                return Operation::Abort(());
            };
            if node.pointer().should_be_invalidated_by(node.pointer()) {
                let mut node = node.clone();
                node.invalidated_by.push(reason);
                // The node is invalidated.
                invalidated.push(node.pointer());
                node.invalidation_version.0 += 1;
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
                            (node.presise_pointer(), InvalidatedReason::Invalidated),
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
    pub fn register_new_version(
        &self,
        query_id: QueryId,
        dependencies: Vec<Pointer>,
        preknown_dependents: Vec<Pointer>,
    ) -> RegisterNewVersionResult {
        // Register the new version
        enum InsertAbortReason {
            AlreadyOld,
        }
        let pinned = self.nodes.pin();
        let dependencies = Dependencies(Arc::new(dependencies));
        let preknown_dependents = Dependents(Arc::new(preknown_dependents));
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
                dependents: preknown_dependents.clone(),
                invalidation_version: Default::default(),
                invalidated_by: Default::default(),
            })
        });

        let (mut new_node, old_node) = match result {
            Compute::Inserted(_key, new) => (new.clone(), None),
            Compute::Updated {
                old: (_, old),
                new: (_, new),
            } => (new.clone(), Some(old)),
            Compute::Removed(_, _) => unreachable!(),
            Compute::Aborted(InsertAbortReason::AlreadyOld) => unreachable!(
                "version is calculated within atomic computation, so latter version should be always newer"
            ),
        };

        // At this point, other threads may be read this version without invalidated state before checking if it is invalidated.

        // Register dependents
        // While registering dependents, other threads may be update or invalidate those dependencies, so we need to collect all invalidated dependencies.
        let mut invalidated_by = vec![];
        for dependency in dependencies.0.iter().cloned() {
            enum AbortReason {
                NotFound,
                AlreadyInvalidated(PrecisePointer),
                AlreadyUpdated(PrecisePointer),
            }
            let pinned = self.nodes.pin();
            let result = pinned.compute(dependency.query_id, |node| {
                let Some((_, node)) = node else {
                    return Operation::Abort(AbortReason::NotFound);
                };
                if node.version != dependency.version {
                    assert!(node.version.0 > dependency.version.0);
                    return Operation::Abort(AbortReason::AlreadyUpdated(node.presise_pointer()));
                }
                if node.is_invalidated() {
                    return Operation::Abort(AbortReason::AlreadyInvalidated(
                        node.presise_pointer(),
                    ));
                }
                let mut node = node.clone();
                node.dependents = node.dependents.updated(new_node.pointer());
                Operation::Insert(node)
            });
            match result {
                Compute::Inserted(_, _) => {}
                Compute::Updated { .. } => {}
                Compute::Removed(_, _) => {}
                Compute::Aborted(AbortReason::NotFound) => {}
                Compute::Aborted(AbortReason::AlreadyInvalidated(invalidator)) => {
                    invalidated_by.push((invalidator, InvalidatedReason::Invalidated));
                }
                Compute::Aborted(AbortReason::AlreadyUpdated(invalidator)) => {
                    invalidated_by.push((invalidator, InvalidatedReason::NewVersion));
                }
            }
        }

        if !invalidated_by.is_empty() {
            let pinned = self.nodes.pin();
            let result = pinned.compute(query_id, |node| {
                let Some((_, node)) = node else {
                    return Operation::Abort(());
                };
                if node.version != new_node.version {
                    return Operation::Abort(());
                }
                let mut node = node.clone();
                node.invalidated_by.extend(invalidated_by.clone());
                Operation::Insert(node)
            });
            match result {
                Compute::Inserted(_, _) => unreachable!(),
                Compute::Updated {
                    old: _,
                    new: (_, new),
                } => {
                    new_node = new.clone();
                }
                Compute::Removed(_, _) => unreachable!(),
                Compute::Aborted(_) => {}
            }
        }

        let Some(old_node) = old_node else {
            return RegisterNewVersionResult {
                version: new_node.version,
                node: new_node,
                invalidated: vec![],
            };
        };

        // Recursively invalidate and collect old dependents
        let mut invalidated = vec![];
        for dependent in old_node.dependents.0.iter().cloned() {
            invalidated.extend(self.invalidate(
                dependent,
                (old_node.presise_pointer(), InvalidatedReason::NewVersion),
            ));
        }

        RegisterNewVersionResult {
            version: new_node.version,
            node: new_node,
            invalidated,
        }
    }
}
