use std::sync::{
    atomic::{AtomicU64, Ordering},
    Arc,
};

use papaya::{Compute, HashMap, Operation};

#[derive(Debug, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Runtime {
    nodes: HashMap<QueryId, Node>,
    next_version: AtomicU64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]

pub struct QueryId(pub u64);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Version(pub u64);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Pointer {
    pub query_id: QueryId,
    pub version: Version,
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Node {
    pub id: QueryId,
    pub version: Version,
    pub dependencies: Dependencies,
    pub dependents: Vec<Pointer>,
    pub invalidated: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Dependencies(pub Arc<Vec<Pointer>>);

impl Dependencies {
    pub fn search(&self, query_id: QueryId) -> Option<Pointer> {
        self.0.iter().find(|p| p.query_id == query_id).cloned()
    }
}

pub struct Dependency {
    pub query_id: QueryId,
    pub version: Version,
}

pub struct RegisterNewVersionResult {
    pub version: Version,
    pub invalidated: Vec<Pointer>,
}

impl Runtime {
    pub fn new() -> Self {
        Default::default()
    }

    /// Get the node for a query.
    pub fn get(&self, query_id: QueryId) -> Option<Node> {
        self.nodes.pin().get(&query_id).cloned()
    }

    /// Remove a node from the runtime. If the node is returned and has dependents, you should update them.
    pub fn remove(&self, query_id: QueryId) -> Option<Node> {
        self.nodes.pin().remove(&query_id).cloned()
    }

    /// Register a new version for a query. If the previous version is returned, you should update all dependents.
    pub fn register_new_version(
        &self,
        query_id: QueryId,
        dependencies: Vec<Pointer>,
        preknown_dependents: Vec<Pointer>,
    ) -> RegisterNewVersionResult {
        let version = Version(self.next_version.fetch_add(1, Ordering::Relaxed));
        let mut invalidated = false;
        for dependency in dependencies.iter().cloned() {
            enum AbortReason {
                NotFound,
                AlreadyInvalidated,
                AlreadyUpdated,
            };
            let pinned = self.nodes.pin();
            let result = pinned.compute(dependency.query_id, |node| {
                let Some((_, node)) = node else {
                    return Operation::Abort(AbortReason::NotFound);
                };
                if node.version != dependency.version {
                    assert!(node.version > dependency.version);
                    return Operation::Abort(AbortReason::AlreadyUpdated);
                }
                if node.invalidated {
                    return Operation::Abort(AbortReason::AlreadyInvalidated);
                }
                let mut node = node.clone();
                if let Some(existing) = node.dependents.iter_mut().find(|p| p.query_id == query_id)
                {
                    existing.version = dependency.version;
                } else {
                    node.dependents.push(Pointer {
                        query_id,
                        version: dependency.version,
                    });
                }
                Operation::Insert(node)
            });
            match result {
                Compute::Inserted(_, _) => {}
                Compute::Updated { .. } => {}
                Compute::Removed(_, _) => {}
                Compute::Aborted(AbortReason::NotFound) => {}
                Compute::Aborted(AbortReason::AlreadyInvalidated)
                | Compute::Aborted(AbortReason::AlreadyUpdated) => {
                    invalidated = true;
                }
            }
        }
        let node = Node {
            id: query_id,
            version,
            dependencies: Dependencies(Arc::new(dependencies)),
            dependents: preknown_dependents,
            invalidated,
        };
        let Some(previous) = self.nodes.pin().insert(query_id, node).cloned() else {
            return RegisterNewVersionResult {
                version,
                invalidated: vec![],
            };
        };
        let invalidated = previous.dependents;
        // TODO: this should be recursive??
        for dependent in invalidated.iter().cloned() {
            self.nodes.pin().compute(dependent.query_id, |node| {
                let Some((_, node)) = node else {
                    return Operation::Abort(());
                };
                // If the node is already invalidated, we don't need to do anything
                if node.invalidated {
                    return Operation::Abort(());
                }
                let Some(depended) = node.dependencies.search(query_id) else {
                    return Operation::Abort(());
                };
                // If the depended version is the same as the previous version, or
                // if it depends on older version of the previous version,
                // we need to invalidate the node
                if previous.version >= depended.version {
                    let mut node = node.clone();
                    node.invalidated = true;
                    Operation::Insert(node)
                } else {
                    Operation::Abort(())
                }
            });
        }
        RegisterNewVersionResult {
            version,
            invalidated,
        }
    }
}
