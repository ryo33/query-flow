//! Node and dependency types for the Whale incremental computation system.
//!
//! This module defines the core data structures for representing nodes
//! in the dependency graph, following the Lean4 formal specification.

use std::sync::Arc;

use crate::revision::{Durability, RevisionCounter};

/// Dependency record: tracks which query we depend on and
/// what its `changed_at` was when we observed it.
///
/// This captures the state of a dependency at the time the observation was made,
/// allowing us to detect whether the dependency has changed since then.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Dep<K> {
    /// The query ID of the dependency.
    pub query_id: K,
    /// The `changed_at` value of the dependency when we observed it.
    pub observed_changed_at: RevisionCounter,
}

/// Node in the dependency graph.
///
/// Each node represents a query with its current state, including:
/// - When it was last verified and changed
/// - Its durability level
/// - Its position in the dependency graph (level, dependencies, dependents)
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Node<K, T, const N: usize> {
    /// Unique identifier for this query.
    pub id: K,
    /// User-provided data for this node. Should be cheap to clone.
    pub data: T,
    /// Durability level (0 = volatile, N-1 = stable).
    ///
    /// A node's durability determines which revision counter is used
    /// to track its validity. Lower durability means more frequent changes.
    pub durability: Durability<N>,
    /// Last revision at which this node was verified.
    ///
    /// A node is considered valid if `verified_at >= revision[durability]`,
    /// meaning it was verified after the last change at its durability level.
    pub verified_at: RevisionCounter,
    /// Last revision at which this node's value changed.
    ///
    /// Dependents compare this against their `observed_changed_at` to
    /// determine if they need to recompute.
    pub changed_at: RevisionCounter,
    /// Topological level in the dependency graph.
    ///
    /// Enforces DAG structure: `level > all(deps.level)`.
    /// This prevents cycles and enables ordered recomputation.
    pub level: u32,
    /// Who this node depends on.
    pub dependencies: Dependencies<K>,
    /// Who depends on this node (reverse edges).
    pub dependents: Dependents<K>,
}

impl<K, T, const N: usize> Node<K, T, N>
where
    K: Clone + PartialEq + Eq + std::hash::Hash,
    T: Clone,
{
    /// Create a new node with the given parameters.
    pub fn new(
        id: K,
        data: T,
        durability: Durability<N>,
        verified_at: RevisionCounter,
        changed_at: RevisionCounter,
        level: u32,
        dependencies: Dependencies<K>,
    ) -> Self {
        Self {
            id,
            data,
            durability,
            verified_at,
            changed_at,
            level,
            dependencies,
            dependents: Dependents::default(),
        }
    }
}

/// Dependencies is a list of dependency records for the queries that this query depends on.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Dependencies<K>(Arc<Vec<Dep<K>>>);

impl<K> Dependencies<K> {
    /// Create new dependencies from a list of dependency records.
    pub fn new(deps: Vec<Dep<K>>) -> Self {
        Dependencies(Arc::new(deps))
    }

    /// Returns true if there are no dependencies.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Returns the number of dependencies.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Iterate over the dependencies.
    pub fn iter(&self) -> impl Iterator<Item = &Dep<K>> + '_ {
        self.0.iter()
    }
}

impl<K> FromIterator<Dep<K>> for Dependencies<K> {
    fn from_iter<I: IntoIterator<Item = Dep<K>>>(iter: I) -> Self {
        Dependencies(Arc::new(iter.into_iter().collect()))
    }
}

/// Dependents is a list of query IDs that depend on this query.
///
/// This maintains reverse edges for efficient invalidation propagation
/// and bidirectional graph consistency.
#[derive(Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Dependents<K>(Arc<Vec<K>>);

impl<K> Default for Dependents<K> {
    fn default() -> Self {
        Dependents(Arc::new(Vec::new()))
    }
}

impl<K> Clone for Dependents<K> {
    fn clone(&self) -> Self {
        Dependents(self.0.clone())
    }
}

impl<K> Dependents<K>
where
    K: Clone + PartialEq,
{
    /// Create new dependents from a list of query IDs.
    pub fn new(deps: Vec<K>) -> Self {
        Dependents(Arc::new(deps))
    }

    /// Returns a new dependents list with the query ID added.
    ///
    /// If the query ID already exists, it is not duplicated.
    #[must_use]
    pub fn added(&self, qid: K) -> Self {
        if self.0.contains(&qid) {
            return self.clone();
        }
        let mut dependents = Vec::clone(&self.0);
        dependents.push(qid);
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
    pub fn iter(&self) -> impl Iterator<Item = &K> + '_ {
        self.0.iter()
    }

    /// Check if the given query ID is in the dependents list.
    pub fn contains(&self, qid: &K) -> bool {
        self.0.contains(qid)
    }
}

impl<K> FromIterator<K> for Dependents<K> {
    fn from_iter<I: IntoIterator<Item = K>>(iter: I) -> Self {
        Dependents(Arc::new(iter.into_iter().collect()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dep_creation() {
        let dep: Dep<&str> = Dep {
            query_id: "test",
            observed_changed_at: 42,
        };
        assert_eq!(dep.query_id, "test");
        assert_eq!(dep.observed_changed_at, 42);
    }

    #[test]
    fn test_dependencies() {
        let deps: Dependencies<&str> = Dependencies::new(vec![
            Dep {
                query_id: "a",
                observed_changed_at: 1,
            },
            Dep {
                query_id: "b",
                observed_changed_at: 2,
            },
        ]);

        assert_eq!(deps.len(), 2);
        assert!(!deps.is_empty());

        let ids: Vec<_> = deps.iter().map(|d| d.query_id).collect();
        assert_eq!(ids, vec!["a", "b"]);
    }

    #[test]
    fn test_dependents_added() {
        let deps: Dependents<&str> = Dependents::default();
        assert!(deps.is_empty());

        let deps = deps.added("a");
        assert_eq!(deps.len(), 1);
        assert!(deps.contains(&"a"));

        // Adding same id should not duplicate
        let deps = deps.added("a");
        assert_eq!(deps.len(), 1);

        let deps = deps.added("b");
        assert_eq!(deps.len(), 2);
    }

    #[test]
    fn test_node_creation() {
        let node: Node<&str, (), 3> = Node::new(
            "test",
            (),
            Durability::volatile(),
            1,
            1,
            1,
            Dependencies::default(),
        );

        assert_eq!(node.id, "test");
        assert_eq!(node.durability, Durability::volatile());
        assert_eq!(node.verified_at, 1);
        assert_eq!(node.changed_at, 1);
        assert_eq!(node.level, 1);
        assert!(node.dependencies.is_empty());
        assert!(node.dependents.is_empty());
    }
}
