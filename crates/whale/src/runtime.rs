//! Runtime for the Whale incremental computation system.
//!
//! The Runtime manages the dependency graph and provides the core operations
//! for registering queries, checking validity, and handling early cutoff.

use std::sync::Arc;

use papaya::{Compute, HashMap, Operation};

use crate::{
    node::{Dep, Dependencies, Node},
    revision::{AtomicRevision, Durability, Revision, RevisionCounter},
};

/// Runtime manages the dependency graph and revision tracking.
///
/// This is cheap to clone - all data is behind `Arc`.
///
/// # Type Parameters
/// - `K`: Query identifier type
/// - `T`: User-provided metadata type
/// - `N`: Number of durability levels (const generic)
pub struct Runtime<K, T, const N: usize> {
    nodes: Arc<HashMap<K, Node<K, T, N>, ahash::RandomState>>,
    revision: Arc<AtomicRevision<N>>,
}

impl<K, T, const N: usize> Default for Runtime<K, T, N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K, T, const N: usize> Clone for Runtime<K, T, N> {
    fn clone(&self) -> Self {
        Self {
            nodes: self.nodes.clone(),
            revision: self.revision.clone(),
        }
    }
}

impl<K, T, const N: usize> Runtime<K, T, N> {
    /// Create a new runtime.
    pub fn new() -> Self {
        Self {
            nodes: Arc::new(HashMap::with_hasher(ahash::RandomState::new())),
            revision: Arc::new(AtomicRevision::new()),
        }
    }
}

/// Result of a registration operation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RegisterResult<const N: usize> {
    /// The new revision counter value.
    pub new_rev: RevisionCounter,
    /// The effective durability (may be lower than requested due to dependencies).
    pub effective_durability: Durability<N>,
    /// The topological level assigned to the node.
    pub level: u32,
}

impl<K, T, const N: usize> Runtime<K, T, N>
where
    K: Clone + PartialEq + Eq + std::hash::Hash + std::fmt::Debug,
    T: Clone,
{
    /// Get a node by query ID.
    pub fn get(&self, query_id: &K) -> Option<Node<K, T, N>> {
        self.nodes.pin().get(query_id).cloned()
    }

    /// Iterate over all query IDs.
    pub fn keys(&self) -> Vec<K> {
        self.nodes.pin().keys().cloned().collect()
    }

    /// Get current revision snapshot.
    pub fn current_revision(&self) -> Revision<N> {
        self.revision.snapshot()
    }

    /// Increment revision at durability level `d` and all lower levels (0..=d).
    ///
    /// Returns the new revision counter at level `d`.
    pub fn increment_revision(&self, d: Durability<N>) -> RevisionCounter {
        self.revision.increment(d)
    }

    /// Check if a node is valid at a given revision.
    ///
    /// A node is valid if:
    /// 1. Its `verified_at >= revision[node.durability]`, OR
    /// 2. All dependencies have not changed since we last observed them
    ///    (`dep_node.changed_at <= dep.observed_changed_at`)
    pub fn is_valid_at(&self, qid: &K, at_rev: &Revision<N>) -> bool {
        let Some(node) = self.get(qid) else {
            return false;
        };

        let d = node.durability;

        // Check if already verified at this revision
        if node.verified_at >= at_rev.get(d) {
            return true;
        }

        // Check each dependency
        let deps_valid = node.dependencies.iter().all(|dep| {
            match self.get(&dep.query_id) {
                None => false, // dependency removed
                Some(dep_node) => {
                    // Using <= (not <): equal means "no change since observation"
                    dep_node.changed_at <= dep.observed_changed_at
                }
            }
        });
        deps_valid
    }

    /// Convenience: check validity at current revision.
    pub fn is_valid(&self, qid: &K) -> bool {
        self.is_valid_at(qid, &self.current_revision())
    }

    /// Mark a node as verified at given revision (idempotent update).
    ///
    /// Uses `max` to ensure monotonicity - `verified_at` only increases.
    pub fn mark_verified(&self, qid: &K, at_rev: &Revision<N>) {
        let pinned = self.nodes.pin();
        let _ = pinned.compute(qid.clone(), |node| {
            let Some((_, node)) = node else {
                return Operation::Abort(());
            };

            let d = node.durability;
            let new_verified_at = node.verified_at.max(at_rev.get(d));

            if new_verified_at == node.verified_at {
                return Operation::Abort(()); // No change needed
            }

            let mut new_node = node.clone();
            new_node.verified_at = new_verified_at;
            Operation::Insert(new_node)
        });
    }

    /// Build dependency records by capturing current `changed_at` values.
    ///
    /// Returns `Err` with the list of missing query IDs if any dependency doesn't exist.
    fn build_dep_records(&self, dep_ids: &[K]) -> Result<Vec<Dep<K>>, Vec<K>> {
        let mut deps = Vec::with_capacity(dep_ids.len());
        let mut missing = Vec::new();

        for dep_id in dep_ids {
            match self.get(dep_id) {
                Some(dep_node) => {
                    deps.push(Dep {
                        query_id: dep_id.clone(),
                        observed_changed_at: dep_node.changed_at,
                    });
                }
                None => {
                    missing.push(dep_id.clone());
                }
            }
        }

        if missing.is_empty() {
            Ok(deps)
        } else {
            Err(missing)
        }
    }

    /// Calculate effective durability (minimum of requested and all dependencies).
    ///
    /// Enforces the durability invariant: a node's durability must not exceed
    /// the minimum durability of its dependencies.
    fn calculate_effective_durability(
        &self,
        requested: Durability<N>,
        deps: &[Dep<K>],
    ) -> Durability<N> {
        let min_dep = deps
            .iter()
            .filter_map(|dep| self.get(&dep.query_id))
            .map(|n| n.durability.value())
            .min()
            .unwrap_or(N - 1);

        let effective = requested.value().min(min_dep);
        Durability::new(effective).unwrap_or(Durability::volatile())
    }

    /// Calculate topological level from dependencies.
    ///
    /// Enforces the level invariant: `node.level > all(deps.level)`.
    fn calculate_level(&self, deps: &[Dep<K>]) -> u32 {
        let max_dep_level = deps
            .iter()
            .filter_map(|dep| self.get(&dep.query_id))
            .map(|n| n.level)
            .max()
            .unwrap_or(0);

        max_dep_level + 1
    }

    /// Update reverse edges: add `qid` to the dependents list of all its dependencies.
    ///
    /// This maintains bidirectional consistency of the graph structure.
    fn update_graph_edges(&self, qid: &K, deps: &[Dep<K>]) {
        let pinned = self.nodes.pin();
        for dep in deps {
            let _ = pinned.compute(dep.query_id.clone(), |node| {
                let Some((_, node)) = node else {
                    return Operation::Abort(());
                };

                if node.dependents.contains(qid) {
                    return Operation::Abort(()); // Already added
                }

                let mut new_node = node.clone();
                new_node.dependents = node.dependents.added(qid.clone());
                Operation::Insert(new_node)
            });
        }
    }

    /// Remove `qid` from the dependents list of old dependencies that are no longer in new deps.
    ///
    /// This cleans up stale reverse edges when a node's dependencies change.
    fn cleanup_stale_edges(&self, qid: &K, old_deps: &Dependencies<K>, new_dep_ids: &[K]) {
        let new_set: ahash::HashSet<&K> = new_dep_ids.iter().collect();
        let pinned = self.nodes.pin();

        for old_dep in old_deps.iter() {
            if !new_set.contains(&old_dep.query_id) {
                // This dependency was removed, clean up the reverse edge
                let _ = pinned.compute(old_dep.query_id.clone(), |node| {
                    let Some((_, node)) = node else {
                        return Operation::Abort(());
                    };

                    if !node.dependents.contains(qid) {
                        return Operation::Abort(()); // Already removed
                    }

                    let mut new_node = node.clone();
                    new_node.dependents = node.dependents.removed(qid);
                    Operation::Insert(new_node)
                });
            }
        }
    }

    /// Register a new node or update an existing one.
    ///
    /// This:
    /// 1. Builds dependency records with current `changed_at` snapshots
    /// 2. Calculates effective durability (`min(requested, deps.durability)`)
    /// 3. Calculates topological level (`max(deps.level) + 1`)
    /// 4. Increments revision at the effective durability level
    /// 5. Creates node with `verified_at = changed_at = new_rev`
    /// 6. Updates reverse edges (dependents lists)
    ///
    /// Returns `Err` with missing dependency IDs if any dependency doesn't exist.
    pub fn register(
        &self,
        qid: K,
        data: T,
        requested_durability: Durability<N>,
        dep_ids: Vec<K>,
    ) -> Result<RegisterResult<N>, Vec<K>> {
        // Build dependency records with current changed_at snapshots
        let dep_records = self.build_dep_records(&dep_ids)?;

        // Calculate effective durability (min of requested and all deps)
        let effective_dur = self.calculate_effective_durability(requested_durability, &dep_records);

        // Calculate topological level
        let new_level = self.calculate_level(&dep_records);

        // Increment revision
        let new_rev = self.increment_revision(effective_dur);

        // Get old node state for edge cleanup
        let old_node = self.get(&qid);
        let old_dependents = old_node
            .as_ref()
            .map(|n| n.dependents.clone())
            .unwrap_or_default();

        // Create new node
        let new_node = Node {
            id: qid.clone(),
            data,
            durability: effective_dur,
            verified_at: new_rev,
            changed_at: new_rev,
            level: new_level,
            dependencies: Dependencies::new(dep_records.clone()),
            dependents: old_dependents,
        };

        // Insert node
        self.nodes.pin().insert(qid.clone(), new_node);

        // Clean up stale edges from old dependencies
        if let Some(old) = old_node {
            self.cleanup_stale_edges(&qid, &old.dependencies, &dep_ids);
        }

        // Update reverse edges
        self.update_graph_edges(&qid, &dep_records);

        Ok(RegisterResult {
            new_rev,
            effective_durability: effective_dur,
            level: new_level,
        })
    }

    /// Confirm that a node's value has not changed after recomputation (early cutoff).
    ///
    /// This is the key optimization for incremental computation:
    /// - Updates `verified_at` to current revision
    /// - **Does NOT update `changed_at`** - this is the essence of early cutoff!
    /// - Dependents who observed the old `changed_at` will still see it,
    ///   so they remain valid with respect to this dependency
    /// - Recalculates durability and level based on new dependencies
    ///
    /// Returns `Err` with missing dependency IDs if any dependency doesn't exist.
    pub fn confirm_unchanged(&self, qid: &K, new_dep_ids: Vec<K>) -> Result<(), Vec<K>> {
        let Some(node) = self.get(qid) else {
            return Ok(());
        };

        let new_deps = self.build_dep_records(&new_dep_ids)?;

        // Recalculate effective durability based on new dependencies
        let effective_dur = self.calculate_effective_durability(node.durability, &new_deps);
        let new_level = self.calculate_level(&new_deps);
        let current_rev = self.revision.get(effective_dur);

        // Update node: verified_at changes, changed_at stays the same!
        let new_node = Node {
            id: node.id.clone(),
            data: node.data.clone(),
            durability: effective_dur,
            verified_at: current_rev,
            changed_at: node.changed_at, // Key: unchanged!
            level: new_level,
            dependencies: Dependencies::new(new_deps.clone()),
            dependents: node.dependents.clone(),
        };

        self.nodes.pin().insert(qid.clone(), new_node);

        // Clean up stale edges and add new ones
        self.cleanup_stale_edges(qid, &node.dependencies, &new_dep_ids);
        self.update_graph_edges(qid, &new_deps);

        Ok(())
    }

    /// Confirm that a node's value has changed after recomputation.
    ///
    /// This:
    /// - Recalculates durability and level based on new dependencies
    /// - Increments revision at the effective durability level
    /// - Updates both `verified_at` and `changed_at` to the new revision
    /// - Dependents will see the increased `changed_at` and know they need to recheck
    ///
    /// Returns the new revision counter, or `Err` with missing dependency IDs.
    pub fn confirm_changed(&self, qid: &K, new_dep_ids: Vec<K>) -> Result<RevisionCounter, Vec<K>> {
        let Some(node) = self.get(qid) else {
            return Ok(0);
        };

        let new_deps = self.build_dep_records(&new_dep_ids)?;

        // Recalculate effective durability and level based on new dependencies
        let effective_dur = self.calculate_effective_durability(node.durability, &new_deps);
        let new_level = self.calculate_level(&new_deps);

        // Increment revision at the effective durability level
        let new_rev = self.increment_revision(effective_dur);

        let new_node = Node {
            id: node.id.clone(),
            data: node.data.clone(),
            durability: effective_dur,
            verified_at: new_rev,
            changed_at: new_rev, // Both updated!
            level: new_level,
            dependencies: Dependencies::new(new_deps.clone()),
            dependents: node.dependents.clone(),
        };

        self.nodes.pin().insert(qid.clone(), new_node);

        // Clean up stale edges and add new ones
        self.cleanup_stale_edges(qid, &node.dependencies, &new_dep_ids);
        self.update_graph_edges(qid, &new_deps);

        Ok(new_rev)
    }

    /// Remove a node from the runtime.
    ///
    /// Returns the removed node if it existed.
    pub fn remove(&self, query_id: &K) -> Option<Node<K, T, N>> {
        self.nodes.pin().remove(query_id).cloned()
    }

    /// Remove a node if it has no dependents.
    ///
    /// Useful for garbage collection.
    pub fn remove_if_unused(&self, query_id: K) -> Option<Node<K, T, N>> {
        let pinned = self.nodes.pin();
        let result = pinned.compute(query_id, |node| {
            let Some((_, node)) = node else {
                return Operation::Abort(());
            };
            if node.dependents.is_empty() {
                Operation::Remove
            } else {
                Operation::Abort(())
            }
        });
        match result {
            Compute::Removed(_, node) => Some(node.clone()),
            _ => None,
        }
    }

    /// Detect a cycle in the dependency graph starting from the given query.
    ///
    /// Uses iterative DFS to avoid stack overflow on deep graphs.
    pub fn has_cycle(&self, query_id: K) -> bool {
        let mut visited = ahash::HashSet::default();
        let mut in_stack = ahash::HashSet::default();
        let mut stack = vec![(query_id, false)]; // (node, is_backtracking)

        while let Some((qid, backtracking)) = stack.pop() {
            if backtracking {
                in_stack.remove(&qid);
                continue;
            }

            if in_stack.contains(&qid) {
                return true; // Cycle detected
            }

            if visited.contains(&qid) {
                continue; // Already fully processed
            }

            visited.insert(qid.clone());
            in_stack.insert(qid.clone());

            // Push backtrack marker
            stack.push((qid.clone(), true));

            // Push dependencies
            if let Some(node) = self.get(&qid) {
                for dep in node.dependencies.iter() {
                    stack.push((dep.query_id.clone(), false));
                }
            }
        }

        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    type TestRuntime = Runtime<&'static str, (), 3>;

    #[test]
    fn test_basic_registration() {
        let rt: TestRuntime = Runtime::new();

        let result = rt
            .register("a", (), Durability::volatile(), vec![])
            .unwrap();
        assert_eq!(result.new_rev, 1);
        assert_eq!(result.effective_durability, Durability::volatile());
        assert_eq!(result.level, 1);

        let node = rt.get(&"a").unwrap();
        assert_eq!(node.id, "a");
        assert_eq!(node.verified_at, 1);
        assert_eq!(node.changed_at, 1);
    }

    #[test]
    fn test_dependency_tracking() {
        let rt: TestRuntime = Runtime::new();

        // Register a
        rt.register("a", (), Durability::volatile(), vec![])
            .unwrap();

        // Register b depending on a
        let b_result = rt
            .register("b", (), Durability::volatile(), vec!["a"])
            .unwrap();

        // b should have level 2 (a is level 1)
        assert_eq!(b_result.level, 2);

        // a should have b in its dependents
        let a_node = rt.get(&"a").unwrap();
        assert!(a_node.dependents.contains(&"b"));

        // b should have a in its dependencies
        let b_node = rt.get(&"b").unwrap();
        assert_eq!(b_node.dependencies.len(), 1);
        assert_eq!(b_node.dependencies.iter().next().unwrap().query_id, "a");
    }

    #[test]
    fn test_is_valid_at_verified() {
        let rt: TestRuntime = Runtime::new();

        rt.register("a", (), Durability::volatile(), vec![])
            .unwrap();

        // Node should be valid at current revision
        let rev = rt.current_revision();
        assert!(rt.is_valid_at(&"a", &rev));
    }

    #[test]
    fn test_is_valid_at_deps_unchanged() {
        let rt: TestRuntime = Runtime::new();

        rt.register("a", (), Durability::volatile(), vec![])
            .unwrap();
        rt.register("b", (), Durability::volatile(), vec!["a"])
            .unwrap();

        // Both should be valid
        assert!(rt.is_valid(&"a"));
        assert!(rt.is_valid(&"b"));
    }

    #[test]
    fn test_is_valid_at_dep_changed() {
        let rt: TestRuntime = Runtime::new();

        rt.register("a", (), Durability::volatile(), vec![])
            .unwrap();
        rt.register("b", (), Durability::volatile(), vec!["a"])
            .unwrap();

        // Get b's observed changed_at for a
        let b_node = rt.get(&"b").unwrap();
        let observed = b_node
            .dependencies
            .iter()
            .next()
            .unwrap()
            .observed_changed_at;

        // Update a (this changes its changed_at)
        rt.register("a", (), Durability::volatile(), vec![])
            .unwrap();

        let a_node = rt.get(&"a").unwrap();
        assert!(a_node.changed_at > observed);

        // b should now be invalid (if not verified at new revision)
        // Since b's verified_at is less than new revision, and a changed
        let rev = rt.current_revision();
        assert!(!rt.is_valid_at(&"b", &rev));
    }

    #[test]
    fn test_early_cutoff() {
        let rt: TestRuntime = Runtime::new();

        rt.register("a", (), Durability::volatile(), vec![])
            .unwrap();
        rt.register("b", (), Durability::volatile(), vec!["a"])
            .unwrap();
        rt.register("c", (), Durability::volatile(), vec!["b"])
            .unwrap();

        // Record b's changed_at
        let b_old = rt.get(&"b").unwrap();
        let b_changed_at_before = b_old.changed_at;

        // Confirm b unchanged (early cutoff)
        rt.confirm_unchanged(&"b", vec!["a"]).unwrap();

        // b's changed_at should be preserved
        let b_new = rt.get(&"b").unwrap();
        assert_eq!(b_new.changed_at, b_changed_at_before);

        // But verified_at should be updated
        assert!(b_new.verified_at >= b_changed_at_before);
    }

    #[test]
    fn test_confirm_changed() {
        let rt: TestRuntime = Runtime::new();

        rt.register("a", (), Durability::volatile(), vec![])
            .unwrap();
        let a_old = rt.get(&"a").unwrap();

        // Confirm a changed
        let new_rev = rt.confirm_changed(&"a", vec![]).unwrap();

        let a_new = rt.get(&"a").unwrap();
        assert!(a_new.changed_at > a_old.changed_at);
        assert_eq!(a_new.changed_at, new_rev);
        assert_eq!(a_new.verified_at, new_rev);
    }

    #[test]
    fn test_durability_invariant() {
        let rt: TestRuntime = Runtime::new();

        // Register a with stable durability
        rt.register("a", (), Durability::stable(), vec![]).unwrap();

        // Register b with stable durability, depending on a
        let b_result = rt
            .register("b", (), Durability::stable(), vec!["a"])
            .unwrap();
        assert_eq!(b_result.effective_durability, Durability::stable());

        // Register c with volatile durability
        rt.register("c", (), Durability::volatile(), vec![])
            .unwrap();

        // Register d with stable requested, but depending on volatile c
        let d_result = rt
            .register("d", (), Durability::stable(), vec!["c"])
            .unwrap();
        // d's effective durability should be volatile (min of stable and volatile)
        assert_eq!(d_result.effective_durability, Durability::volatile());
    }

    #[test]
    fn test_cycle_detection() {
        let rt: TestRuntime = Runtime::new();

        rt.register("a", (), Durability::volatile(), vec![])
            .unwrap();
        rt.register("b", (), Durability::volatile(), vec!["a"])
            .unwrap();
        rt.register("a", (), Durability::volatile(), vec!["b"])
            .unwrap();

        assert!(rt.has_cycle("a"));
        assert!(rt.has_cycle("b"));
    }

    #[test]
    fn test_remove_if_unused() {
        let rt: TestRuntime = Runtime::new();

        rt.register("a", (), Durability::volatile(), vec![])
            .unwrap();

        // a has no dependents, can be removed
        let removed = rt.remove_if_unused("a");
        assert!(removed.is_some());
        assert!(rt.get(&"a").is_none());

        // Re-register a and b
        rt.register("a", (), Durability::volatile(), vec![])
            .unwrap();
        rt.register("b", (), Durability::volatile(), vec!["a"])
            .unwrap();

        // a has dependents now, cannot be removed
        let removed = rt.remove_if_unused("a");
        assert!(removed.is_none());
        assert!(rt.get(&"a").is_some());
    }

    #[test]
    fn test_mark_verified() {
        let rt: TestRuntime = Runtime::new();

        rt.register("a", (), Durability::volatile(), vec![])
            .unwrap();
        let a_old = rt.get(&"a").unwrap();

        // Increment revision without changing a
        rt.increment_revision(Durability::volatile());
        let new_rev = rt.current_revision();

        // Mark a as verified at new revision
        rt.mark_verified(&"a", &new_rev);

        let a_new = rt.get(&"a").unwrap();
        assert!(a_new.verified_at > a_old.verified_at);
    }

    #[test]
    fn test_missing_dependency_error() {
        let rt: TestRuntime = Runtime::new();

        // Try to register with non-existent dependency
        let result = rt.register("a", (), Durability::volatile(), vec!["nonexistent"]);
        assert!(result.is_err());
        assert_eq!(result.unwrap_err(), vec!["nonexistent"]);
    }

    #[test]
    fn test_multi_level_revision_increment() {
        let rt: TestRuntime = Runtime::new();

        // Increment at level 2 (stable)
        rt.increment_revision(Durability::stable());

        let rev = rt.current_revision();
        // All levels 0, 1, 2 should be incremented
        assert_eq!(rev.get(Durability::new(0).unwrap()), 1);
        assert_eq!(rev.get(Durability::new(1).unwrap()), 1);
        assert_eq!(rev.get(Durability::new(2).unwrap()), 1);

        // Increment at level 0 only
        rt.increment_revision(Durability::volatile());

        let rev = rt.current_revision();
        assert_eq!(rev.get(Durability::new(0).unwrap()), 2);
        assert_eq!(rev.get(Durability::new(1).unwrap()), 1);
        assert_eq!(rev.get(Durability::new(2).unwrap()), 1);
    }
}
