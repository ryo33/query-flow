//! Runtime for the Whale incremental computation system.
//!
//! The Runtime manages the dependency graph and provides the core operations
//! for registering queries, checking validity, and handling early cutoff.
//!
//! # Concurrency model
//!
//! Nodes live in a [`ShardedMap`] of `Arc<NodeState>`. The fields that validity
//! checks read (`verified_at`, `changed_at`, `durability`, `level`) are atomics,
//! so `is_valid`, `is_verified_at` and dependency lookups never block on a
//! writer. Structural updates (data, dependencies, reverse edges) take a
//! per-node mutex and run exactly once; no operation retries.
//!
//! Lock order is always shard lock, then node lock, and no lock is held while
//! calling into another shard. The only user callback that runs under a lock
//! is the `compare` function of [`Runtime::update_with_compare`]; it must not
//! call back into the runtime.

use std::sync::Arc;

use crate::{
    map::ShardedMap,
    node::{Dep, Dependencies, Node},
    node_state::{NodeInner, NodeState},
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
    nodes: Arc<ShardedMap<K, Arc<NodeState<K, T, N>>>>,
    revision: Arc<AtomicRevision<N>>,
}

#[test]
fn test_runtime_send_sync() {
    fn assert_send_sync<T: Send + Sync>() {}
    assert_send_sync::<Runtime<&str, (), 3>>();
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
            nodes: Arc::new(ShardedMap::new()),
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

/// Result of an update_with_compare operation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UpdateCompareResult<const N: usize> {
    /// Whether the value was considered changed.
    pub changed: bool,
    /// The revision counter (new if changed, current if unchanged).
    pub revision: RevisionCounter,
    /// The effective durability.
    pub effective_durability: Durability<N>,
}

/// Result of a get_or_insert operation.
#[derive(Debug, Clone)]
pub enum GetOrInsertResult<K, T, const N: usize> {
    /// Node was inserted (didn't exist before).
    Inserted(Node<K, T, N>),
    /// Node already existed (returned existing node).
    Existing(Node<K, T, N>),
}

/// Dependency information resolved in a single pass over the dependency nodes.
struct ResolvedDeps<K, const N: usize> {
    records: Vec<Dep<K>>,
    effective_durability: Durability<N>,
    level: u32,
}

/// The entry handed to [`Runtime::upsert`]'s closure.
enum Entry<'a, K, T, const N: usize> {
    /// The node exists; its structural fields are write-locked.
    Occupied(&'a NodeState<K, T, N>, &'a mut NodeInner<K, T>),
    /// No node exists; the closure gets the key back to build one.
    Vacant(K),
}

impl<K, T, const N: usize> Runtime<K, T, N>
where
    K: Clone + PartialEq + Eq + std::hash::Hash + std::fmt::Debug,
    T: Clone,
{
    /// Get a node by query ID.
    ///
    /// This copies the whole node, including its dependency and dependent
    /// lists. When only the data and `changed_at` are needed, prefer
    /// [`Self::get_data`].
    pub fn get(&self, query_id: &K) -> Option<Node<K, T, N>> {
        self.nodes.with(query_id, |node| node.snapshot())
    }

    /// Get a node's data together with its `changed_at`.
    ///
    /// Cheaper than [`Self::get`]: it does not copy the query ID or the edge lists.
    pub fn get_data(&self, query_id: &K) -> Option<(T, RevisionCounter)> {
        self.nodes.with(query_id, |node| node.data_and_changed_at())
    }

    /// Iterate over all query IDs.
    pub fn keys(&self) -> Vec<K> {
        self.nodes.keys()
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
        // Fast path (no Arc clone, no node lock): already verified at this revision.
        let dependencies = self.nodes.with(qid, |node| {
            if node.verified_at() >= at_rev.get(node.durability()) {
                None
            } else {
                Some(node.read().dependencies.clone())
            }
        });
        let dependencies = match dependencies {
            None => return false, // node does not exist
            Some(None) => return true,
            Some(Some(dependencies)) => dependencies,
        };

        // Check each dependency (shallow check - only direct deps' changed_at)
        let deps_valid = dependencies.iter().all(|dep| {
            self.nodes
                .with(&dep.query_id, |dep_node| {
                    // Using <= (not <): equal means "no change since observation"
                    dep_node.changed_at() <= dep.observed_changed_at
                })
                // dependency removed
                .unwrap_or(false)
        });
        deps_valid
    }

    /// Convenience: check validity at current revision.
    pub fn is_valid(&self, qid: &K) -> bool {
        self.is_valid_at(qid, &self.current_revision())
    }

    /// Get the dependency IDs for a node.
    ///
    /// Returns None if the node doesn't exist.
    /// Used by query-flow to verify dependencies before deciding to recompute.
    pub fn get_dependency_ids(&self, qid: &K) -> Option<Vec<K>> {
        self.nodes.with(qid, |node| {
            node.read()
                .dependencies
                .iter()
                .map(|d| d.query_id.clone())
                .collect()
        })
    }

    /// Check if a node has been verified at the given revision.
    ///
    /// This is a fast check that only looks at verified_at, not dependencies.
    pub fn is_verified_at(&self, qid: &K, at_rev: &Revision<N>) -> bool {
        self.nodes
            .with(qid, |node| {
                node.verified_at() >= at_rev.get(node.durability())
            })
            .unwrap_or(false)
    }

    /// Mark a node as verified at given revision (idempotent update).
    ///
    /// Uses `max` to ensure monotonicity - `verified_at` only increases.
    pub fn mark_verified(&self, qid: &K, at_rev: &Revision<N>) {
        self.nodes.with(qid, |node| {
            // Lock-free fast path: already verified at (or past) this revision.
            // This is the steady state on cache hits, so it must not write.
            if node.verified_at() >= at_rev.get(node.durability()) {
                return;
            }
            // A read guard is enough: it excludes writers (who may change the
            // durability), and fetch_max commutes with other markers.
            let _guard = node.read();
            node.raise_verified_at(at_rev.get(node.durability()));
        });
    }

    /// Resolve dependencies in one pass: capture each dependency's current
    /// `changed_at`, and compute the effective durability
    /// (`min(requested, deps.durability)`) and topological level
    /// (`max(deps.level) + 1`).
    ///
    /// Returns `Err` with the list of missing query IDs if any dependency doesn't exist.
    fn resolve_deps(
        &self,
        requested: Durability<N>,
        dep_ids: &[K],
    ) -> Result<ResolvedDeps<K, N>, Vec<K>> {
        let mut records = Vec::with_capacity(dep_ids.len());
        let mut missing = Vec::new();
        let mut min_durability = N - 1;
        let mut max_level = 0;

        for dep_id in dep_ids {
            let found = self.nodes.with(dep_id, |dep_node| {
                records.push(Dep {
                    query_id: dep_id.clone(),
                    observed_changed_at: dep_node.changed_at(),
                });
                min_durability = min_durability.min(dep_node.durability().value());
                max_level = max_level.max(dep_node.level());
            });
            if found.is_none() {
                missing.push(dep_id.clone());
            }
        }

        if !missing.is_empty() {
            return Err(missing);
        }

        let effective = requested.value().min(min_durability);
        Ok(ResolvedDeps {
            records,
            effective_durability: Durability::new(effective).unwrap_or(Durability::volatile()),
            level: max_level + 1,
        })
    }

    /// Update reverse edges: add `qid` to the dependents list of all its dependencies.
    ///
    /// This maintains bidirectional consistency of the graph structure.
    fn update_graph_edges(&self, qid: &K, deps: &Dependencies<K>) {
        for dep in deps.iter() {
            self.nodes.with(&dep.query_id, |dep_node| {
                dep_node.write().dependents.insert(qid);
            });
        }
    }

    /// Remove `qid` from the dependents list of old dependencies that are no longer in new deps.
    ///
    /// This cleans up stale reverse edges when a node's dependencies change.
    fn cleanup_stale_edges(&self, qid: &K, old_deps: &Dependencies<K>, new_deps: &Dependencies<K>) {
        for old_dep in old_deps.iter() {
            if new_deps.iter().any(|d| d.query_id == old_dep.query_id) {
                continue;
            }
            // This dependency was removed, clean up the reverse edge
            self.nodes.with(&old_dep.query_id, |dep_node| {
                dep_node.write().dependents.remove(qid);
            });
        }
    }

    /// Replace `qid`'s old dependency edges with `new_deps`.
    fn replace_edges(
        &self,
        qid: &K,
        old_deps: Option<&Dependencies<K>>,
        new_deps: &Dependencies<K>,
    ) {
        if let Some(old_deps) = old_deps {
            self.cleanup_stale_edges(qid, old_deps, new_deps);
        }
        self.update_graph_edges(qid, new_deps);
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
        let resolved = self.resolve_deps(requested_durability, &dep_ids)?;
        let effective_dur = resolved.effective_durability;
        let new_level = resolved.level;
        let new_deps = Dependencies::new(resolved.records);

        // Increment revision
        let new_rev = self.increment_revision(effective_dur);

        // Insert or update in place (keeping the existing dependents list).
        let old_deps = self.upsert(qid.clone(), |entry| match entry {
            Entry::Occupied(node, inner) => {
                inner.data = data;
                let old = std::mem::replace(&mut inner.dependencies, new_deps.clone());
                node.set_meta(effective_dur, new_level);
                node.set_verified_at(new_rev);
                node.set_changed_at(new_rev);
                (None, Some(old))
            }
            Entry::Vacant(qid) => {
                let node = NodeState::new(
                    qid,
                    data,
                    effective_dur,
                    new_rev,
                    new_rev,
                    new_level,
                    new_deps.clone(),
                );
                (Some(Arc::new(node)), None)
            }
        });

        self.replace_edges(&qid, old_deps.as_ref(), &new_deps);

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
        let Some(node) = self.nodes.get(qid) else {
            return Ok(());
        };

        let resolved = self.resolve_deps(node.durability(), &new_dep_ids)?;
        let effective_dur = resolved.effective_durability;
        let new_deps = Dependencies::new(resolved.records);
        let current_rev = self.revision.get(effective_dur);

        // Update node: verified_at changes, changed_at stays the same!
        let old_deps = {
            let mut inner = node.write();
            if inner.detached {
                return Ok(()); // Removed concurrently; nothing to confirm.
            }
            let old = std::mem::replace(&mut inner.dependencies, new_deps.clone());
            node.set_meta(effective_dur, resolved.level);
            node.raise_verified_at(current_rev);
            old
        };

        self.replace_edges(qid, Some(&old_deps), &new_deps);

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
        let Some(node) = self.nodes.get(qid) else {
            return Ok(0);
        };

        let resolved = self.resolve_deps(node.durability(), &new_dep_ids)?;
        let effective_dur = resolved.effective_durability;
        let new_deps = Dependencies::new(resolved.records);

        let old_deps = {
            let mut inner = node.write();
            if inner.detached {
                return Ok(0); // Removed concurrently; nothing to confirm.
            }
            // Increment revision at the effective durability level
            let new_rev = self.increment_revision(effective_dur);
            let old = std::mem::replace(&mut inner.dependencies, new_deps.clone());
            node.set_meta(effective_dur, resolved.level);
            node.set_verified_at(new_rev);
            node.set_changed_at(new_rev); // Both updated!
            (old, new_rev)
        };
        let (old_deps, new_rev) = old_deps;

        self.replace_edges(qid, Some(&old_deps), &new_deps);

        Ok(new_rev)
    }

    /// Remove a node from the runtime.
    ///
    /// Returns the removed node if it existed.
    pub fn remove(&self, query_id: &K) -> Option<Node<K, T, N>> {
        self.nodes.compute(query_id.clone(), |slot| {
            slot.take().map(|node| Self::detach(&node))
        })
    }

    /// Mark a node that has just been taken out of the map as detached and
    /// return its final state. Must run under the shard's write lock (i.e.
    /// inside [`ShardedMap::compute`]) so that no writer can slip in between
    /// the map removal and the flag.
    fn detach(node: &NodeState<K, T, N>) -> Node<K, T, N> {
        let mut inner = node.write();
        inner.detached = true;
        node.snapshot_with(&inner)
    }

    /// Apply `f` to the entry for `qid`: either the existing node (under its
    /// write lock) or a vacant slot, in which case `f` returns the node to
    /// insert. `f` runs exactly once.
    ///
    /// An existing node is updated without taking the shard's write lock, so
    /// writers to different keys never block each other. Only an insert (or a
    /// race with a concurrent removal) goes through the shard's write lock.
    fn upsert<R>(
        &self,
        qid: K,
        f: impl FnOnce(Entry<'_, K, T, N>) -> (Option<Arc<NodeState<K, T, N>>>, R),
    ) -> R {
        let mut f = Some(f);

        // Fast path: the node exists; update it in place.
        if let Some(node) = self.nodes.get(&qid) {
            let mut inner = node.write();
            if !inner.detached {
                let f = f.take().expect("closure is consumed once");
                let (inserted, result) = f(Entry::Occupied(&node, &mut inner));
                debug_assert!(inserted.is_none(), "occupied entry must not insert");
                return result;
            }
            // Removed between the lookup and the lock; go through the map.
        }

        // Slow path: insert under the shard's write lock, unless someone
        // inserted in the meantime, in which case update that node.
        let key = qid.clone();
        self.nodes.compute(key, |slot| match slot {
            Some(node) => {
                let mut inner = node.write();
                let f = f.take().expect("closure is consumed once");
                let (inserted, result) = f(Entry::Occupied(node, &mut inner));
                debug_assert!(inserted.is_none(), "occupied entry must not insert");
                result
            }
            None => {
                let f = f.take().expect("closure is consumed once");
                let (inserted, result) = f(Entry::Vacant(qid));
                *slot = inserted;
                result
            }
        })
    }

    /// Remove a node if it has no dependents.
    ///
    /// Useful for garbage collection.
    pub fn remove_if_unused(&self, query_id: K) -> Option<Node<K, T, N>> {
        self.nodes.compute(query_id, |slot| {
            let unused = slot
                .as_ref()
                .is_some_and(|node| node.read().dependents.is_empty());
            if unused {
                slot.take().map(|node| Self::detach(&node))
            } else {
                None
            }
        })
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
            let dependencies = self
                .nodes
                .with(&qid, |node| node.read().dependencies.clone());
            if let Some(dependencies) = dependencies {
                for dep in dependencies.iter() {
                    stack.push((dep.query_id.clone(), false));
                }
            }
        }

        false
    }

    /// Atomically update a node with a compare function to determine if the value changed.
    ///
    /// This is the primary API for updating cached values with early cutoff optimization.
    /// The compare function receives the old data (if any) and new data, and returns
    /// true if the value should be considered changed.
    ///
    /// The whole read-compare-write runs once, under the node's lock, so
    /// `compare` is called exactly once. It must not call back into the runtime.
    ///
    /// Uses last-writer-wins semantics for concurrent updates.
    ///
    /// # Arguments
    /// - `qid`: The node ID
    /// - `new_data`: The new data to store
    /// - `compare`: Function that returns true if old and new are different
    /// - `durability`: Requested durability level
    /// - `dep_ids`: Dependencies
    ///
    /// # Returns
    /// - `Ok(UpdateCompareResult)` with changed flag and revision
    /// - `Err(Vec<K>)` if dependencies are missing
    pub fn update_with_compare<F>(
        &self,
        qid: K,
        new_data: T,
        compare: F,
        durability: Durability<N>,
        dep_ids: Vec<K>,
    ) -> Result<UpdateCompareResult<N>, Vec<K>>
    where
        F: FnOnce(Option<&T>, &T) -> bool,
    {
        // Build dependency records first (outside the atomic operation)
        let resolved = self.resolve_deps(durability, &dep_ids)?;
        let effective_dur = resolved.effective_durability;
        let new_level = resolved.level;
        let new_deps = Dependencies::new(resolved.records);

        // Atomic compare-and-update
        let (changed, revision, old_deps) = self.upsert(qid.clone(), |entry| match entry {
            Entry::Occupied(node, inner) => {
                let changed = compare(Some(&inner.data), &new_data);
                inner.data = new_data;
                let old = std::mem::replace(&mut inner.dependencies, new_deps.clone());
                node.set_meta(effective_dur, new_level);
                let revision = if changed {
                    let rev = self.increment_revision(effective_dur);
                    node.set_verified_at(rev);
                    node.set_changed_at(rev);
                    rev
                } else {
                    node.raise_verified_at(self.revision.get(effective_dur));
                    node.changed_at()
                };
                (None, (changed, revision, Some(old)))
            }
            Entry::Vacant(qid) => {
                let changed = compare(None, &new_data);
                let rev = if changed {
                    self.increment_revision(effective_dur)
                } else {
                    self.revision.get(effective_dur)
                };
                let node = NodeState::new(
                    qid,
                    new_data,
                    effective_dur,
                    rev,
                    rev,
                    new_level,
                    new_deps.clone(),
                );
                (Some(Arc::new(node)), (changed, rev, None))
            }
        });

        // Graph edge updates (dependents lists on dependency nodes).
        // These run outside the atomic section for the following reasons:
        // - Core correctness (changedAt/verifiedAt) is already atomic above
        // - Edge updates are idempotent: re-adding to dependents list is a no-op
        // - This provides eventual consistency for graph traversal
        // - Validity checks use changedAt/verifiedAt, not edge traversal
        self.replace_edges(&qid, old_deps.as_ref(), &new_deps);

        Ok(UpdateCompareResult {
            changed,
            revision,
            effective_durability: effective_dur,
        })
    }

    /// Atomically get an existing node or insert a new one.
    ///
    /// This is useful for cache-miss scenarios where multiple threads might
    /// try to populate the cache simultaneously.
    ///
    /// # Arguments
    /// - `qid`: The query/asset ID
    /// - `data`: Data to insert if the node doesn't exist
    /// - `durability`: Durability level for new node
    /// - `dep_ids`: Dependencies for new node
    ///
    /// # Returns
    /// - `Ok(GetOrInsertResult::Inserted(node))` if a new node was created
    /// - `Ok(GetOrInsertResult::Existing(node))` if the node already existed
    /// - `Err(Vec<K>)` if dependencies are missing (only checked on insert)
    pub fn get_or_insert(
        &self,
        qid: K,
        data: T,
        durability: Durability<N>,
        dep_ids: Vec<K>,
    ) -> Result<GetOrInsertResult<K, T, N>, Vec<K>> {
        // Fast-path: check if node already exists before doing expensive work.
        if let Some(existing) = self.get(&qid) {
            return Ok(GetOrInsertResult::Existing(existing));
        }

        // Build dependency records (only needed for insert)
        let resolved = self.resolve_deps(durability, &dep_ids)?;
        let effective_dur = resolved.effective_durability;
        let new_level = resolved.level;
        let new_deps = Dependencies::new(resolved.records);

        // Atomic insert-if-absent. The revision is only incremented when the
        // insert actually happens, so a losing thread wastes no revision numbers.
        let (node, inserted) = self.nodes.get_or_insert_with(qid.clone(), || {
            let new_rev = self.increment_revision(effective_dur);
            Arc::new(NodeState::new(
                qid.clone(),
                data,
                effective_dur,
                new_rev,
                new_rev,
                new_level,
                new_deps.clone(),
            ))
        });

        if inserted {
            self.update_graph_edges(&qid, &new_deps);
            Ok(GetOrInsertResult::Inserted(node.snapshot()))
        } else {
            Ok(GetOrInsertResult::Existing(node.snapshot()))
        }
    }
}

impl<K, T, const N: usize> std::fmt::Debug for Runtime<K, T, N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Runtime")
            .field("nodes", &self.nodes.len())
            .field("revision", &self.revision.snapshot())
            .finish()
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

#[cfg(test)]
mod concurrency_tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::thread;

    type TestRuntime = Runtime<u64, u64, 3>;

    #[test]
    fn compare_runs_exactly_once_under_contention() {
        let rt: Arc<TestRuntime> = Arc::new(Runtime::new());
        let calls = Arc::new(AtomicUsize::new(0));
        let threads = 8;
        let per_thread = 200;

        let handles: Vec<_> = (0..threads)
            .map(|t| {
                let rt = rt.clone();
                let calls = calls.clone();
                thread::spawn(move || {
                    for i in 0..per_thread {
                        rt.update_with_compare(
                            1,
                            t * 1000 + i,
                            |old, new| {
                                calls.fetch_add(1, Ordering::Relaxed);
                                old != Some(new)
                            },
                            Durability::volatile(),
                            vec![],
                        )
                        .unwrap();
                    }
                })
            })
            .collect();
        for h in handles {
            h.join().unwrap();
        }

        assert_eq!(
            calls.load(Ordering::Relaxed),
            threads as usize * per_thread as usize
        );
    }

    #[test]
    fn get_or_insert_increments_revision_once() {
        let rt: Arc<TestRuntime> = Arc::new(Runtime::new());
        let inserted = Arc::new(AtomicUsize::new(0));

        let handles: Vec<_> = (0..8)
            .map(|t| {
                let rt = rt.clone();
                let inserted = inserted.clone();
                thread::spawn(move || {
                    match rt
                        .get_or_insert(7, t, Durability::volatile(), vec![])
                        .unwrap()
                    {
                        GetOrInsertResult::Inserted(_) => {
                            inserted.fetch_add(1, Ordering::Relaxed);
                        }
                        GetOrInsertResult::Existing(_) => {}
                    }
                })
            })
            .collect();
        for h in handles {
            h.join().unwrap();
        }

        assert_eq!(inserted.load(Ordering::Relaxed), 1);
        // Exactly one revision was consumed: losers must not bump the counter.
        assert_eq!(rt.current_revision().get(Durability::volatile()), 1);
    }

    #[test]
    fn concurrent_registers_keep_reverse_edges_consistent() {
        let rt: Arc<TestRuntime> = Arc::new(Runtime::new());
        rt.register(0, 0, Durability::stable(), vec![]).unwrap();

        // Many nodes concurrently depend on node 0, then re-register with no deps.
        let handles: Vec<_> = (1..=16u64)
            .map(|id| {
                let rt = rt.clone();
                thread::spawn(move || {
                    for round in 0..50 {
                        rt.register(id, round, Durability::volatile(), vec![0])
                            .unwrap();
                        assert!(rt.is_valid(&id));
                        rt.register(id, round, Durability::volatile(), vec![])
                            .unwrap();
                    }
                })
            })
            .collect();
        for h in handles {
            h.join().unwrap();
        }

        // Every node ended with no deps, so node 0 must have no dependents left.
        let root = rt.get(&0).unwrap();
        assert!(root.dependents.is_empty(), "{:?}", root.dependents);
        assert!(rt.remove_if_unused(0).is_some());
    }

    #[test]
    fn readers_do_not_block_and_see_monotonic_revisions() {
        let rt: Arc<TestRuntime> = Arc::new(Runtime::new());
        rt.register(1, 0, Durability::volatile(), vec![]).unwrap();

        let writer = {
            let rt = rt.clone();
            thread::spawn(move || {
                for i in 1..=500 {
                    rt.confirm_changed(&1, vec![]).unwrap();
                    let rev = rt.current_revision();
                    rt.mark_verified(&1, &rev);
                    rt.register(1, i, Durability::volatile(), vec![]).unwrap();
                }
            })
        };
        let reader = {
            let rt = rt.clone();
            thread::spawn(move || {
                let mut last_changed = 0;
                let mut last_verified = 0;
                for _ in 0..2000 {
                    let node = rt.get(&1).unwrap();
                    assert!(node.changed_at >= last_changed);
                    assert!(node.verified_at >= last_verified);
                    assert!(node.verified_at >= node.changed_at);
                    last_changed = node.changed_at;
                    last_verified = node.verified_at;
                    let _ = rt.is_valid(&1);
                    let _ = rt.get_data(&1);
                }
            })
        };
        writer.join().unwrap();
        reader.join().unwrap();
    }

    #[test]
    fn concurrent_remove_and_register_never_lose_the_final_write() {
        let rt: Arc<TestRuntime> = Arc::new(Runtime::new());
        rt.register(1, 0, Durability::volatile(), vec![]).unwrap();

        let remover = {
            let rt = rt.clone();
            thread::spawn(move || {
                for _ in 0..2000 {
                    rt.remove(&1);
                    rt.remove_if_unused(1);
                }
            })
        };
        let writers: Vec<_> = (0..4)
            .map(|t| {
                let rt = rt.clone();
                thread::spawn(move || {
                    for i in 0..2000 {
                        rt.register(1, t * 10_000 + i, Durability::volatile(), vec![])
                            .unwrap();
                        rt.update_with_compare(
                            1,
                            i,
                            |a, b| a != Some(b),
                            Durability::volatile(),
                            vec![],
                        )
                        .unwrap();
                        let _ = rt.confirm_unchanged(&1, vec![]);
                        let _ = rt.confirm_changed(&1, vec![]);
                    }
                })
            })
            .collect();
        remover.join().unwrap();
        for w in writers {
            w.join().unwrap();
        }

        // Whatever interleaving happened, a write after all removals must stick.
        rt.register(1, 42, Durability::volatile(), vec![]).unwrap();
        assert_eq!(rt.get_data(&1), Some((42, rt.get(&1).unwrap().changed_at)));
        assert!(rt.is_valid(&1));
    }

    #[test]
    fn get_data_matches_get() {
        let rt: TestRuntime = Runtime::new();
        rt.register(1, 42, Durability::volatile(), vec![]).unwrap();
        let node = rt.get(&1).unwrap();
        assert_eq!(rt.get_data(&1), Some((42, node.changed_at)));
        assert_eq!(rt.get_data(&2), None);
    }

    #[test]
    fn remove_snapshot_is_detached() {
        let rt: TestRuntime = Runtime::new();
        rt.register(1, 1, Durability::volatile(), vec![]).unwrap();
        rt.register(2, 2, Durability::volatile(), vec![1]).unwrap();

        let removed = rt.remove(&1).unwrap();
        assert!(removed.dependents.contains(&2));
        assert!(rt.get(&1).is_none());
        // Once the revision moves on, a dependent of a removed node is invalid.
        rt.increment_revision(Durability::volatile());
        assert!(!rt.is_valid(&2));
        // Confirming with a missing dependency reports it.
        assert_eq!(rt.confirm_unchanged(&2, vec![1]), Err(vec![1]));
    }
}
