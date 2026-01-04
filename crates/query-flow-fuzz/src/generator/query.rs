//! Synthetic query implementation.

use super::asset::SyntheticAssetKey;
use super::tree::compute_hash_output;
use super::NodeId;
use query_flow::{Db, Query, QueryError};
use serde::{Deserialize, Serialize};
use std::cell::RefCell;
use std::sync::Arc;

thread_local! {
    /// Thread-local registry for looking up queries during execution.
    static QUERY_REGISTRY: RefCell<Option<Arc<QueryRegistry>>> = const { RefCell::new(None) };
}

/// Set the query registry for the current thread.
pub fn set_query_registry(registry: Arc<QueryRegistry>) {
    QUERY_REGISTRY.with(|r| {
        *r.borrow_mut() = Some(registry);
    });
}

/// Clear the query registry for the current thread.
pub fn clear_query_registry() {
    QUERY_REGISTRY.with(|r| {
        *r.borrow_mut() = None;
    });
}

/// Get a query from the thread-local registry.
fn get_query(node_id: &NodeId) -> Option<SyntheticQuery> {
    QUERY_REGISTRY.with(|r| {
        r.borrow()
            .as_ref()
            .and_then(|reg| reg.get(node_id).cloned())
    })
}

/// Dependency type for synthetic queries.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Dependency {
    /// Dependency on another synthetic query.
    Query(NodeId),
    /// Dependency on a synthetic asset.
    Asset(NodeId),
}

/// Synthetic query output.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SyntheticOutput {
    pub node_id: NodeId,
    pub data: Vec<u8>,
}

/// Synthetic query that simulates work and combines dependencies.
///
/// This query:
/// - Calls all its dependencies (other queries or assets)
/// - Combines their outputs into a deterministic hash-based output
/// - Records simulated execution time in events (but doesn't actually sleep)
#[derive(Clone, Debug)]
pub struct SyntheticQuery {
    /// Node ID in the tree.
    pub node_id: NodeId,
    /// Dependencies (other queries or assets).
    pub dependencies: Vec<Dependency>,
    /// Simulated execution time (recorded in events, no actual delay).
    pub simulated_time_us: u64,
    /// Output size in bytes.
    pub output_size: usize,
}

impl SyntheticQuery {
    /// Create a new synthetic query.
    pub fn new(
        node_id: NodeId,
        dependencies: Vec<Dependency>,
        simulated_time_us: u64,
        output_size: usize,
    ) -> Self {
        Self {
            node_id,
            dependencies,
            simulated_time_us,
            output_size,
        }
    }
}

impl Query for SyntheticQuery {
    type CacheKey = NodeId;
    type Output = SyntheticOutput;

    fn cache_key(&self) -> Self::CacheKey {
        self.node_id
    }

    fn query(self, db: &impl Db) -> Result<Arc<Self::Output>, QueryError> {
        // Collect dependency outputs
        let mut combined_data = Vec::new();

        for dep in &self.dependencies {
            match dep {
                Dependency::Query(dep_id) => {
                    // Look up the dependency query from the thread-local registry
                    let dep_query = get_query(dep_id).unwrap_or_else(|| {
                        // Fallback: create minimal query (should not happen in normal use)
                        SyntheticQuery::new(*dep_id, vec![], 0, 8)
                    });
                    let output = db.query(dep_query)?;
                    combined_data.extend_from_slice(&output.data);
                }
                Dependency::Asset(asset_id) => {
                    let asset_key = SyntheticAssetKey(*asset_id);
                    let data = db.asset(asset_key)?.suspend()?;
                    combined_data.extend_from_slice(&data);
                }
            }
        }

        // Compute deterministic output
        let output_data = compute_hash_output(&combined_data, self.output_size);

        Ok(Arc::new(SyntheticOutput {
            node_id: self.node_id,
            data: output_data,
        }))
    }

    fn output_eq(old: &Self::Output, new: &Self::Output) -> bool {
        old == new
    }
}

/// Registry of synthetic queries for lookup during execution.
#[derive(Debug, Default)]
pub struct QueryRegistry {
    queries: std::collections::HashMap<NodeId, SyntheticQuery>,
}

impl QueryRegistry {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn register(&mut self, query: SyntheticQuery) {
        self.queries.insert(query.node_id, query);
    }

    pub fn get(&self, node_id: &NodeId) -> Option<&SyntheticQuery> {
        self.queries.get(node_id)
    }

    pub fn iter(&self) -> impl Iterator<Item = (&NodeId, &SyntheticQuery)> {
        self.queries.iter()
    }
}

/// Build a query registry from a dependency tree.
pub fn build_query_registry(tree: &super::DependencyTree) -> QueryRegistry {
    use super::NodeKind;

    let mut registry = QueryRegistry::new();

    for (node_id, node) in &tree.nodes {
        if !node.kind.is_query() {
            continue;
        }

        let dependencies: Vec<Dependency> = node
            .dependencies
            .iter()
            .map(|&dep_id| {
                let dep_node = &tree.nodes[&dep_id];
                match &dep_node.kind {
                    NodeKind::Asset { .. } => Dependency::Asset(dep_id),
                    NodeKind::Query | NodeKind::Root => Dependency::Query(dep_id),
                }
            })
            .collect();

        let query = SyntheticQuery::new(
            *node_id,
            dependencies,
            node.simulated_time_us,
            node.output_size,
        );
        registry.register(query);
    }

    registry
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::{FuzzConfig, TreeShape};
    use crate::generator::TreeGenerator;

    #[test]
    fn test_build_query_registry() {
        let config = FuzzConfig::minimal()
            .with_depth(3)
            .with_asset_count(4)
            .with_shape(TreeShape::Binary);
        let mut gen = TreeGenerator::new(config, rand::thread_rng());
        let tree = gen.generate();

        let registry = build_query_registry(&tree);

        // Should have registered all query nodes (non-assets)
        let query_count = tree.nodes.values().filter(|n| n.kind.is_query()).count();
        assert_eq!(registry.queries.len(), query_count);
    }
}
