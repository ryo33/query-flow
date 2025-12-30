//! Dependency tree generation.

use crate::config::{DataSize, FuzzConfig, QueryTimeBias, TimeDistribution, TreeShape};
use crate::distribution::sample_in_range;
use rand::prelude::*;
use std::collections::HashMap;

/// Unique identifier for a node in the synthetic tree.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct NodeId(pub u32);

impl std::fmt::Display for NodeId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Node({})", self.0)
    }
}

/// Node in the synthetic dependency tree.
#[derive(Debug, Clone)]
pub struct TreeNode {
    pub id: NodeId,
    pub depth: u32,
    pub kind: NodeKind,
    pub dependencies: Vec<NodeId>,
    /// Simulated execution time for this node (microseconds).
    pub simulated_time_us: u64,
    /// Output size in bytes.
    pub output_size: usize,
}

/// Kind of node in the tree.
#[derive(Debug, Clone)]
pub enum NodeKind {
    /// Leaf node (asset).
    Asset {
        /// Size of asset data in bytes.
        data_size: usize,
        /// Resolution time in microseconds.
        resolve_time_us: u64,
    },
    /// Internal query node.
    Query,
    /// Root query (entry point).
    Root,
}

impl NodeKind {
    pub fn is_asset(&self) -> bool {
        matches!(self, NodeKind::Asset { .. })
    }

    pub fn is_query(&self) -> bool {
        matches!(self, NodeKind::Query | NodeKind::Root)
    }
}

/// Generated dependency tree.
#[derive(Debug)]
pub struct DependencyTree {
    pub nodes: HashMap<NodeId, TreeNode>,
    pub roots: Vec<NodeId>,
    pub leaves: Vec<NodeId>,
    pub max_depth: u32,
    /// Topological order: leaves first, roots last.
    pub topology_order: Vec<NodeId>,
}

impl DependencyTree {
    /// Get all nodes at a specific depth.
    pub fn nodes_at_depth(&self, depth: u32) -> Vec<NodeId> {
        self.nodes
            .values()
            .filter(|n| n.depth == depth)
            .map(|n| n.id)
            .collect()
    }

    /// Compute expected output for all nodes given leaf values.
    ///
    /// Returns a map from node ID to expected output bytes.
    pub fn compute_expected(&self, leaf_values: &HashMap<NodeId, Vec<u8>>) -> HashMap<NodeId, Vec<u8>> {
        let mut outputs: HashMap<NodeId, Vec<u8>> = HashMap::new();

        // Process in topological order (leaves first)
        for &node_id in &self.topology_order {
            let node = &self.nodes[&node_id];
            let output: Vec<u8> = match &node.kind {
                NodeKind::Asset { .. } => {
                    leaf_values.get(&node_id).cloned().unwrap_or_default()
                }
                NodeKind::Query | NodeKind::Root => {
                    // Combine dependency outputs with deterministic function
                    let mut combined = Vec::new();
                    for dep_id in &node.dependencies {
                        if let Some(dep_output) = outputs.get(dep_id) {
                            combined.extend_from_slice(dep_output);
                        }
                    }
                    // Apply a deterministic transform
                    compute_hash_output(&combined, node.output_size)
                }
            };
            outputs.insert(node_id, output);
        }

        outputs
    }
}

/// Tree generator.
pub struct TreeGenerator<R: Rng> {
    rng: R,
    config: FuzzConfig,
    next_id: u32,
}

impl<R: Rng> TreeGenerator<R> {
    pub fn new(config: FuzzConfig, rng: R) -> Self {
        Self {
            rng,
            config,
            next_id: 0,
        }
    }

    fn next_id(&mut self) -> NodeId {
        let id = NodeId(self.next_id);
        self.next_id += 1;
        id
    }

    pub fn generate(&mut self) -> DependencyTree {
        match self.config.tree_shape {
            TreeShape::LinkedList => self.generate_linked_list(),
            TreeShape::Binary => self.generate_nary_tree(2, false),
            TreeShape::NAry { branching_factor } => self.generate_nary_tree(branching_factor, false),
            TreeShape::CompleteNAry { branching_factor } => {
                self.generate_nary_tree(branching_factor, true)
            }
            TreeShape::RandomDag { expected_fan_out } => self.generate_random_dag(expected_fan_out),
        }
    }

    fn generate_linked_list(&mut self) -> DependencyTree {
        let mut nodes = HashMap::new();
        let mut prev_id = None;

        // Generate from root (depth 0) to leaf (max depth)
        for depth in 0..self.config.tree_depth {
            let id = self.next_id();
            let is_leaf = depth == self.config.tree_depth - 1;

            let kind = if is_leaf {
                NodeKind::Asset {
                    data_size: self.sample_asset_size(),
                    resolve_time_us: self.sample_asset_resolve_time(),
                }
            } else if depth == 0 {
                NodeKind::Root
            } else {
                NodeKind::Query
            };

            // In a linked list, each node depends on the next (deeper) node
            // We'll build bottom-up, so dependencies point to previously created nodes
            let dependencies = prev_id.map(|p| vec![p]).unwrap_or_default();

            nodes.insert(
                id,
                TreeNode {
                    id,
                    depth,
                    kind,
                    dependencies,
                    simulated_time_us: self.sample_query_time(depth),
                    output_size: self.sample_output_size(),
                },
            );

            prev_id = Some(id);
        }

        let root = NodeId(0);
        let leaf = NodeId(self.config.tree_depth - 1);

        DependencyTree {
            topology_order: compute_topo_order(&nodes),
            nodes,
            roots: vec![root],
            leaves: vec![leaf],
            max_depth: self.config.tree_depth - 1,
        }
    }

    fn generate_nary_tree(&mut self, branching_factor: u32, _complete: bool) -> DependencyTree {
        let mut nodes = HashMap::new();
        let mut current_level = vec![];
        let mut leaves = vec![];

        // Calculate how many leaves we need
        let target_leaf_count = self.config.asset_count.max(1);

        // Generate leaves at the deepest level
        for _ in 0..target_leaf_count {
            let id = self.next_id();
            nodes.insert(
                id,
                TreeNode {
                    id,
                    depth: self.config.tree_depth - 1,
                    kind: NodeKind::Asset {
                        data_size: self.sample_asset_size(),
                        resolve_time_us: self.sample_asset_resolve_time(),
                    },
                    dependencies: vec![],
                    simulated_time_us: 0,
                    output_size: self.sample_output_size(),
                },
            );
            leaves.push(id);
            current_level.push(id);
        }

        // Build tree from leaves up to root
        for depth in (0..self.config.tree_depth - 1).rev() {
            let mut next_level = vec![];
            let chunks: Vec<_> = current_level
                .chunks(branching_factor as usize)
                .collect();

            for chunk in chunks {
                let id = self.next_id();
                let kind = if depth == 0 {
                    NodeKind::Root
                } else {
                    NodeKind::Query
                };

                nodes.insert(
                    id,
                    TreeNode {
                        id,
                        depth,
                        kind,
                        dependencies: chunk.to_vec(),
                        simulated_time_us: self.sample_query_time(depth),
                        output_size: self.sample_output_size(),
                    },
                );
                next_level.push(id);
            }
            current_level = next_level;
        }

        let roots = current_level;

        DependencyTree {
            topology_order: compute_topo_order(&nodes),
            nodes,
            roots,
            leaves,
            max_depth: self.config.tree_depth - 1,
        }
    }

    fn generate_random_dag(&mut self, expected_fan_out: f64) -> DependencyTree {
        let mut nodes = HashMap::new();
        let mut levels: Vec<Vec<NodeId>> = vec![vec![]; self.config.tree_depth as usize];

        // Create leaves
        for _ in 0..self.config.asset_count {
            let id = self.next_id();
            let depth = self.config.tree_depth - 1;
            nodes.insert(
                id,
                TreeNode {
                    id,
                    depth,
                    kind: NodeKind::Asset {
                        data_size: self.sample_asset_size(),
                        resolve_time_us: self.sample_asset_resolve_time(),
                    },
                    dependencies: vec![],
                    simulated_time_us: 0,
                    output_size: self.sample_output_size(),
                },
            );
            levels[depth as usize].push(id);
        }

        // Create internal nodes with random dependencies to lower levels
        for depth in (0..self.config.tree_depth - 1).rev() {
            let nodes_at_level = (self.config.node_count / self.config.tree_depth).max(1);

            for _ in 0..nodes_at_level {
                let id = self.next_id();

                // Randomly select dependencies from lower levels
                let dep_count = self.rng.gen_range(1..=(expected_fan_out * 2.0) as usize);
                let mut dependencies = vec![];

                for lower_depth in (depth + 1)..self.config.tree_depth {
                    let lower_level = &levels[lower_depth as usize];
                    if !lower_level.is_empty() {
                        let sample_count =
                            (dep_count / (self.config.tree_depth - depth - 1) as usize).max(1);
                        for &dep_id in lower_level.choose_multiple(&mut self.rng, sample_count) {
                            dependencies.push(dep_id);
                        }
                    }
                }

                // Ensure at least one dependency
                if dependencies.is_empty() {
                    if let Some(lower_level) = levels.get((depth + 1) as usize) {
                        if let Some(&dep_id) = lower_level.choose(&mut self.rng) {
                            dependencies.push(dep_id);
                        }
                    }
                }

                let kind = if depth == 0 {
                    NodeKind::Root
                } else {
                    NodeKind::Query
                };

                nodes.insert(
                    id,
                    TreeNode {
                        id,
                        depth,
                        kind,
                        dependencies,
                        simulated_time_us: self.sample_query_time(depth),
                        output_size: self.sample_output_size(),
                    },
                );
                levels[depth as usize].push(id);
            }
        }

        let roots = levels[0].clone();
        let leaves = levels[(self.config.tree_depth - 1) as usize].clone();

        DependencyTree {
            topology_order: compute_topo_order(&nodes),
            nodes,
            roots,
            leaves,
            max_depth: self.config.tree_depth - 1,
        }
    }

    fn sample_query_time(&mut self, depth: u32) -> u64 {
        let base = sample_time(&self.config.query_time, &mut self.rng);

        match self.config.query_time_bias {
            QueryTimeBias::Uniform => base,
            QueryTimeBias::DepthProportional => {
                // Root queries take longer
                let factor =
                    (self.config.tree_depth - depth) as f64 / self.config.tree_depth as f64;
                (base as f64 * (0.5 + factor)).round() as u64
            }
            QueryTimeBias::HotQueries {
                hot_fraction,
                hot_multiplier,
            } => {
                if self.rng.gen::<f64>() < hot_fraction {
                    (base as f64 * hot_multiplier).round() as u64
                } else {
                    base
                }
            }
        }
    }

    fn sample_asset_size(&mut self) -> usize {
        sample_size(&self.config.asset_size, &mut self.rng)
    }

    fn sample_asset_resolve_time(&mut self) -> u64 {
        sample_time(&self.config.asset_resolve_time, &mut self.rng)
    }

    fn sample_output_size(&mut self) -> usize {
        sample_size(&self.config.output_size, &mut self.rng)
    }
}

fn sample_time<R: Rng>(dist: &TimeDistribution, rng: &mut R) -> u64 {
    sample_in_range(rng, dist.min_us, dist.max_us, dist.distribution)
}

fn sample_size<R: Rng>(size: &DataSize, rng: &mut R) -> usize {
    sample_in_range(
        rng,
        size.min_bytes as u64,
        size.max_bytes as u64,
        size.distribution,
    ) as usize
}

/// Compute topological order using Kahn's algorithm.
/// Returns nodes in order: leaves first, roots last.
fn compute_topo_order(nodes: &HashMap<NodeId, TreeNode>) -> Vec<NodeId> {
    use std::collections::VecDeque;

    let mut in_degree: HashMap<NodeId, usize> = HashMap::new();
    let mut dependents: HashMap<NodeId, Vec<NodeId>> = HashMap::new();

    // Initialize in-degree and build reverse adjacency list
    for (&id, node) in nodes {
        in_degree.entry(id).or_insert(0);
        for &dep_id in &node.dependencies {
            *in_degree.entry(id).or_insert(0) += 1;
            dependents.entry(dep_id).or_default().push(id);
        }
    }

    // Start with nodes that have no dependencies (leaves/assets)
    let mut queue: VecDeque<NodeId> = in_degree
        .iter()
        .filter(|(_, &deg)| deg == 0)
        .map(|(&id, _)| id)
        .collect();

    let mut order = Vec::with_capacity(nodes.len());

    while let Some(node_id) = queue.pop_front() {
        order.push(node_id);

        if let Some(deps) = dependents.get(&node_id) {
            for &dependent_id in deps {
                if let Some(deg) = in_degree.get_mut(&dependent_id) {
                    *deg -= 1;
                    if *deg == 0 {
                        queue.push_back(dependent_id);
                    }
                }
            }
        }
    }

    order
}

/// Compute a deterministic hash-based output from input data.
pub fn compute_hash_output(input: &[u8], size: usize) -> Vec<u8> {
    use std::hash::{Hash, Hasher};

    let mut output = Vec::with_capacity(size);
    let mut hasher = ahash::AHasher::default();
    input.hash(&mut hasher);

    // Generate deterministic output bytes
    let mut seed = hasher.finish();
    while output.len() < size {
        output.extend_from_slice(&seed.to_le_bytes());
        seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
    }
    output.truncate(size);
    output
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_linked_list_generation() {
        let config = FuzzConfig::minimal()
            .with_depth(5)
            .with_shape(TreeShape::LinkedList);
        let mut gen = TreeGenerator::new(config, rand::thread_rng());
        let tree = gen.generate();

        assert_eq!(tree.roots.len(), 1);
        assert_eq!(tree.leaves.len(), 1);
        assert_eq!(tree.nodes.len(), 5);
        assert_eq!(tree.max_depth, 4);
    }

    #[test]
    fn test_binary_tree_generation() {
        let config = FuzzConfig::minimal()
            .with_depth(3)
            .with_asset_count(4)
            .with_shape(TreeShape::Binary);
        let mut gen = TreeGenerator::new(config, rand::thread_rng());
        let tree = gen.generate();

        assert_eq!(tree.leaves.len(), 4);
        assert!(!tree.roots.is_empty());
    }

    #[test]
    fn test_topo_order() {
        let config = FuzzConfig::minimal()
            .with_depth(3)
            .with_asset_count(4)
            .with_shape(TreeShape::Binary);
        let mut gen = TreeGenerator::new(config, rand::thread_rng());
        let tree = gen.generate();

        // Verify topological order: all dependencies come before dependents
        let mut processed = std::collections::HashSet::new();
        for &node_id in &tree.topology_order {
            let node = &tree.nodes[&node_id];
            for dep_id in &node.dependencies {
                assert!(
                    processed.contains(dep_id),
                    "Dependency {:?} should come before {:?}",
                    dep_id,
                    node_id
                );
            }
            processed.insert(node_id);
        }
    }

    #[test]
    fn test_compute_expected() {
        let config = FuzzConfig::minimal()
            .with_depth(2)
            .with_asset_count(2)
            .with_shape(TreeShape::Binary);
        let mut gen = TreeGenerator::new(config, rand::thread_rng());
        let tree = gen.generate();

        // Create leaf values
        let mut leaf_values = HashMap::new();
        for &leaf_id in &tree.leaves {
            leaf_values.insert(leaf_id, vec![leaf_id.0 as u8; 8]);
        }

        let expected = tree.compute_expected(&leaf_values);

        // All nodes should have expected values
        assert_eq!(expected.len(), tree.nodes.len());
    }

    #[test]
    fn test_deterministic_output() {
        let input = b"hello world";
        let output1 = compute_hash_output(input, 32);
        let output2 = compute_hash_output(input, 32);
        assert_eq!(output1, output2);
        assert_eq!(output1.len(), 32);
    }
}
