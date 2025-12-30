//! Test execution engine.

use crate::config::{FuzzConfig, UpdateBias};
use crate::generator::{
    build_query_registry, clear_query_registry, generate_asset_data, set_query_registry,
    DependencyTree, NodeId, NodeKind, QueryRegistry, SyntheticAssetKey, TreeGenerator,
};
use crate::recorder::{FuzzEventRecorder, FuzzRunRecord, RunMetadata, RunStats};
use crate::validator::{ValidationFailure, ValidationResult, Validator};
use query_flow::{QueryError, QueryRuntime};
use rand::prelude::*;
use rand::rngs::SmallRng;
use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration, Instant};

/// Result of a fuzz test run.
#[derive(Debug, Default)]
pub struct FuzzResult {
    pub query_successes: Vec<(NodeId, Duration)>,
    pub query_failures: Vec<(NodeId, QueryError)>,
    pub validation_successes: u32,
    pub validation_failures: Vec<ValidationFailure>,
    pub update_cycles: Vec<(u32, usize)>, // (cycle, assets_updated)
    pub total_duration: Duration,
}

impl FuzzResult {
    pub fn is_success(&self) -> bool {
        self.query_failures.is_empty() && self.validation_failures.is_empty()
    }

    pub fn total_queries(&self) -> usize {
        self.query_successes.len() + self.query_failures.len()
    }

    fn merge_validation(&mut self, result: ValidationResult) {
        self.validation_successes += result.successes;
        self.validation_failures.extend(result.failures);
        for (node_id, err) in result.errors {
            self.query_failures.push((node_id, err));
        }
    }
}

/// Fuzzy test runner.
pub struct FuzzRunner {
    config: FuzzConfig,
    rng: SmallRng,
    runtime: QueryRuntime,
    tree: DependencyTree,
    /// Current asset values (for validation).
    asset_values: HashMap<NodeId, Vec<u8>>,
    /// Asset version counters (for generating unique data).
    asset_versions: HashMap<NodeId, u64>,
    /// Query registry for looking up queries by ID.
    query_registry: Arc<QueryRegistry>,
    /// Event recorder.
    recorder: Option<Arc<FuzzEventRecorder>>,
    /// Round-robin index for RoundRobin update bias.
    round_robin_index: usize,
}

impl FuzzRunner {
    pub fn new(config: FuzzConfig) -> Self {
        let seed = config.seed.unwrap_or_else(rand::random);
        let mut rng = SmallRng::seed_from_u64(seed);

        // Generate the dependency tree
        let mut generator = TreeGenerator::new(config.clone(), SmallRng::seed_from_u64(seed));
        let tree = generator.generate();

        // Create runtime with inspector if recording
        let runtime = QueryRuntime::new();
        let recorder = if config.record_events {
            let recorder = Arc::new(FuzzEventRecorder::new());
            runtime.set_sink(Some(recorder.clone()));
            Some(recorder)
        } else {
            None
        };

        // Initialize query registry
        let query_registry = Arc::new(build_query_registry(&tree));

        // Initialize asset values
        let mut asset_values = HashMap::new();
        let mut asset_versions = HashMap::new();
        for &leaf_id in &tree.leaves {
            let node = &tree.nodes[&leaf_id];
            if let NodeKind::Asset { data_size, .. } = &node.kind {
                let data = generate_asset_data(leaf_id, *data_size, 0, &mut rng);
                asset_values.insert(leaf_id, data);
                asset_versions.insert(leaf_id, 0u64);
            }
        }

        Self {
            config,
            rng,
            runtime,
            tree,
            asset_values,
            asset_versions,
            query_registry,
            recorder,
            round_robin_index: 0,
        }
    }

    /// Run the complete fuzz test.
    pub fn run(&mut self) -> FuzzResult {
        let start = Instant::now();
        let mut result = FuzzResult::default();

        // Set up thread-local query registry
        set_query_registry(self.query_registry.clone());

        // Initial population: resolve all assets
        self.resolve_all_assets();

        // Initial query execution
        self.execute_all_roots(&mut result);

        // Validate initial state
        if self.config.full_validation_cycles {
            let validation = self.validate_all();
            result.merge_validation(validation);
        }

        // Run update cycles
        for cycle in 0..self.config.update_cycles {
            // Update some assets
            let updated = self.update_assets();
            result.update_cycles.push((cycle, updated.len()));

            // Re-query roots
            self.execute_all_roots(&mut result);

            // Validate
            if self.config.full_validation_cycles {
                let validation = self.validate_all();
                result.merge_validation(validation);
            } else if self.config.validation_sample_rate > 0.0 {
                let validation = self.validate_sample();
                result.merge_validation(validation);
            }
        }

        // Clear thread-local registry
        clear_query_registry();

        result.total_duration = start.elapsed();
        result
    }

    /// Run a single update cycle (for incremental testing).
    pub fn run_single_cycle(&mut self) -> FuzzResult {
        let start = Instant::now();
        let mut result = FuzzResult::default();

        set_query_registry(self.query_registry.clone());

        let updated = self.update_assets();
        result.update_cycles.push((0, updated.len()));

        self.execute_all_roots(&mut result);

        if self.config.full_validation_cycles {
            let validation = self.validate_all();
            result.merge_validation(validation);
        }

        clear_query_registry();

        result.total_duration = start.elapsed();
        result
    }

    /// Get the dependency tree.
    pub fn tree(&self) -> &DependencyTree {
        &self.tree
    }

    /// Get the query runtime.
    pub fn runtime(&self) -> &QueryRuntime {
        &self.runtime
    }

    /// Get the recorder (if recording is enabled).
    pub fn recorder(&self) -> Option<&Arc<FuzzEventRecorder>> {
        self.recorder.as_ref()
    }

    /// Export run record.
    pub fn export_run_record(&self, result: &FuzzResult) -> FuzzRunRecord {
        let events = self
            .recorder
            .as_ref()
            .map(|r| r.events())
            .unwrap_or_default();
        let stats = RunStats::from_events(&events, result);

        FuzzRunRecord {
            config: self.config.to_serializable(),
            seed: self.config.seed.unwrap_or(0),
            events,
            stats,
            metadata: RunMetadata::new(result.total_duration.as_millis() as u64),
        }
    }

    fn resolve_all_assets(&mut self) {
        for (&node_id, data) in &self.asset_values {
            self.runtime
                .resolve_asset(SyntheticAssetKey(node_id), data.clone());
        }
    }

    fn execute_all_roots(&self, result: &mut FuzzResult) {
        for &root_id in &self.tree.roots {
            if let Some(query) = self.query_registry.get(&root_id) {
                let start = Instant::now();

                match self.runtime.query(query.clone()) {
                    Ok(_output) => {
                        result.query_successes.push((root_id, start.elapsed()));
                    }
                    Err(e) => {
                        result.query_failures.push((root_id, e));
                    }
                }
            }
        }
    }

    fn update_assets(&mut self) -> Vec<NodeId> {
        let count = self.rng.gen_range(self.config.assets_per_update.clone());
        let leaves = self.tree.leaves.clone();

        if leaves.is_empty() {
            return vec![];
        }

        let selected: Vec<NodeId> = match &self.config.update_bias.clone() {
            UpdateBias::Uniform => leaves
                .choose_multiple(&mut self.rng, count as usize)
                .copied()
                .collect(),
            UpdateBias::Zipf { s } => self.select_zipf(&leaves, count as usize, *s),
            UpdateBias::HotSpot {
                hot_fraction,
                hot_probability,
            } => self.select_hotspot(&leaves, count as usize, *hot_fraction, *hot_probability),
            UpdateBias::RoundRobin => {
                let mut selected = vec![];
                for _ in 0..count {
                    selected.push(leaves[self.round_robin_index % leaves.len()]);
                    self.round_robin_index += 1;
                }
                selected
            }
        };

        for &node_id in &selected {
            let node = &self.tree.nodes[&node_id];
            if let NodeKind::Asset { data_size, .. } = &node.kind {
                // Increment version
                let version = self.asset_versions.entry(node_id).or_insert(0);
                *version += 1;

                // Generate new data
                let new_data = generate_asset_data(node_id, *data_size, *version, &mut self.rng);

                // Update stored value
                self.asset_values.insert(node_id, new_data.clone());

                // Resolve in runtime
                self.runtime
                    .resolve_asset(SyntheticAssetKey(node_id), new_data);
            }
        }

        selected
    }

    fn validate_all(&self) -> ValidationResult {
        let validator = Validator::new(&self.tree, &self.runtime);
        validator.validate_all(&self.asset_values, &self.query_registry)
    }

    fn validate_sample(&mut self) -> ValidationResult {
        let validator = Validator::new(&self.tree, &self.runtime);
        validator.validate_sample(
            &self.asset_values,
            &self.query_registry,
            self.config.validation_sample_rate,
            &mut self.rng,
        )
    }

    /// Select items using Zipf distribution.
    fn select_zipf(&mut self, items: &[NodeId], count: usize, s: f64) -> Vec<NodeId> {
        let n = items.len();
        if n == 0 || count == 0 {
            return vec![];
        }

        // Compute Zipf weights
        let weights: Vec<f64> = (1..=n).map(|k| 1.0 / (k as f64).powf(s)).collect();
        let total: f64 = weights.iter().sum();

        let mut selected = vec![];
        for _ in 0..count {
            let r: f64 = self.rng.gen::<f64>() * total;
            let mut cumulative = 0.0;
            for (i, &w) in weights.iter().enumerate() {
                cumulative += w;
                if r <= cumulative {
                    selected.push(items[i]);
                    break;
                }
            }
        }

        selected
    }

    /// Select items using hot-spot distribution.
    fn select_hotspot(
        &mut self,
        items: &[NodeId],
        count: usize,
        hot_fraction: f64,
        hot_probability: f64,
    ) -> Vec<NodeId> {
        let n = items.len();
        if n == 0 || count == 0 {
            return vec![];
        }

        let hot_count = ((n as f64) * hot_fraction).max(1.0) as usize;
        let hot_items = &items[..hot_count.min(n)];
        let cold_items = &items[hot_count.min(n)..];

        let mut selected = vec![];
        for _ in 0..count {
            if self.rng.gen::<f64>() < hot_probability && !hot_items.is_empty() {
                selected.push(*hot_items.choose(&mut self.rng).unwrap());
            } else if !cold_items.is_empty() {
                selected.push(*cold_items.choose(&mut self.rng).unwrap());
            } else if !hot_items.is_empty() {
                selected.push(*hot_items.choose(&mut self.rng).unwrap());
            }
        }

        selected
    }
}

impl Drop for FuzzRunner {
    fn drop(&mut self) {
        // Ensure registry is cleared even if run() wasn't called
        clear_query_registry();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::TreeShape;

    #[test]
    fn test_basic_run() {
        let config = FuzzConfig::minimal()
            .with_depth(3)
            .with_asset_count(4)
            .with_shape(TreeShape::Binary)
            .with_update_cycles(5)
            .with_seed(42);

        let mut runner = FuzzRunner::new(config);
        let result = runner.run();

        assert!(result.is_success(), "Run should succeed: {:?}", result);
        assert_eq!(result.update_cycles.len(), 5);
    }

    #[test]
    fn test_determinism() {
        let config = FuzzConfig::minimal()
            .with_depth(4)
            .with_asset_count(8)
            .with_shape(TreeShape::Binary)
            .with_update_cycles(10)
            .with_seed(12345);

        let mut runner1 = FuzzRunner::new(config.clone());
        let result1 = runner1.run();

        let mut runner2 = FuzzRunner::new(config);
        let result2 = runner2.run();

        assert_eq!(result1.query_successes.len(), result2.query_successes.len());
        assert_eq!(result1.update_cycles, result2.update_cycles);
    }

    #[test]
    fn test_with_recording() {
        let config = FuzzConfig::minimal()
            .with_depth(3)
            .with_asset_count(4)
            .with_recording(true)
            .with_update_cycles(3);

        let mut runner = FuzzRunner::new(config);
        let result = runner.run();

        assert!(result.is_success());

        let recorder = runner.recorder().expect("Recorder should be present");
        assert!(!recorder.is_empty(), "Should have recorded events");
    }
}
