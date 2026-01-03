//! Test execution engine.

use crate::config::{FuzzConfig, MutationKind, UpdateBias};
use crate::generator::{
    build_query_registry, clear_query_registry, generate_asset_data, set_query_registry,
    DependencyTree, NodeId, NodeKind, QueryRegistry, SyntheticAssetKey, SyntheticQuery,
    TreeGenerator,
};
use crate::recorder::{FuzzEventRecorder, FuzzRunRecord, RunMetadata, RunStats};
use crate::validator::{ValidationFailure, ValidationResult, Validator};
use parking_lot::Mutex;
use query_flow::{DurabilityLevel, QueryError};
use query_flow_inspector::{EventSinkTracer, NullSink};
use rand::prelude::*;
use rand::rngs::SmallRng;
use std::collections::{HashMap, HashSet};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

type FuzzRuntime = query_flow::QueryRuntime<EventSinkTracer>;

/// Result of a fuzz test run.
#[derive(Debug, Default, Clone)]
pub struct FuzzResult {
    pub query_successes: Vec<(NodeId, Duration)>,
    pub query_failures: Vec<(NodeId, QueryError)>,
    pub validation_successes: u32,
    pub validation_failures: Vec<ValidationFailure>,
    pub update_cycles: Vec<(u32, usize)>, // (cycle, assets_updated)
    pub total_duration: Duration,
}

impl FuzzResult {
    /// Check if the test succeeded (no unexpected errors).
    /// Note: Suspend errors are expected when using RemoveAsset/InvalidateAsset mutations.
    pub fn is_success(&self) -> bool {
        self.validation_failures.is_empty() && self.unexpected_failures().is_empty()
    }

    /// Get failures that are not expected (excludes Suspend which is normal for some mutations).
    pub fn unexpected_failures(&self) -> Vec<&(NodeId, QueryError)> {
        self.query_failures
            .iter()
            .filter(|(_, e)| !matches!(e, QueryError::Suspend { .. }))
            .collect()
    }

    /// Check if there were any panics (for concurrent testing).
    pub fn has_panic(&self) -> bool {
        self.query_failures
            .iter()
            .any(|(_, e)| matches!(e, QueryError::Cancelled))
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
    rng: Mutex<SmallRng>,
    runtime: FuzzRuntime,
    tree: DependencyTree,
    /// Current asset values (for validation).
    asset_values: Mutex<HashMap<NodeId, Vec<u8>>>,
    /// Asset version counters (for generating unique data).
    asset_versions: Mutex<HashMap<NodeId, u64>>,
    /// Set of currently removed assets (need re-resolve before query).
    removed_assets: Mutex<HashSet<NodeId>>,
    /// Query registry for looking up queries by ID.
    query_registry: Arc<QueryRegistry>,
    /// Event recorder.
    recorder: Option<Arc<FuzzEventRecorder>>,
    /// Round-robin index for RoundRobin update bias.
    round_robin_index: AtomicUsize,
}

impl FuzzRunner {
    pub fn new(config: FuzzConfig) -> Self {
        let seed = config.seed.unwrap_or_else(rand::random);
        let mut rng = SmallRng::seed_from_u64(seed);

        // Generate the dependency tree
        let mut generator = TreeGenerator::new(config.clone(), SmallRng::seed_from_u64(seed));
        let tree = generator.generate();

        // Create runtime with tracer (FuzzEventRecorder or NullSink)
        let (runtime, recorder) = if config.record_events {
            let recorder = Arc::new(FuzzEventRecorder::new());
            let tracer = EventSinkTracer::new(recorder.clone());
            (FuzzRuntime::with_tracer(tracer), Some(recorder))
        } else {
            let tracer = EventSinkTracer::new(Arc::new(NullSink));
            (FuzzRuntime::with_tracer(tracer), None)
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
            rng: Mutex::new(rng),
            runtime,
            tree,
            asset_values: Mutex::new(asset_values),
            asset_versions: Mutex::new(asset_versions),
            removed_assets: Mutex::new(HashSet::new()),
            query_registry,
            recorder,
            round_robin_index: AtomicUsize::new(0),
        }
    }

    /// Run the complete fuzz test.
    pub fn run(&mut self) -> FuzzResult {
        let start = Instant::now();
        let result = Arc::new(Mutex::new(FuzzResult::default()));

        // Set up thread-local query registry
        set_query_registry(self.query_registry.clone());

        // Initial population: resolve all assets
        self.resolve_all_assets();

        // Initial query execution
        self.execute_all_roots(&result);

        // Validate initial state
        if self.config.full_validation_cycles {
            let validation = self.validate_all();
            result.lock().merge_validation(validation);
        }

        // Run update cycles
        if self.config.threads > 1 {
            self.run_concurrent(&result);
        } else {
            self.run_sequential(&result);
        }

        // Clear thread-local registry
        clear_query_registry();

        let mut final_result = match Arc::try_unwrap(result) {
            Ok(mutex) => mutex.into_inner(),
            Err(arc) => arc.lock().clone(),
        };
        final_result.total_duration = start.elapsed();
        final_result
    }

    /// Run update cycles sequentially (single-threaded).
    fn run_sequential(&self, result: &Arc<Mutex<FuzzResult>>) {
        for cycle in 0..self.config.update_cycles {
            // Mutate some assets/queries
            let mutated = self.mutate();
            result.lock().update_cycles.push((cycle, mutated));

            // Re-query roots
            self.execute_all_roots(result);

            // Validate
            if self.config.full_validation_cycles {
                let validation = self.validate_all();
                result.lock().merge_validation(validation);
            } else if self.config.validation_sample_rate > 0.0 {
                let validation = self.validate_sample();
                result.lock().merge_validation(validation);
            }
        }
    }

    /// Run update cycles concurrently (multi-threaded).
    fn run_concurrent(&self, result: &Arc<Mutex<FuzzResult>>) {
        // Install rayon thread-local registry on worker threads
        let registry = self.query_registry.clone();

        // Configure thread pool
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(self.config.threads)
            .build()
            .expect("Failed to create thread pool");

        let mutations_done = AtomicUsize::new(0);
        let should_stop = AtomicBool::new(false);
        let total_mutations = self.config.update_cycles as usize;

        pool.scope(|s| {
            // Mutation threads
            for _ in 0..self.config.threads.min(4) {
                let registry = registry.clone();
                let mutations_done = &mutations_done;
                let should_stop = &should_stop;
                let result = result.clone();

                s.spawn(move |_| {
                    set_query_registry(registry);

                    loop {
                        let cycle = mutations_done.fetch_add(1, Ordering::SeqCst);
                        if cycle >= total_mutations {
                            mutations_done.fetch_sub(1, Ordering::SeqCst);
                            break;
                        }

                        let mutated = self.mutate();
                        result.lock().update_cycles.push((cycle as u32, mutated));

                        if should_stop.load(Ordering::Relaxed) {
                            break;
                        }
                    }

                    clear_query_registry();
                });
            }

            // Query threads - run queries concurrently with mutations
            for _ in 0..self.config.threads {
                let registry = registry.clone();
                let should_stop = &should_stop;
                let mutations_done = &mutations_done;
                let result = result.clone();

                s.spawn(move |_| {
                    set_query_registry(registry);

                    // Keep querying while mutations are happening
                    while mutations_done.load(Ordering::SeqCst) < total_mutations
                        && !should_stop.load(Ordering::Relaxed)
                    {
                        self.execute_all_roots(&result);
                    }

                    // Final query after all mutations
                    self.execute_all_roots(&result);

                    clear_query_registry();
                });
            }
        });
    }

    /// Run a single update cycle (for incremental testing).
    pub fn run_single_cycle(&mut self) -> FuzzResult {
        let start = Instant::now();
        let result = Arc::new(Mutex::new(FuzzResult::default()));

        set_query_registry(self.query_registry.clone());

        let mutated = self.mutate();
        result.lock().update_cycles.push((0, mutated));

        self.execute_all_roots(&result);

        if self.config.full_validation_cycles {
            let validation = self.validate_all();
            result.lock().merge_validation(validation);
        }

        clear_query_registry();

        let mut final_result = match Arc::try_unwrap(result) {
            Ok(mutex) => mutex.into_inner(),
            Err(arc) => arc.lock().clone(),
        };
        final_result.total_duration = start.elapsed();
        final_result
    }

    /// Get the dependency tree.
    pub fn tree(&self) -> &DependencyTree {
        &self.tree
    }

    /// Get the query runtime.
    pub fn runtime(&self) -> &FuzzRuntime {
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

    fn resolve_all_assets(&self) {
        let asset_values = self.asset_values.lock();
        for (&node_id, data) in asset_values.iter() {
            self.runtime.resolve_asset(
                SyntheticAssetKey(node_id),
                data.clone(),
                DurabilityLevel::Volatile,
            );
        }
    }

    fn execute_all_roots(&self, result: &Arc<Mutex<FuzzResult>>) {
        for &root_id in &self.tree.roots {
            if let Some(query) = self.query_registry.get(&root_id) {
                let start = Instant::now();

                match self.runtime.query(query.clone()) {
                    Ok(_output) => {
                        result
                            .lock()
                            .query_successes
                            .push((root_id, start.elapsed()));
                    }
                    Err(QueryError::Suspend { .. }) => {
                        // Expected when assets are removed/invalidated
                    }
                    Err(e) => {
                        result.lock().query_failures.push((root_id, e));
                    }
                }
            }
        }
    }

    /// Perform mutations based on the configured mutation kind.
    /// Returns the number of mutations performed.
    fn mutate(&self) -> usize {
        // First, re-resolve any previously removed assets
        self.re_resolve_removed_assets();

        let count = {
            let mut rng = self.rng.lock();
            rng.gen_range(self.config.assets_per_update.clone()) as usize
        };

        match &self.config.mutation_kind {
            MutationKind::Update => self.mutate_update_assets(count),
            MutationKind::RemoveAsset => self.mutate_remove_assets(count),
            MutationKind::InvalidateAsset => self.mutate_invalidate_assets(count),
            MutationKind::RemoveQuery => self.mutate_remove_queries(count),
            MutationKind::InvalidateQuery => self.mutate_invalidate_queries(count),
            MutationKind::Mixed {
                remove_asset_prob,
                invalidate_asset_prob,
                remove_query_prob,
                invalidate_query_prob,
            } => self.mutate_mixed(
                count,
                *remove_asset_prob,
                *invalidate_asset_prob,
                *remove_query_prob,
                *invalidate_query_prob,
            ),
        }
    }

    /// Re-resolve any assets that were previously removed.
    fn re_resolve_removed_assets(&self) {
        let mut removed = self.removed_assets.lock();
        if removed.is_empty() {
            return;
        }

        let mut rng = self.rng.lock();
        let mut asset_values = self.asset_values.lock();
        let mut asset_versions = self.asset_versions.lock();

        for &node_id in removed.iter() {
            let node = &self.tree.nodes[&node_id];
            if let NodeKind::Asset { data_size, .. } = &node.kind {
                let version = asset_versions.entry(node_id).or_insert(0);
                *version += 1;

                let new_data = generate_asset_data(node_id, *data_size, *version, &mut *rng);
                asset_values.insert(node_id, new_data.clone());

                self.runtime.resolve_asset(
                    SyntheticAssetKey(node_id),
                    new_data,
                    DurabilityLevel::Volatile,
                );
            }
        }

        removed.clear();
    }

    /// Update asset values (the original behavior).
    fn mutate_update_assets(&self, count: usize) -> usize {
        let selected = self.select_assets(count);

        let mut rng = self.rng.lock();
        let mut asset_values = self.asset_values.lock();
        let mut asset_versions = self.asset_versions.lock();

        for &node_id in &selected {
            let node = &self.tree.nodes[&node_id];
            if let NodeKind::Asset { data_size, .. } = &node.kind {
                let version = asset_versions.entry(node_id).or_insert(0);
                *version += 1;

                let new_data = generate_asset_data(node_id, *data_size, *version, &mut *rng);
                asset_values.insert(node_id, new_data.clone());

                self.runtime.resolve_asset(
                    SyntheticAssetKey(node_id),
                    new_data,
                    DurabilityLevel::Volatile,
                );
            }
        }

        selected.len()
    }

    /// Remove assets from cache.
    fn mutate_remove_assets(&self, count: usize) -> usize {
        let selected = self.select_assets(count);

        let mut removed = self.removed_assets.lock();
        for &node_id in &selected {
            self.runtime.remove_asset(&SyntheticAssetKey(node_id));
            removed.insert(node_id);
        }

        selected.len()
    }

    /// Invalidate assets.
    fn mutate_invalidate_assets(&self, count: usize) -> usize {
        let selected = self.select_assets(count);

        let mut removed = self.removed_assets.lock();
        for &node_id in &selected {
            self.runtime.invalidate_asset(&SyntheticAssetKey(node_id));
            removed.insert(node_id);
        }

        selected.len()
    }

    /// Remove queries from cache.
    fn mutate_remove_queries(&self, count: usize) -> usize {
        let queries = self.select_queries(count);

        for query in &queries {
            self.runtime.remove_query::<SyntheticQuery>(&query.node_id);
        }

        queries.len()
    }

    /// Invalidate queries.
    fn mutate_invalidate_queries(&self, count: usize) -> usize {
        let queries = self.select_queries(count);

        for query in &queries {
            self.runtime.invalidate::<SyntheticQuery>(&query.node_id);
        }

        queries.len()
    }

    /// Mixed mutations with configurable probabilities.
    fn mutate_mixed(
        &self,
        count: usize,
        remove_asset_prob: f64,
        invalidate_asset_prob: f64,
        remove_query_prob: f64,
        invalidate_query_prob: f64,
    ) -> usize {
        let mut total = 0;
        let mut rng = self.rng.lock();

        for _ in 0..count {
            let r: f64 = rng.gen();

            if r < remove_asset_prob {
                drop(rng);
                total += self.mutate_remove_assets(1);
                rng = self.rng.lock();
            } else if r < remove_asset_prob + invalidate_asset_prob {
                drop(rng);
                total += self.mutate_invalidate_assets(1);
                rng = self.rng.lock();
            } else if r < remove_asset_prob + invalidate_asset_prob + remove_query_prob {
                drop(rng);
                total += self.mutate_remove_queries(1);
                rng = self.rng.lock();
            } else if r < remove_asset_prob
                + invalidate_asset_prob
                + remove_query_prob
                + invalidate_query_prob
            {
                drop(rng);
                total += self.mutate_invalidate_queries(1);
                rng = self.rng.lock();
            } else {
                drop(rng);
                total += self.mutate_update_assets(1);
                rng = self.rng.lock();
            }
        }

        total
    }

    /// Select assets based on the configured update bias.
    fn select_assets(&self, count: usize) -> Vec<NodeId> {
        let leaves = &self.tree.leaves;

        if leaves.is_empty() || count == 0 {
            return vec![];
        }

        let mut rng = self.rng.lock();

        match &self.config.update_bias {
            UpdateBias::Uniform => leaves
                .choose_multiple(&mut *rng, count.min(leaves.len()))
                .copied()
                .collect(),
            UpdateBias::Zipf { s } => self.select_zipf_with_rng(leaves, count, *s, &mut *rng),
            UpdateBias::HotSpot {
                hot_fraction,
                hot_probability,
            } => self.select_hotspot_with_rng(
                leaves,
                count,
                *hot_fraction,
                *hot_probability,
                &mut *rng,
            ),
            UpdateBias::RoundRobin => {
                let mut selected = vec![];
                for _ in 0..count {
                    let idx = self.round_robin_index.fetch_add(1, Ordering::SeqCst);
                    selected.push(leaves[idx % leaves.len()]);
                }
                selected
            }
        }
    }

    /// Select queries for mutation.
    fn select_queries(&self, count: usize) -> Vec<SyntheticQuery> {
        let query_nodes: Vec<NodeId> = self
            .tree
            .nodes
            .iter()
            .filter(|(_, node)| node.kind.is_query())
            .map(|(id, _)| *id)
            .collect();

        if query_nodes.is_empty() || count == 0 {
            return vec![];
        }

        let mut rng = self.rng.lock();
        let selected: Vec<NodeId> = query_nodes
            .choose_multiple(&mut *rng, count.min(query_nodes.len()))
            .copied()
            .collect();

        selected
            .into_iter()
            .filter_map(|id| self.query_registry.get(&id).cloned())
            .collect()
    }

    fn validate_all(&self) -> ValidationResult {
        let validator = Validator::new(&self.tree, &self.runtime);
        let asset_values = self.asset_values.lock();
        validator.validate_all(&asset_values, &self.query_registry)
    }

    fn validate_sample(&self) -> ValidationResult {
        let validator = Validator::new(&self.tree, &self.runtime);
        let asset_values = self.asset_values.lock();
        let mut rng = self.rng.lock();
        validator.validate_sample(
            &asset_values,
            &self.query_registry,
            self.config.validation_sample_rate,
            &mut *rng,
        )
    }

    /// Select items using Zipf distribution.
    fn select_zipf_with_rng<R: Rng>(
        &self,
        items: &[NodeId],
        count: usize,
        s: f64,
        rng: &mut R,
    ) -> Vec<NodeId> {
        let n = items.len();
        if n == 0 || count == 0 {
            return vec![];
        }

        // Compute Zipf weights
        let weights: Vec<f64> = (1..=n).map(|k| 1.0 / (k as f64).powf(s)).collect();
        let total: f64 = weights.iter().sum();

        let mut selected = vec![];
        for _ in 0..count {
            let r: f64 = rng.gen::<f64>() * total;
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
    fn select_hotspot_with_rng<R: Rng>(
        &self,
        items: &[NodeId],
        count: usize,
        hot_fraction: f64,
        hot_probability: f64,
        rng: &mut R,
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
            if rng.gen::<f64>() < hot_probability && !hot_items.is_empty() {
                selected.push(*hot_items.choose(rng).unwrap());
            } else if !cold_items.is_empty() {
                selected.push(*cold_items.choose(rng).unwrap());
            } else if !hot_items.is_empty() {
                selected.push(*hot_items.choose(rng).unwrap());
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

    #[test]
    fn test_remove_asset_mutation() {
        let config = FuzzConfig::minimal()
            .with_depth(3)
            .with_asset_count(4)
            .with_shape(TreeShape::Binary)
            .with_mutation_kind(MutationKind::RemoveAsset)
            .with_update_cycles(10)
            .with_seed(42);

        let mut runner = FuzzRunner::new(config);
        let result = runner.run();

        // With RemoveAsset, we expect some Suspend errors which are normal
        assert!(
            result.validation_failures.is_empty(),
            "Should have no validation failures: {:?}",
            result.validation_failures
        );
        assert!(
            result.unexpected_failures().is_empty(),
            "Should have no unexpected failures: {:?}",
            result.unexpected_failures()
        );
    }

    #[test]
    fn test_remove_query_mutation() {
        let config = FuzzConfig::minimal()
            .with_depth(3)
            .with_asset_count(4)
            .with_shape(TreeShape::Binary)
            .with_mutation_kind(MutationKind::RemoveQuery)
            .with_update_cycles(10)
            .with_seed(42);

        let mut runner = FuzzRunner::new(config);
        let result = runner.run();

        assert!(result.is_success(), "Run should succeed: {:?}", result);
    }

    #[test]
    fn test_mixed_mutations() {
        let config = FuzzConfig::minimal()
            .with_depth(4)
            .with_asset_count(8)
            .with_shape(TreeShape::Binary)
            .with_mutation_kind(MutationKind::Mixed {
                remove_asset_prob: 0.1,
                invalidate_asset_prob: 0.1,
                remove_query_prob: 0.05,
                invalidate_query_prob: 0.05,
            })
            .with_update_cycles(50)
            .with_seed(42);

        let mut runner = FuzzRunner::new(config);
        let result = runner.run();

        assert!(
            result.validation_failures.is_empty(),
            "Should have no validation failures"
        );
        assert!(
            result.unexpected_failures().is_empty(),
            "Should have no unexpected failures"
        );
    }

    #[test]
    fn test_concurrent_execution() {
        let config = FuzzConfig::minimal()
            .with_depth(4)
            .with_asset_count(8)
            .with_shape(TreeShape::Binary)
            .with_threads(4)
            .with_update_cycles(20)
            .with_seed(42);

        let mut runner = FuzzRunner::new(config);
        let result = runner.run();

        assert!(result.is_success(), "Run should succeed: {:?}", result);
        assert!(!result.has_panic(), "Should not have any panics");
    }

    #[test]
    fn test_concurrent_with_mutations() {
        let config = FuzzConfig::minimal()
            .with_depth(4)
            .with_asset_count(8)
            .with_shape(TreeShape::Binary)
            .with_threads(4)
            .with_mutation_kind(MutationKind::Mixed {
                remove_asset_prob: 0.1,
                invalidate_asset_prob: 0.1,
                remove_query_prob: 0.05,
                invalidate_query_prob: 0.05,
            })
            .with_update_cycles(30)
            .with_seed(42);

        let mut runner = FuzzRunner::new(config);
        let result = runner.run();

        // Concurrent execution with mutations - should not panic or deadlock
        assert!(!result.has_panic(), "Should not have any panics");
        assert!(
            result.validation_failures.is_empty(),
            "Should have no validation failures"
        );
    }
}
