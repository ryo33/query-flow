//! Predefined configurations for common test scenarios.

use crate::config::{DataSize, FuzzConfig, MutationKind, TimeDistribution, TreeShape, UpdateBias};

/// Collection of preset configurations.
pub struct Presets;

impl Presets {
    /// Quick sanity check (CI-friendly, runs fast).
    pub fn quick() -> FuzzConfig {
        FuzzConfig::minimal()
            .with_depth(4)
            .with_asset_count(8)
            .with_shape(TreeShape::Binary)
            .with_update_cycles(10)
    }

    /// Standard test suite.
    pub fn standard() -> FuzzConfig {
        FuzzConfig::minimal()
            .with_depth(8)
            .with_asset_count(50)
            .with_shape(TreeShape::NAry {
                branching_factor: 3,
            })
            .with_update_cycles(100)
            .with_validation_sample_rate(0.1)
    }

    /// Stress test for deep dependency chains.
    pub fn deep_chain() -> FuzzConfig {
        FuzzConfig::minimal()
            .with_depth(50)
            .with_asset_count(1)
            .with_shape(TreeShape::LinkedList)
            .with_update_cycles(100)
    }

    /// Stress test for wide dependency graphs.
    pub fn wide_tree() -> FuzzConfig {
        FuzzConfig::minimal()
            .with_depth(4)
            .with_asset_count(256)
            .with_shape(TreeShape::CompleteNAry {
                branching_factor: 4,
            })
            .with_update_cycles(100)
    }

    /// Test early cutoff effectiveness with hot-spot updates.
    pub fn early_cutoff() -> FuzzConfig {
        FuzzConfig::minimal()
            .with_depth(6)
            .with_asset_count(32)
            .with_shape(TreeShape::Binary)
            .with_update_bias(UpdateBias::HotSpot {
                hot_fraction: 0.1,
                hot_probability: 0.9,
            })
            .with_update_cycles(200)
    }

    /// Test with Zipf-distributed updates.
    pub fn zipf_updates() -> FuzzConfig {
        FuzzConfig::minimal()
            .with_depth(6)
            .with_asset_count(64)
            .with_shape(TreeShape::NAry {
                branching_factor: 4,
            })
            .with_update_bias(UpdateBias::Zipf { s: 1.0 })
            .with_update_cycles(200)
    }

    /// Configuration with larger data sizes.
    pub fn large_data() -> FuzzConfig {
        FuzzConfig::minimal()
            .with_depth(5)
            .with_asset_count(32)
            .with_shape(TreeShape::Binary)
            .with_output_size(DataSize::range(1024, 4096))
            .with_asset_size(DataSize::range(512, 2048))
            .with_update_cycles(50)
    }

    /// Random DAG structure.
    pub fn random_dag() -> FuzzConfig {
        FuzzConfig::minimal()
            .with_depth(6)
            .with_node_count(100)
            .with_asset_count(30)
            .with_shape(TreeShape::RandomDag {
                expected_fan_out: 3.0,
            })
            .with_update_cycles(100)
    }

    /// Batch updates (many assets updated at once).
    pub fn batch_updates() -> FuzzConfig {
        FuzzConfig::minimal()
            .with_depth(5)
            .with_asset_count(64)
            .with_shape(TreeShape::Binary)
            .with_assets_per_update(8..=16)
            .with_update_cycles(50)
    }

    /// Benchmark configuration with realistic timing recorded.
    pub fn benchmark_realistic() -> FuzzConfig {
        FuzzConfig::minimal()
            .with_depth(6)
            .with_asset_count(64)
            .with_shape(TreeShape::NAry {
                branching_factor: 4,
            })
            .with_query_time(TimeDistribution::range_us(10, 1000))
            .with_asset_resolve_time(TimeDistribution::microseconds(100))
            .with_output_size(DataSize::range(64, 1024))
            .with_update_cycles(50)
            .with_recording(true)
    }

    /// Test with asset removal mutations.
    pub fn remove_asset() -> FuzzConfig {
        FuzzConfig::minimal()
            .with_depth(5)
            .with_asset_count(32)
            .with_shape(TreeShape::Binary)
            .with_mutation_kind(MutationKind::RemoveAsset)
            .with_update_cycles(50)
    }

    /// Test with query removal mutations.
    pub fn remove_query() -> FuzzConfig {
        FuzzConfig::minimal()
            .with_depth(5)
            .with_asset_count(32)
            .with_shape(TreeShape::Binary)
            .with_mutation_kind(MutationKind::RemoveQuery)
            .with_update_cycles(50)
    }

    /// Test with mixed mutations (update, remove, invalidate).
    pub fn mixed_mutations() -> FuzzConfig {
        FuzzConfig::minimal()
            .with_depth(5)
            .with_asset_count(32)
            .with_shape(TreeShape::Binary)
            .with_mutation_kind(MutationKind::Mixed {
                remove_asset_prob: 0.1,
                invalidate_asset_prob: 0.1,
                remove_query_prob: 0.05,
                invalidate_query_prob: 0.05,
            })
            .with_update_cycles(100)
    }

    /// Concurrent execution stress test.
    pub fn concurrent() -> FuzzConfig {
        FuzzConfig::minimal()
            .with_depth(5)
            .with_asset_count(32)
            .with_shape(TreeShape::Binary)
            .with_threads(4)
            .with_update_cycles(50)
    }

    /// Heavy concurrent execution with mixed mutations.
    pub fn concurrent_stress() -> FuzzConfig {
        FuzzConfig::minimal()
            .with_depth(6)
            .with_asset_count(64)
            .with_shape(TreeShape::NAry {
                branching_factor: 4,
            })
            .with_threads(8)
            .with_mutation_kind(MutationKind::Mixed {
                remove_asset_prob: 0.1,
                invalidate_asset_prob: 0.1,
                remove_query_prob: 0.05,
                invalidate_query_prob: 0.05,
            })
            .with_update_cycles(100)
    }

    /// All presets as a list for iteration.
    pub fn all() -> Vec<(&'static str, FuzzConfig)> {
        vec![
            ("quick", Self::quick()),
            ("standard", Self::standard()),
            ("deep_chain", Self::deep_chain()),
            ("wide_tree", Self::wide_tree()),
            ("early_cutoff", Self::early_cutoff()),
            ("zipf_updates", Self::zipf_updates()),
            ("large_data", Self::large_data()),
            ("random_dag", Self::random_dag()),
            ("batch_updates", Self::batch_updates()),
            ("benchmark_realistic", Self::benchmark_realistic()),
            ("remove_asset", Self::remove_asset()),
            ("remove_query", Self::remove_query()),
            ("mixed_mutations", Self::mixed_mutations()),
            ("concurrent", Self::concurrent()),
            ("concurrent_stress", Self::concurrent_stress()),
        ]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::runner::FuzzRunner;

    #[test]
    fn test_all_presets_run() {
        for (name, config) in Presets::all() {
            // Use smaller update cycles for test speed
            let config = config.with_update_cycles(5).with_seed(42);
            let mut runner = FuzzRunner::new(config);
            let result = runner.run();
            assert!(
                result.is_success(),
                "Preset '{}' should succeed: {:?}",
                name,
                result
            );
        }
    }
}
