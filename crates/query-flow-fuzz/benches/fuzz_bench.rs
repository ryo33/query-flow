//! Criterion benchmarks for query-flow performance testing.

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use query_flow_fuzz::{FuzzConfig, FuzzRunner, LogScale, Presets, TreeShape, UpdateBias};

fn bench_tree_depth(c: &mut Criterion) {
    let mut group = c.benchmark_group("tree_depth");

    // Use a fixed asset count to isolate the effect of tree depth.
    // Previously, 2^(depth-1) caused overflow at depth=100, resulting in asset_count=0.
    let asset_count = 32u32;
    let update_cycles = 20u32;

    for depth in LogScale::new(10, 0, 2).values() {
        let depth = (depth as u32).max(2); // Ensure depth >= 2 for meaningful tree
        let config = FuzzConfig::minimal()
            .with_depth(depth)
            .with_shape(TreeShape::Binary)
            .with_asset_count(asset_count)
            .with_update_cycles(update_cycles)
            .with_seed(42);

        // Throughput based on total update operations performed
        group.throughput(Throughput::Elements((asset_count * update_cycles) as u64));
        group.bench_with_input(BenchmarkId::from_parameter(depth), &config, |b, config| {
            b.iter_batched(
                || FuzzRunner::new(config.clone()),
                |mut runner| runner.run(),
                criterion::BatchSize::SmallInput,
            );
        });
    }

    group.finish();
}

fn bench_tree_shape(c: &mut Criterion) {
    let mut group = c.benchmark_group("tree_shape");

    // Use consistent asset_count for fair comparison across shapes.
    // Note: LinkedList ignores asset_count and always has 1 leaf (chain structure).
    let asset_count = 32u32;

    let shapes = [
        ("linked_list", TreeShape::LinkedList),
        ("binary", TreeShape::Binary),
        (
            "nary4",
            TreeShape::NAry {
                branching_factor: 4,
            },
        ),
        (
            "complete_nary4",
            TreeShape::CompleteNAry {
                branching_factor: 4,
            },
        ),
        (
            "random_dag",
            TreeShape::RandomDag {
                expected_fan_out: 3.0,
            },
        ),
    ];

    for (name, shape) in shapes {
        let config = FuzzConfig::minimal()
            .with_depth(5)
            .with_shape(shape)
            .with_asset_count(asset_count)
            .with_update_cycles(20)
            .with_seed(42);

        group.bench_with_input(BenchmarkId::new("shape", name), &config, |b, config| {
            b.iter_batched(
                || FuzzRunner::new(config.clone()),
                |mut runner| runner.run(),
                criterion::BatchSize::SmallInput,
            );
        });
    }

    group.finish();
}

fn bench_update_pattern(c: &mut Criterion) {
    let mut group = c.benchmark_group("update_pattern");

    let biases = [
        ("uniform", UpdateBias::Uniform),
        ("zipf_1.0", UpdateBias::Zipf { s: 1.0 }),
        ("zipf_2.0", UpdateBias::Zipf { s: 2.0 }),
        (
            "hotspot_10",
            UpdateBias::HotSpot {
                hot_fraction: 0.1,
                hot_probability: 0.9,
            },
        ),
        ("round_robin", UpdateBias::RoundRobin),
    ];

    for (name, bias) in biases {
        let config = FuzzConfig::minimal()
            .with_depth(6)
            .with_shape(TreeShape::Binary)
            .with_asset_count(32)
            .with_update_bias(bias)
            .with_update_cycles(50)
            .with_seed(42);

        group.bench_with_input(BenchmarkId::new("bias", name), &config, |b, config| {
            b.iter_batched(
                || FuzzRunner::new(config.clone()),
                |mut runner| runner.run(),
                criterion::BatchSize::SmallInput,
            );
        });
    }

    group.finish();
}

fn bench_asset_count(c: &mut Criterion) {
    let mut group = c.benchmark_group("asset_count");

    for count in LogScale::new(2, 2, 6).values() {
        // 4, 8, 16, 32, 64
        let count = count as u32;
        let config = FuzzConfig::minimal()
            .with_depth(5)
            .with_shape(TreeShape::Binary)
            .with_asset_count(count)
            .with_update_cycles(20)
            .with_seed(42);

        group.throughput(Throughput::Elements(count as u64));
        group.bench_with_input(BenchmarkId::from_parameter(count), &config, |b, config| {
            b.iter_batched(
                || FuzzRunner::new(config.clone()),
                |mut runner| runner.run(),
                criterion::BatchSize::SmallInput,
            );
        });
    }

    group.finish();
}

fn bench_update_cycles(c: &mut Criterion) {
    let mut group = c.benchmark_group("update_cycles");

    for cycles in [10, 50, 100, 200] {
        let config = FuzzConfig::minimal()
            .with_depth(5)
            .with_shape(TreeShape::Binary)
            .with_asset_count(16)
            .with_update_cycles(cycles)
            .with_seed(42);

        group.throughput(Throughput::Elements(cycles as u64));
        group.bench_with_input(BenchmarkId::from_parameter(cycles), &config, |b, config| {
            b.iter_batched(
                || FuzzRunner::new(config.clone()),
                |mut runner| runner.run(),
                criterion::BatchSize::SmallInput,
            );
        });
    }

    group.finish();
}

fn bench_presets(c: &mut Criterion) {
    let mut group = c.benchmark_group("presets");

    // Only benchmark quick presets
    let quick_presets = [
        ("quick", Presets::quick()),
        (
            "early_cutoff",
            Presets::early_cutoff().with_update_cycles(20),
        ),
    ];

    for (name, config) in quick_presets {
        let config = config.with_seed(42);
        group.bench_with_input(BenchmarkId::new("preset", name), &config, |b, config| {
            b.iter_batched(
                || FuzzRunner::new(config.clone()),
                |mut runner| runner.run(),
                criterion::BatchSize::SmallInput,
            );
        });
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_tree_depth,
    bench_tree_shape,
    bench_update_pattern,
    bench_asset_count,
    bench_update_cycles,
    bench_presets,
);

criterion_main!(benches);
