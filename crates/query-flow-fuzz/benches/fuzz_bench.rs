//! Criterion benchmarks for query-flow performance testing.

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use query_flow_fuzz::{FuzzConfig, FuzzRunner, LogScale, Presets, TreeShape, UpdateBias};

fn bench_tree_depth(c: &mut Criterion) {
    let mut group = c.benchmark_group("tree_depth");

    for depth in LogScale::new(10, 0, 2).values() {
        let depth = depth as u32;
        let config = FuzzConfig::minimal()
            .with_depth(depth)
            .with_shape(TreeShape::Binary)
            .with_asset_count(2u32.pow(depth.saturating_sub(1)).min(64))
            .with_update_cycles(20)
            .with_seed(42);

        group.throughput(Throughput::Elements(depth as u64));
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

    let shapes = [
        ("linked_list", TreeShape::LinkedList, 1),
        ("binary", TreeShape::Binary, 16),
        (
            "nary4",
            TreeShape::NAry {
                branching_factor: 4,
            },
            64,
        ),
        (
            "complete_nary4",
            TreeShape::CompleteNAry {
                branching_factor: 4,
            },
            64,
        ),
        (
            "random_dag",
            TreeShape::RandomDag {
                expected_fan_out: 3.0,
            },
            32,
        ),
    ];

    for (name, shape, asset_count) in shapes {
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
