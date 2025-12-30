//! Parameter sweep binary for fuzzy testing.

use clap::Parser;
use query_flow_fuzz::{FuzzConfig, FuzzRunner, LogScale, Presets, TreeShape, UpdateBias};
use std::path::{Path, PathBuf};

#[derive(Parser, Debug)]
#[command(name = "sweep")]
#[command(about = "Run parameter sweeps for query-flow fuzzy testing")]
struct Args {
    /// Output directory for results
    #[arg(short, long, default_value = "./tmp/fuzz_results")]
    output_dir: PathBuf,

    /// Random seed for reproducibility
    #[arg(short, long)]
    seed: Option<u64>,

    /// Run only presets (skip parameter sweep)
    #[arg(long)]
    presets_only: bool,

    /// Run a quick sweep (fewer parameter combinations)
    #[arg(long)]
    quick: bool,

    /// Specific preset to run
    #[arg(long)]
    preset: Option<String>,

    /// Tree depth filter (only run this depth)
    #[arg(long)]
    depth: Option<u32>,

    /// Tree shape filter (linked_list, binary, nary, complete_nary, random_dag)
    #[arg(long)]
    shape: Option<String>,

    /// Enable verbose output
    #[arg(short, long)]
    verbose: bool,
}

fn main() {
    let args = Args::parse();

    // Create output directory
    if let Err(e) = std::fs::create_dir_all(&args.output_dir) {
        eprintln!("Failed to create output directory: {}", e);
        std::process::exit(1);
    }

    let seed = args.seed.unwrap_or_else(rand::random);
    println!("Using seed: {}", seed);
    println!("Output directory: {}", args.output_dir.display());
    println!();

    if args.presets_only || args.preset.is_some() {
        run_presets(&args, seed);
    } else {
        run_parameter_sweep(&args, seed);
    }
}

fn run_presets(args: &Args, seed: u64) {
    println!("=== Running Presets ===\n");

    let presets = if let Some(ref name) = args.preset {
        Presets::all()
            .into_iter()
            .filter(|(n, _)| n == name)
            .collect()
    } else {
        Presets::all()
    };

    if presets.is_empty() {
        eprintln!("No matching presets found");
        if let Some(ref _name) = args.preset {
            eprintln!("Available presets:");
            for (n, _) in Presets::all() {
                eprintln!("  - {}", n);
            }
        }
        std::process::exit(1);
    }

    for (name, config) in presets {
        let config = config.with_seed(seed).with_recording(true);
        run_single_config(&args.output_dir, name, &config, args.verbose);
    }
}

fn run_parameter_sweep(args: &Args, seed: u64) {
    println!("=== Running Parameter Sweep ===\n");

    let depths: Vec<u64> = if args.quick {
        LogScale::new(10, 0, 2).values().collect() // 1, 10, 100
    } else {
        LogScale::STANDARD.values().collect() // 1, 10, 100, 1000
    };

    let shapes = get_shapes(&args.shape);
    let update_biases = get_update_biases();

    let total = depths.len() * shapes.len() * update_biases.len();
    let mut completed = 0;

    for depth in &depths {
        let depth = *depth as u32;

        // Filter by depth if specified
        if let Some(filter_depth) = args.depth {
            if depth != filter_depth {
                continue;
            }
        }

        for (shape_name, shape) in &shapes {
            for (bias_name, bias) in &update_biases {
                completed += 1;

                let config = FuzzConfig::minimal()
                    .with_depth(depth)
                    .with_shape(*shape)
                    .with_update_bias(bias.clone())
                    .with_seed(seed)
                    .with_recording(true)
                    .with_update_cycles(if args.quick { 20 } else { 100 })
                    .with_asset_count(calc_asset_count(depth, shape));

                let name = format!("depth{}_{}_{}", depth, shape_name, bias_name);

                if args.verbose {
                    println!("[{}/{}] Running: {}", completed, total, name);
                }

                run_single_config(&args.output_dir, &name, &config, args.verbose);
            }
        }
    }

    println!("\nCompleted {} configurations", completed);
}

fn run_single_config(output_dir: &Path, name: &str, config: &FuzzConfig, verbose: bool) {
    let start = std::time::Instant::now();

    let mut runner = FuzzRunner::new(config.clone());
    let result = runner.run();

    let elapsed = start.elapsed();
    let record = runner.export_run_record(&result);

    // Save to file
    let filename = output_dir.join(format!("{}.json", name));
    if let Err(e) = record.export_to_file(&filename) {
        eprintln!("Failed to write {}: {}", filename.display(), e);
    }

    // Print summary
    let status = if result.is_success() { "OK" } else { "FAIL" };
    println!(
        "{}: {} | queries={} cache_hits={} early_cutoffs={} time={:?}",
        name,
        status,
        record.stats.total_queries_executed,
        record.stats.cache_hits,
        record.stats.early_cutoffs,
        elapsed
    );

    if verbose && !result.is_success() {
        for failure in &result.validation_failures {
            eprintln!(
                "  Validation failure at {:?}: expected {} bytes, got {} bytes",
                failure.node_id,
                failure.expected.len(),
                failure.actual.len()
            );
        }
        for (node_id, err) in &result.query_failures {
            eprintln!("  Query failure at {:?}: {:?}", node_id, err);
        }
    }
}

fn get_shapes(filter: &Option<String>) -> Vec<(&'static str, TreeShape)> {
    let all = vec![
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

    if let Some(ref f) = filter {
        all.into_iter()
            .filter(|(name, _)| name.contains(f.as_str()))
            .collect()
    } else {
        all
    }
}

fn get_update_biases() -> Vec<(&'static str, UpdateBias)> {
    vec![
        ("uniform", UpdateBias::Uniform),
        ("zipf1", UpdateBias::Zipf { s: 1.0 }),
        (
            "hotspot",
            UpdateBias::HotSpot {
                hot_fraction: 0.1,
                hot_probability: 0.9,
            },
        ),
    ]
}

fn calc_asset_count(depth: u32, shape: &TreeShape) -> u32 {
    match shape {
        TreeShape::LinkedList => 1,
        TreeShape::Binary => 2u32.saturating_pow(depth.saturating_sub(1).min(8)).min(256),
        TreeShape::NAry { branching_factor } | TreeShape::CompleteNAry { branching_factor } => {
            (*branching_factor)
                .saturating_pow(depth.saturating_sub(1).min(6))
                .min(256)
        }
        TreeShape::RandomDag { .. } => (depth * 5).min(100),
    }
}
