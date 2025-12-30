//! Configuration types for fuzzy testing.

use crate::distribution::Distribution;
use serde::{Deserialize, Serialize};
use std::ops::RangeInclusive;
use std::path::PathBuf;

/// Complete configuration for a fuzzy test run.
#[derive(Debug, Clone)]
pub struct FuzzConfig {
    // === Structural parameters ===
    /// Depth of the dependency tree.
    pub tree_depth: u32,

    /// Shape of the dependency tree.
    pub tree_shape: TreeShape,

    /// Total number of query nodes (approximate for random shapes).
    pub node_count: u32,

    /// Number of leaf assets.
    pub asset_count: u32,

    // === Timing parameters (recorded only, no actual sleep) ===
    /// Query execution time distribution.
    pub query_time: TimeDistribution,

    /// Bias for query execution time across nodes.
    pub query_time_bias: QueryTimeBias,

    /// Asset resolve time distribution.
    pub asset_resolve_time: TimeDistribution,

    // === Update pattern parameters ===
    /// Number of assets updated per "tick".
    pub assets_per_update: RangeInclusive<u32>,

    /// Which assets are updated (bias).
    pub update_bias: UpdateBias,

    /// Number of update cycles to run.
    pub update_cycles: u32,

    // === Data size parameters ===
    /// Query output size in bytes.
    pub output_size: DataSize,

    /// Asset data size in bytes.
    pub asset_size: DataSize,

    // === Validation ===
    /// Fraction of queries to sample and validate (0.0-1.0).
    pub validation_sample_rate: f64,

    /// Validate all queries after each update cycle.
    pub full_validation_cycles: bool,

    // === RNG ===
    /// Seed for reproducibility (None = random).
    pub seed: Option<u64>,

    // === Recording ===
    /// Enable inspector event recording.
    pub record_events: bool,

    /// Output path for events (if recording).
    pub event_output_path: Option<PathBuf>,
}

impl Default for FuzzConfig {
    fn default() -> Self {
        Self::minimal()
    }
}

impl FuzzConfig {
    /// Create a minimal configuration for fast tests.
    pub fn minimal() -> Self {
        Self {
            tree_depth: 3,
            tree_shape: TreeShape::Binary,
            node_count: 7,
            asset_count: 4,
            query_time: TimeDistribution::NOOP,
            query_time_bias: QueryTimeBias::Uniform,
            asset_resolve_time: TimeDistribution::NOOP,
            assets_per_update: 1..=1,
            update_bias: UpdateBias::Uniform,
            update_cycles: 10,
            output_size: DataSize::MINIMAL,
            asset_size: DataSize::MINIMAL,
            validation_sample_rate: 1.0,
            full_validation_cycles: true,
            seed: Some(42),
            record_events: false,
            event_output_path: None,
        }
    }

    // === Builder methods ===

    pub fn with_depth(mut self, depth: u32) -> Self {
        self.tree_depth = depth;
        self
    }

    pub fn with_shape(mut self, shape: TreeShape) -> Self {
        self.tree_shape = shape;
        self
    }

    pub fn with_node_count(mut self, count: u32) -> Self {
        self.node_count = count;
        self
    }

    pub fn with_asset_count(mut self, count: u32) -> Self {
        self.asset_count = count;
        self
    }

    pub fn with_query_time(mut self, time: TimeDistribution) -> Self {
        self.query_time = time;
        self
    }

    pub fn with_query_time_bias(mut self, bias: QueryTimeBias) -> Self {
        self.query_time_bias = bias;
        self
    }

    pub fn with_asset_resolve_time(mut self, time: TimeDistribution) -> Self {
        self.asset_resolve_time = time;
        self
    }

    pub fn with_assets_per_update(mut self, range: RangeInclusive<u32>) -> Self {
        self.assets_per_update = range;
        self
    }

    pub fn with_update_bias(mut self, bias: UpdateBias) -> Self {
        self.update_bias = bias;
        self
    }

    pub fn with_update_cycles(mut self, cycles: u32) -> Self {
        self.update_cycles = cycles;
        self
    }

    pub fn with_output_size(mut self, size: DataSize) -> Self {
        self.output_size = size;
        self
    }

    pub fn with_asset_size(mut self, size: DataSize) -> Self {
        self.asset_size = size;
        self
    }

    pub fn with_validation_sample_rate(mut self, rate: f64) -> Self {
        self.validation_sample_rate = rate.clamp(0.0, 1.0);
        self
    }

    pub fn with_full_validation(mut self, enabled: bool) -> Self {
        self.full_validation_cycles = enabled;
        self
    }

    pub fn with_seed(mut self, seed: u64) -> Self {
        self.seed = Some(seed);
        self
    }

    pub fn with_random_seed(mut self) -> Self {
        self.seed = None;
        self
    }

    pub fn with_recording(mut self, enabled: bool) -> Self {
        self.record_events = enabled;
        self
    }

    pub fn with_event_output_path(mut self, path: impl Into<PathBuf>) -> Self {
        self.event_output_path = Some(path.into());
        self.record_events = true;
        self
    }

    /// Convert to a serializable form for recording.
    pub fn to_serializable(&self) -> SerializableConfig {
        SerializableConfig {
            tree_depth: self.tree_depth,
            tree_shape: self.tree_shape.name().to_string(),
            node_count: self.node_count,
            asset_count: self.asset_count,
            query_time_min_us: self.query_time.min_us,
            query_time_max_us: self.query_time.max_us,
            asset_resolve_time_min_us: self.asset_resolve_time.min_us,
            asset_resolve_time_max_us: self.asset_resolve_time.max_us,
            assets_per_update_min: *self.assets_per_update.start(),
            assets_per_update_max: *self.assets_per_update.end(),
            update_bias: self.update_bias.name().to_string(),
            update_cycles: self.update_cycles,
            output_size_min: self.output_size.min_bytes,
            output_size_max: self.output_size.max_bytes,
            asset_size_min: self.asset_size.min_bytes,
            asset_size_max: self.asset_size.max_bytes,
            validation_sample_rate: self.validation_sample_rate,
        }
    }
}

/// Tree shape specification.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum TreeShape {
    /// Linear chain: each node has exactly 1 child.
    /// Depth = N, Width = 1.
    LinkedList,

    /// Binary tree: each node has 0-2 children.
    Binary,

    /// N-ary tree with specified branching factor.
    NAry { branching_factor: u32 },

    /// Complete N-ary tree (all non-leaf nodes have N children).
    CompleteNAry { branching_factor: u32 },

    /// Random DAG (Directed Acyclic Graph) with expected fan-out.
    RandomDag { expected_fan_out: f64 },
}

impl TreeShape {
    /// Get a short name for this shape.
    pub fn name(&self) -> &'static str {
        match self {
            TreeShape::LinkedList => "linked_list",
            TreeShape::Binary => "binary",
            TreeShape::NAry { .. } => "nary",
            TreeShape::CompleteNAry { .. } => "complete_nary",
            TreeShape::RandomDag { .. } => "random_dag",
        }
    }
}

/// Bias distribution for selecting which nodes to update.
#[derive(Debug, Clone)]
pub enum UpdateBias {
    /// Uniform random across all leaves.
    Uniform,

    /// Zipf distribution: some leaves updated much more frequently.
    Zipf { s: f64 },

    /// Specific leaves are "hot" (updated frequently).
    HotSpot {
        hot_fraction: f64,
        hot_probability: f64,
    },

    /// Round-robin through leaves.
    RoundRobin,
}

impl UpdateBias {
    /// Get a short name for this bias.
    pub fn name(&self) -> &'static str {
        match self {
            UpdateBias::Uniform => "uniform",
            UpdateBias::Zipf { .. } => "zipf",
            UpdateBias::HotSpot { .. } => "hotspot",
            UpdateBias::RoundRobin => "round_robin",
        }
    }
}

/// Time distribution for simulated work.
#[derive(Debug, Clone, Copy)]
pub struct TimeDistribution {
    /// Minimum time in microseconds.
    pub min_us: u64,
    /// Maximum time in microseconds.
    pub max_us: u64,
    /// Distribution type.
    pub distribution: Distribution,
}

impl TimeDistribution {
    /// No-op timing (0 microseconds).
    pub const NOOP: Self = Self {
        min_us: 0,
        max_us: 0,
        distribution: Distribution::Constant,
    };

    /// Constant time in microseconds.
    pub const fn microseconds(us: u64) -> Self {
        Self {
            min_us: us,
            max_us: us,
            distribution: Distribution::Constant,
        }
    }

    /// Constant time in milliseconds.
    pub const fn milliseconds(ms: u64) -> Self {
        Self::microseconds(ms * 1000)
    }

    /// Range with uniform distribution.
    pub const fn range_us(min: u64, max: u64) -> Self {
        Self {
            min_us: min,
            max_us: max,
            distribution: Distribution::Uniform,
        }
    }
}

/// Bias for query execution time.
#[derive(Debug, Clone, Copy)]
pub enum QueryTimeBias {
    /// All queries take similar time.
    Uniform,

    /// Leaf queries faster, root queries slower.
    DepthProportional,

    /// Some queries are expensive.
    HotQueries {
        hot_fraction: f64,
        hot_multiplier: f64,
    },
}

/// Data size specification.
#[derive(Debug, Clone, Copy)]
pub struct DataSize {
    pub min_bytes: usize,
    pub max_bytes: usize,
    pub distribution: Distribution,
}

impl DataSize {
    /// Minimal 8-byte data.
    pub const MINIMAL: Self = Self {
        min_bytes: 8,
        max_bytes: 8,
        distribution: Distribution::Constant,
    };

    /// Fixed size in bytes.
    pub const fn fixed(bytes: usize) -> Self {
        Self {
            min_bytes: bytes,
            max_bytes: bytes,
            distribution: Distribution::Constant,
        }
    }

    /// Range with uniform distribution.
    pub const fn range(min: usize, max: usize) -> Self {
        Self {
            min_bytes: min,
            max_bytes: max,
            distribution: Distribution::Uniform,
        }
    }
}

/// Serializable configuration for recording.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SerializableConfig {
    pub tree_depth: u32,
    pub tree_shape: String,
    pub node_count: u32,
    pub asset_count: u32,
    pub query_time_min_us: u64,
    pub query_time_max_us: u64,
    pub asset_resolve_time_min_us: u64,
    pub asset_resolve_time_max_us: u64,
    pub assets_per_update_min: u32,
    pub assets_per_update_max: u32,
    pub update_bias: String,
    pub update_cycles: u32,
    pub output_size_min: usize,
    pub output_size_max: usize,
    pub asset_size_min: usize,
    pub asset_size_max: usize,
    pub validation_sample_rate: f64,
}
