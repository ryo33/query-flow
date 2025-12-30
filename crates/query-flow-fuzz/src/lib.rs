//! Parameterized fuzzy testing and benchmarking suite for query-flow.
//!
//! This crate provides tools for:
//! - Generating synthetic dependency trees with configurable shapes
//! - Running parameterized tests with various configurations
//! - Recording inspector events for performance analysis
//! - Validating query results against expected values

mod config;
mod distribution;
pub mod generator;
mod presets;
mod recorder;
mod runner;
mod validator;

pub use config::{
    DataSize, FuzzConfig, MutationKind, QueryTimeBias, TimeDistribution, TreeShape, UpdateBias,
};
pub use distribution::LogScale;
pub use generator::{DependencyTree, NodeId, NodeKind, TreeNode};
pub use presets::Presets;
pub use recorder::{FuzzEventRecorder, FuzzRunRecord, RunMetadata, RunStats, TimestampedEvent};
pub use runner::{FuzzResult, FuzzRunner};
pub use validator::ValidationFailure;
