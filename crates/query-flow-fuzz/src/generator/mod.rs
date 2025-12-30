//! Synthetic dependency tree, query, and asset generation.

mod asset;
mod query;
mod tree;

pub use asset::{generate_asset_data, SyntheticAssetKey};
pub use query::{
    build_query_registry, clear_query_registry, set_query_registry, Dependency, QueryRegistry,
    SyntheticOutput, SyntheticQuery,
};
pub use tree::{compute_hash_output, DependencyTree, NodeId, NodeKind, TreeGenerator, TreeNode};
