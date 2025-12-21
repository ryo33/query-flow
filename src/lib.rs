#![deny(missing_docs)]
#![doc = include_str!("../README.md")]

//! Whale is a lock-free incremental computation dependency tracking library.
//!
//! This crate provides primitives for building incremental computation systems,
//! following the formally verified specification in Lean4.
//!
//! # Key Concepts
//!
//! - **Durability**: Nodes have durability levels (0 = volatile, N-1 = stable).
//!   A node's durability cannot exceed its dependencies' minimum durability.
//!
//! - **Validity**: A node is valid if its `verified_at >= revision[durability]`,
//!   or all its dependencies haven't changed since observation.
//!
//! - **Early Cutoff**: When a node's value doesn't change after recomputation,
//!   we use `confirm_unchanged` to preserve `changed_at`, preventing unnecessary
//!   downstream recomputation.
//!
//! # Example
//!
//! ```
//! use whale::{Runtime, Durability};
//!
//! // Create a runtime with 3 durability levels
//! let rt: Runtime<&str, (), 3> = Runtime::new();
//!
//! // Register nodes
//! rt.register("a", (), Durability::volatile(), vec![]).unwrap();
//! rt.register("b", (), Durability::volatile(), vec!["a"]).unwrap();
//!
//! // Check validity
//! assert!(rt.is_valid(&"a"));
//! assert!(rt.is_valid(&"b"));
//!
//! // After updating "a", "b" becomes invalid
//! rt.register("a", (), Durability::volatile(), vec![]).unwrap();
//! assert!(!rt.is_valid(&"b"));
//!
//! // Early cutoff: if "b" recomputes and its value is unchanged
//! rt.confirm_unchanged(&"b", vec!["a"]).unwrap();
//! assert!(rt.is_valid(&"b"));
//! ```

mod node;
mod revision;
mod runtime;

pub use node::{Dep, Dependencies, Dependents, Node};
pub use revision::{AtomicRevision, Durability, Revision, RevisionCounter};
pub use runtime::{RegisterResult, Runtime};
