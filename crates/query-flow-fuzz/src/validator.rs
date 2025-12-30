//! Result validation using oracle-based approach.

use crate::generator::{DependencyTree, NodeId};
use query_flow::{QueryError, QueryRuntime};
use std::collections::HashMap;

/// Validation failure information.
#[derive(Debug, Clone)]
pub struct ValidationFailure {
    pub node_id: NodeId,
    pub expected: Vec<u8>,
    pub actual: Vec<u8>,
}

/// Validator for checking query results against expected values.
pub struct Validator<'a> {
    tree: &'a DependencyTree,
    runtime: &'a QueryRuntime,
}

impl<'a> Validator<'a> {
    pub fn new(tree: &'a DependencyTree, runtime: &'a QueryRuntime) -> Self {
        Self { tree, runtime }
    }

    /// Validate all root queries against expected values.
    pub fn validate_all(
        &self,
        leaf_values: &HashMap<NodeId, Vec<u8>>,
        query_registry: &crate::generator::QueryRegistry,
    ) -> ValidationResult {
        let expected = self.tree.compute_expected(leaf_values);
        let mut result = ValidationResult::default();

        for &root_id in &self.tree.roots {
            if let Some(query) = query_registry.get(&root_id) {
                match self.runtime.query(query.clone()) {
                    Ok(actual) => {
                        if let Some(expected_data) = expected.get(&root_id) {
                            if actual.data != *expected_data {
                                result.failures.push(ValidationFailure {
                                    node_id: root_id,
                                    expected: expected_data.clone(),
                                    actual: actual.data.clone(),
                                });
                            } else {
                                result.successes += 1;
                            }
                        }
                    }
                    Err(e) => {
                        result.errors.push((root_id, e));
                    }
                }
            }
        }

        result
    }

    /// Validate a sample of queries.
    pub fn validate_sample<R: rand::Rng>(
        &self,
        leaf_values: &HashMap<NodeId, Vec<u8>>,
        query_registry: &crate::generator::QueryRegistry,
        sample_rate: f64,
        rng: &mut R,
    ) -> ValidationResult {
        use rand::seq::SliceRandom;

        let expected = self.tree.compute_expected(leaf_values);
        let mut result = ValidationResult::default();

        // Get all query nodes
        let query_nodes: Vec<NodeId> = self
            .tree
            .nodes
            .iter()
            .filter(|(_, node)| node.kind.is_query())
            .map(|(id, _)| *id)
            .collect();

        // Sample based on rate
        let sample_count = ((query_nodes.len() as f64) * sample_rate).ceil() as usize;
        let sampled: Vec<_> = query_nodes.choose_multiple(rng, sample_count).collect();

        for &&node_id in &sampled {
            if let Some(query) = query_registry.get(&node_id) {
                match self.runtime.query(query.clone()) {
                    Ok(actual) => {
                        if let Some(expected_data) = expected.get(&node_id) {
                            if actual.data != *expected_data {
                                result.failures.push(ValidationFailure {
                                    node_id,
                                    expected: expected_data.clone(),
                                    actual: actual.data.clone(),
                                });
                            } else {
                                result.successes += 1;
                            }
                        }
                    }
                    Err(e) => {
                        result.errors.push((node_id, e));
                    }
                }
            }
        }

        result
    }
}

/// Result of validation.
#[derive(Debug, Default)]
pub struct ValidationResult {
    pub successes: u32,
    pub failures: Vec<ValidationFailure>,
    pub errors: Vec<(NodeId, QueryError)>,
}

impl ValidationResult {
    #[allow(dead_code)]
    pub fn is_success(&self) -> bool {
        self.failures.is_empty() && self.errors.is_empty()
    }

    #[allow(dead_code)]
    pub fn merge(&mut self, other: ValidationResult) {
        self.successes += other.successes;
        self.failures.extend(other.failures);
        self.errors.extend(other.errors);
    }
}
