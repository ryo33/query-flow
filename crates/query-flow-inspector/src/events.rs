//! Event types for query-flow tracing.
//!
//! This module defines all events that can be emitted during query-flow execution,
//! including query lifecycle events, dependency tracking, early cutoff, and asset events.

use serde::{Deserialize, Serialize};
use std::time::Duration;

/// Unique identifier for a query execution span.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct SpanId(pub u64);

/// Represents a query key in a type-erased manner.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct QueryKey {
    /// The query type name (e.g., "calc::ParseExpr")
    pub query_type: String,
    /// Debug representation of the cache key (e.g., "(\"main.txt\",)")
    pub cache_key_debug: String,
}

impl QueryKey {
    pub fn new(query_type: impl Into<String>, cache_key_debug: impl Into<String>) -> Self {
        Self {
            query_type: query_type.into(),
            cache_key_debug: cache_key_debug.into(),
        }
    }
}

/// Represents an asset key in a type-erased manner.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct AssetKey {
    /// The asset type name (e.g., "calc::SourceFile")
    pub asset_type: String,
    /// Debug representation of the key (e.g., "SourceFile(\"main.txt\")")
    pub key_debug: String,
}

impl AssetKey {
    pub fn new(asset_type: impl Into<String>, key_debug: impl Into<String>) -> Self {
        Self {
            asset_type: asset_type.into(),
            key_debug: key_debug.into(),
        }
    }
}

/// Reason for cache invalidation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum InvalidationReason {
    /// A dependency query changed its output.
    DependencyChanged { dep: QueryKey },
    /// An asset dependency was updated.
    AssetChanged { asset: AssetKey },
    /// Manual invalidation was triggered.
    ManualInvalidation,
    /// An asset was removed.
    AssetRemoved { asset: AssetKey },
}

/// Query execution result classification.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ExecutionResult {
    /// Query computed a new value (output changed).
    Changed,
    /// Query completed but output unchanged (early cutoff applied).
    Unchanged,
    /// Query returned cached value without execution.
    CacheHit,
    /// Query suspended waiting for async loading.
    Suspended,
    /// Query detected a dependency cycle.
    CycleDetected,
    /// Query failed with an error.
    Error { message: String },
}

/// Asset loading state.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum AssetState {
    /// Asset is currently loading.
    Loading,
    /// Asset is ready with a value.
    Ready,
    /// Asset was not found.
    NotFound,
}

/// Events emitted during query-flow execution.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum FlowEvent {
    // === Query Lifecycle ===
    /// Query execution started.
    QueryStart {
        span_id: SpanId,
        query: QueryKey,
    },

    /// Cache validity check completed.
    CacheCheck {
        span_id: SpanId,
        query: QueryKey,
        /// Whether the cached value was valid.
        valid: bool,
    },

    /// Query execution completed.
    QueryEnd {
        span_id: SpanId,
        query: QueryKey,
        result: ExecutionResult,
        /// Duration of the query execution.
        duration: Duration,
    },

    // === Dependency Tracking ===
    /// A query dependency was registered during execution.
    DependencyRegistered {
        span_id: SpanId,
        parent: QueryKey,
        dependency: QueryKey,
    },

    /// An asset dependency was registered during execution.
    AssetDependencyRegistered {
        span_id: SpanId,
        parent: QueryKey,
        asset: AssetKey,
    },

    // === Early Cutoff ===
    /// Output comparison for early cutoff was performed.
    EarlyCutoffCheck {
        span_id: SpanId,
        query: QueryKey,
        /// Whether the output changed compared to the cached value.
        output_changed: bool,
    },

    // === Asset Events ===
    /// Asset was requested.
    AssetRequested { asset: AssetKey, state: AssetState },

    /// Asset was resolved with a value.
    AssetResolved {
        asset: AssetKey,
        /// Whether the asset value changed from the previous value.
        changed: bool,
    },

    /// Asset was invalidated.
    AssetInvalidated { asset: AssetKey },

    // === Invalidation ===
    /// Query was invalidated.
    QueryInvalidated {
        query: QueryKey,
        reason: InvalidationReason,
    },

    // === Error Events ===
    /// Dependency cycle was detected.
    CycleDetected { path: Vec<QueryKey> },

    /// Missing dependency error occurred.
    MissingDependency {
        query: QueryKey,
        dependency_description: String,
    },
}

/// A complete trace of events for a query execution tree.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct ExecutionTrace {
    pub events: Vec<FlowEvent>,
}

impl ExecutionTrace {
    pub fn new() -> Self {
        Self { events: Vec::new() }
    }

    pub fn push(&mut self, event: FlowEvent) {
        self.events.push(event);
    }

    /// Filter events for a specific query.
    pub fn events_for_query(&self, query: &QueryKey) -> Vec<&FlowEvent> {
        self.events.iter().filter(|e| matches_query(e, query)).collect()
    }

    /// Get all query start events.
    pub fn query_starts(&self) -> impl Iterator<Item = (&SpanId, &QueryKey)> {
        self.events.iter().filter_map(|e| match e {
            FlowEvent::QueryStart { span_id, query } => Some((span_id, query)),
            _ => None,
        })
    }

    /// Get all query end events.
    pub fn query_ends(&self) -> impl Iterator<Item = (&SpanId, &QueryKey, &ExecutionResult, &Duration)> {
        self.events.iter().filter_map(|e| match e {
            FlowEvent::QueryEnd {
                span_id,
                query,
                result,
                duration,
            } => Some((span_id, query, result, duration)),
            _ => None,
        })
    }

    /// Check if any event matches a predicate.
    pub fn has_event<F>(&self, predicate: F) -> bool
    where
        F: Fn(&FlowEvent) -> bool,
    {
        self.events.iter().any(predicate)
    }
}

/// Check if an event is associated with a specific query.
fn matches_query(event: &FlowEvent, query: &QueryKey) -> bool {
    match event {
        FlowEvent::QueryStart { query: q, .. }
        | FlowEvent::CacheCheck { query: q, .. }
        | FlowEvent::QueryEnd { query: q, .. }
        | FlowEvent::EarlyCutoffCheck { query: q, .. }
        | FlowEvent::QueryInvalidated { query: q, .. }
        | FlowEvent::MissingDependency { query: q, .. } => q == query,
        FlowEvent::DependencyRegistered { parent, dependency, .. } => {
            parent == query || dependency == query
        }
        FlowEvent::AssetDependencyRegistered { parent, .. } => parent == query,
        FlowEvent::CycleDetected { path } => path.contains(query),
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_query_key_creation() {
        let key = QueryKey::new("TestQuery", "(1, 2)");
        assert_eq!(key.query_type, "TestQuery");
        assert_eq!(key.cache_key_debug, "(1, 2)");
    }

    #[test]
    fn test_execution_trace() {
        let mut trace = ExecutionTrace::new();
        let span_id = SpanId(1);
        let query = QueryKey::new("TestQuery", "(1)");

        trace.push(FlowEvent::QueryStart {
            span_id,
            query: query.clone(),
        });
        trace.push(FlowEvent::QueryEnd {
            span_id,
            query: query.clone(),
            result: ExecutionResult::Changed,
            duration: Duration::from_millis(10),
        });

        assert_eq!(trace.events.len(), 2);
        assert_eq!(trace.events_for_query(&query).len(), 2);
    }

    #[test]
    fn test_serde_roundtrip() {
        let event = FlowEvent::QueryStart {
            span_id: SpanId(42),
            query: QueryKey::new("TestQuery", "(1)"),
        };

        let json = serde_json::to_string(&event).unwrap();
        let deserialized: FlowEvent = serde_json::from_str(&json).unwrap();
        assert_eq!(event, deserialized);
    }
}
