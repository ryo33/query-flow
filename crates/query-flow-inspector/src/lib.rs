//! Flow Inspector: Tracing and observability for query-flow.
//!
//! This crate provides a flexible observability layer for query-flow.
//! It supports multiple output modes:
//!
//! - **EventCollector**: Collects events for testing and assertion
//! - **FileWriter**: Writes events to a file for later analysis (TODO)
//! - **TracingAdapter**: Bridges to the `tracing` crate (with `tracing` feature)
//!
//! # Quick Start
//!
//! ```ignore
//! use query_flow_inspector::{EventCollector, FlowEvent, ExecutionResult};
//! use std::sync::Arc;
//!
//! // Create a collector and attach to runtime
//! let collector = Arc::new(EventCollector::new());
//! runtime.set_sink(Some(collector.clone()));
//!
//! // Run queries - events are automatically collected
//! runtime.query(MyQuery::new(args));
//!
//! // Inspect collected events
//! let trace = collector.trace();
//! assert!(trace.events.iter().any(|e| matches!(
//!     e,
//!     FlowEvent::QueryEnd { result: ExecutionResult::Changed, .. }
//! )));
//! ```
//!
//! # Event Types
//!
//! The crate defines several categories of events:
//!
//! - **Query Lifecycle**: `QueryStart`, `CacheCheck`, `QueryEnd`
//! - **Dependency Tracking**: `DependencyRegistered`, `AssetDependencyRegistered`
//! - **Early Cutoff**: `EarlyCutoffCheck`
//! - **Asset Events**: `AssetRequested`, `AssetResolved`, `AssetInvalidated`
//! - **Error Events**: `CycleDetected`, `MissingDependency`
//!
//! See [`FlowEvent`] for the complete list.
//!
//! # Architecture
//!
//! The sink is stored in `QueryRuntime` rather than thread-local state,
//! which means:
//! - Multi-threaded query execution works naturally
//! - No global state to manage
//! - Simple API: just call `runtime.set_sink(Some(collector))`

mod collector;
mod events;
mod sink;
mod span_context;

pub use collector::EventCollector;
pub use events::{
    AssetKey, AssetState, ExecutionResult, ExecutionTrace, FlowEvent, InvalidationReason,
    QueryKey, SpanId,
};
pub use sink::{EventSink, FilterSink, MultiplexSink, NullSink};
pub use span_context::new_span_id;

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;
    use std::time::Duration;

    #[test]
    fn test_end_to_end_collection() {
        let collector = Arc::new(EventCollector::new());

        // Directly emit events to the collector
        let span_id = new_span_id();
        let query = QueryKey::new("MyQuery", "(1, 2)");

        collector.emit(FlowEvent::QueryStart {
            span_id,
            query: query.clone(),
        });

        collector.emit(FlowEvent::CacheCheck {
            span_id,
            query: query.clone(),
            valid: false,
        });

        collector.emit(FlowEvent::EarlyCutoffCheck {
            span_id,
            query: query.clone(),
            output_changed: true,
        });

        collector.emit(FlowEvent::QueryEnd {
            span_id,
            query,
            result: ExecutionResult::Changed,
            duration: Duration::from_millis(5),
        });

        let trace = collector.trace();
        assert_eq!(trace.events.len(), 4);

        // Verify event types
        assert!(matches!(trace.events[0], FlowEvent::QueryStart { .. }));
        assert!(matches!(
            trace.events[1],
            FlowEvent::CacheCheck { valid: false, .. }
        ));
        assert!(matches!(
            trace.events[2],
            FlowEvent::EarlyCutoffCheck {
                output_changed: true,
                ..
            }
        ));
        assert!(matches!(
            trace.events[3],
            FlowEvent::QueryEnd {
                result: ExecutionResult::Changed,
                ..
            }
        ));
    }
}
