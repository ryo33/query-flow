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
//! use query_flow::QueryRuntime;
//! use query_flow_inspector::{EventCollector, EventSinkTracer, FlowEvent, ExecutionResult};
//! use std::sync::Arc;
//!
//! // Create a collector and tracer
//! let collector = Arc::new(EventCollector::new());
//! let tracer = EventSinkTracer::new(collector.clone());
//!
//! // Create runtime with tracer
//! let runtime = QueryRuntime::with_tracer(tracer);
//!
//! // Run queries - events are automatically collected
//! runtime.query(MyQuery::new(args))?;
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
//! - **Error Events**: `CycleDetected`
//!
//! See [`FlowEvent`] for the complete list.
//!
//! # Architecture
//!
//! The runtime uses a generic `Tracer` parameter for observability.
//! `EventSinkTracer` bridges the `Tracer` trait to `EventSink` implementations.

mod collector;
mod events;
mod sink;
mod span_context;
mod tracer_impl;

pub use collector::EventCollector;
pub use events::{
    to_kinds, AssetKey, AssetState, CycleKey, EventKind, ExecutionResult, ExecutionTrace,
    FlowEvent, InvalidationReason, QueryKey, SpanContext, SpanId, TraceId,
};
pub use sink::{EventSink, FilterSink, MultiplexSink, NullSink};
pub use span_context::new_span_id;
pub use tracer_impl::EventSinkTracer;

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
        let trace_id = TraceId(1);
        let query = QueryKey::new("MyQuery", "(1, 2)");

        collector.emit(FlowEvent::QueryStart {
            span_id,
            trace_id,
            parent_span_id: None,
            query: query.clone(),
        });

        collector.emit(FlowEvent::CacheCheck {
            span_id,
            trace_id,
            parent_span_id: None,
            query: query.clone(),
            valid: false,
        });

        collector.emit(FlowEvent::EarlyCutoffCheck {
            span_id,
            trace_id,
            parent_span_id: None,
            query: query.clone(),
            output_changed: true,
        });

        collector.emit(FlowEvent::QueryEnd {
            span_id,
            trace_id,
            parent_span_id: None,
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
