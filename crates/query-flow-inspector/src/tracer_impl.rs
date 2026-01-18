//! EventSinkTracer - Bridge between query-flow Tracer and EventSink.
//!
//! This module provides `EventSinkTracer`, which implements the `Tracer` trait
//! from query-flow and forwards events to an `EventSink` as `FlowEvent` instances.

use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use query_flow::{
    AssetCacheKey, ExecutionResult as TracerExecutionResult, FullCacheKey,
    InvalidationReason as TracerInvalidationReason, QueryCacheKey, SpanContext, SpanId, TraceId,
    Tracer, TracerAssetState,
};

use crate::events::FlowEvent;
use crate::sink::EventSink;

/// Global span ID counter for EventSinkTracer.
static SPAN_COUNTER: AtomicU64 = AtomicU64::new(1);
/// Global trace ID counter for EventSinkTracer.
static TRACE_COUNTER: AtomicU64 = AtomicU64::new(1);

/// A `Tracer` implementation that forwards events to an `EventSink`.
///
/// This bridge allows using the new generic tracer system with existing
/// `EventSink` implementations like `EventCollector`.
///
/// # Example
///
/// ```ignore
/// use query_flow::QueryRuntime;
/// use query_flow_inspector::{EventCollector, EventSinkTracer};
/// use std::sync::Arc;
///
/// let collector = Arc::new(EventCollector::new());
/// let tracer = EventSinkTracer::new(collector.clone());
/// let runtime = QueryRuntime::with_tracer(tracer);
///
/// // Run queries...
/// runtime.query(MyQuery::new())?;
///
/// // Get the trace
/// let trace = collector.trace();
/// ```
pub struct EventSinkTracer {
    sink: Arc<dyn EventSink>,
    start_times: Mutex<HashMap<SpanId, Instant>>,
}

impl EventSinkTracer {
    /// Create a new EventSinkTracer wrapping the given sink.
    pub fn new(sink: Arc<dyn EventSink>) -> Self {
        Self {
            sink,
            start_times: Mutex::new(HashMap::new()),
        }
    }
}

impl Tracer for EventSinkTracer {
    #[inline]
    fn new_span_id(&self) -> SpanId {
        SpanId(SPAN_COUNTER.fetch_add(1, Ordering::Relaxed))
    }

    #[inline]
    fn new_trace_id(&self) -> TraceId {
        TraceId(TRACE_COUNTER.fetch_add(1, Ordering::Relaxed))
    }

    #[inline]
    fn on_query_start(&self, ctx: &SpanContext, query: &QueryCacheKey) {
        self.start_times
            .lock()
            .unwrap()
            .insert(ctx.span_id, Instant::now());
        self.sink.emit(FlowEvent::QueryStart {
            span_id: ctx.span_id,
            trace_id: ctx.trace_id,
            parent_span_id: ctx.parent_span_id,
            query: query.into(),
        });
    }

    #[inline]
    fn on_cache_check(&self, ctx: &SpanContext, query: &QueryCacheKey, valid: bool) {
        self.sink.emit(FlowEvent::CacheCheck {
            span_id: ctx.span_id,
            trace_id: ctx.trace_id,
            parent_span_id: ctx.parent_span_id,
            query: query.into(),
            valid,
        });
    }

    #[inline]
    fn on_query_end(
        &self,
        ctx: &SpanContext,
        query: &QueryCacheKey,
        result: TracerExecutionResult,
    ) {
        let duration = self
            .start_times
            .lock()
            .unwrap()
            .remove(&ctx.span_id)
            .map(|start| start.elapsed())
            .unwrap_or(Duration::ZERO);
        self.sink.emit(FlowEvent::QueryEnd {
            span_id: ctx.span_id,
            trace_id: ctx.trace_id,
            parent_span_id: ctx.parent_span_id,
            query: query.into(),
            result: result.into(),
            duration,
        });
    }

    #[inline]
    fn on_dependency_registered(
        &self,
        ctx: &SpanContext,
        parent: &FullCacheKey,
        dependency: &FullCacheKey,
    ) {
        self.sink.emit(FlowEvent::DependencyRegistered {
            span_id: ctx.span_id,
            trace_id: ctx.trace_id,
            parent_span_id: ctx.parent_span_id,
            parent: parent.into(),
            dependency: dependency.into(),
        });
    }

    #[inline]
    fn on_asset_dependency_registered(
        &self,
        ctx: &SpanContext,
        parent: &FullCacheKey,
        asset: &FullCacheKey,
    ) {
        self.sink.emit(FlowEvent::AssetDependencyRegistered {
            span_id: ctx.span_id,
            trace_id: ctx.trace_id,
            parent_span_id: ctx.parent_span_id,
            parent: parent.into(),
            asset: asset.into(),
        });
    }

    #[inline]
    fn on_early_cutoff_check(
        &self,
        ctx: &SpanContext,
        query: &QueryCacheKey,
        output_changed: bool,
    ) {
        self.sink.emit(FlowEvent::EarlyCutoffCheck {
            span_id: ctx.span_id,
            trace_id: ctx.trace_id,
            parent_span_id: ctx.parent_span_id,
            query: query.into(),
            output_changed,
        });
    }

    #[inline]
    fn on_asset_requested(&self, ctx: &SpanContext, asset: &AssetCacheKey) {
        self.sink.emit(FlowEvent::AssetRequested {
            span_id: ctx.span_id,
            trace_id: ctx.trace_id,
            parent_span_id: ctx.parent_span_id,
            asset: asset.into(),
        });
    }

    #[inline]
    fn on_asset_located(&self, ctx: &SpanContext, asset: &AssetCacheKey, state: TracerAssetState) {
        self.sink.emit(FlowEvent::AssetLocated {
            span_id: ctx.span_id,
            trace_id: ctx.trace_id,
            parent_span_id: ctx.parent_span_id,
            asset: asset.into(),
            state: state.into(),
        });
    }

    #[inline]
    fn on_asset_resolved(&self, asset: &AssetCacheKey, changed: bool) {
        self.sink.emit(FlowEvent::AssetResolved {
            asset: asset.into(),
            changed,
        });
    }

    #[inline]
    fn on_asset_invalidated(&self, asset: &AssetCacheKey) {
        self.sink.emit(FlowEvent::AssetInvalidated {
            asset: asset.into(),
        });
    }

    #[inline]
    fn on_query_invalidated(&self, query: &QueryCacheKey, reason: TracerInvalidationReason) {
        self.sink.emit(FlowEvent::QueryInvalidated {
            query: query.into(),
            reason: reason.into(),
        });
    }

    #[inline]
    fn on_cycle_detected(&self, path: &[FullCacheKey]) {
        self.sink.emit(FlowEvent::CycleDetected {
            path: path.iter().map(|k| k.into()).collect(),
        });
    }

    #[inline]
    fn on_missing_dependency(&self, query: &QueryCacheKey, dependency_description: &str) {
        self.sink.emit(FlowEvent::MissingDependency {
            query: query.into(),
            dependency_description: dependency_description.to_string(),
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::collector::EventCollector;

    #[test]
    fn test_event_sink_tracer() {
        let collector = Arc::new(EventCollector::new());
        let tracer = EventSinkTracer::new(collector.clone());

        // Generate some events
        let span_id = tracer.new_span_id();
        let trace_id = tracer.new_trace_id();
        let ctx = SpanContext {
            span_id,
            trace_id,
            parent_span_id: None,
        };
        let query = QueryCacheKey::new(("TestQuery",));

        tracer.on_query_start(&ctx, &query);
        tracer.on_cache_check(&ctx, &query, false);
        tracer.on_query_end(&ctx, &query, TracerExecutionResult::Changed);

        // Check events were collected
        let events = collector.events();
        assert_eq!(events.len(), 3);
        assert!(matches!(events[0], FlowEvent::QueryStart { .. }));
        assert!(matches!(events[1], FlowEvent::CacheCheck { .. }));
        assert!(matches!(events[2], FlowEvent::QueryEnd { .. }));
    }
}
