//! Tracer trait for observing query-flow execution.
//!
//! This module defines the [`Tracer`] trait and related types for observing
//! query execution. The default [`NoopTracer`] provides zero-cost when tracing
//! is not needed.
//!
//! # Example
//!
//! ```ignore
//! use query_flow::{QueryRuntime, Tracer, SpanId, TraceId, SpanContext, QueryCacheKey};
//!
//! // Custom tracer implementation
//! struct MyTracer;
//!
//! impl Tracer for MyTracer {
//!     fn new_span_id(&self) -> SpanId {
//!         SpanId(1)
//!     }
//!
//!     fn new_trace_id(&self) -> TraceId {
//!         TraceId(1)
//!     }
//!
//!     fn on_query_start(&self, ctx: &SpanContext, query: &QueryCacheKey) {
//!         println!("Query started: {:?} (trace={:?})", query, ctx.trace_id);
//!     }
//! }
//!
//! let runtime = QueryRuntime::with_tracer(MyTracer);
//! ```

use serde::{Deserialize, Serialize};

use crate::key::{AssetCacheKey, FullCacheKey, QueryCacheKey};

/// Unique identifier for a query execution span.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct SpanId(pub u64);

impl SpanId {
    /// Zero value, used by NoopTracer.
    pub const ZERO: Self = Self(0);
}

/// Unique identifier for a trace (a complete query execution tree).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct TraceId(pub u64);

impl TraceId {
    /// Zero value, used by NoopTracer.
    pub const ZERO: Self = Self(0);
}

/// Context for a span within a trace, providing parent-child relationships.
///
/// This enables reconstructing the full dependency tree of query executions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct SpanContext {
    /// Unique identifier for this span.
    pub span_id: SpanId,
    /// Identifier for the trace this span belongs to.
    pub trace_id: TraceId,
    /// The parent span's ID, if this is a nested query.
    pub parent_span_id: Option<SpanId>,
}

/// Query execution result classification.
#[derive(Debug, Clone, PartialEq, Eq)]
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

/// Asset loading state for tracing.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TracerAssetState {
    /// Asset is currently loading.
    Loading,
    /// Asset is ready with a value.
    Ready,
    /// Asset was not found.
    NotFound,
}

/// Reason for cache invalidation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InvalidationReason {
    /// A dependency query changed its output.
    DependencyChanged { dep: FullCacheKey },
    /// An asset dependency was updated.
    AssetChanged { asset: FullCacheKey },
    /// Manual invalidation was triggered.
    ManualInvalidation,
    /// An asset was removed.
    AssetRemoved { asset: FullCacheKey },
}

/// Tracer trait for observing query-flow execution.
///
/// Implementations can collect events for testing, forward to the `tracing` crate,
/// or provide custom observability.
///
/// All methods have default empty implementations, so you only need to override
/// the events you're interested in. The [`NoopTracer`] uses all defaults for
/// zero-cost when tracing is disabled.
///
/// # Thread Safety
///
/// Implementations must be `Send + Sync` as the tracer may be called from
/// multiple threads concurrently.
pub trait Tracer: Send + Sync + 'static {
    /// Generate a new unique span ID.
    ///
    /// Called at the start of each query execution.
    fn new_span_id(&self) -> SpanId;

    /// Generate a new unique trace ID.
    ///
    /// Called when starting a root query (one with no parent in the span stack).
    fn new_trace_id(&self) -> TraceId;

    /// Called when a query execution starts.
    ///
    /// Use `query.type_name()` to get the query type and `query.debug_repr()` for the key.
    #[inline]
    fn on_query_start(&self, _ctx: &SpanContext, _query: &QueryCacheKey) {}

    /// Called when cache validity is checked.
    #[inline]
    fn on_cache_check(&self, _ctx: &SpanContext, _query: &QueryCacheKey, _valid: bool) {}

    /// Called when a query execution ends.
    #[inline]
    fn on_query_end(&self, _ctx: &SpanContext, _query: &QueryCacheKey, _result: ExecutionResult) {}

    /// Called when a query dependency is registered during execution.
    #[inline]
    fn on_dependency_registered(
        &self,
        _ctx: &SpanContext,
        _parent: &FullCacheKey,
        _dependency: &FullCacheKey,
    ) {
    }

    /// Called when an asset dependency is registered during execution.
    #[inline]
    fn on_asset_dependency_registered(
        &self,
        _ctx: &SpanContext,
        _parent: &FullCacheKey,
        _asset: &FullCacheKey,
    ) {
    }

    /// Called when early cutoff comparison is performed.
    #[inline]
    fn on_early_cutoff_check(
        &self,
        _ctx: &SpanContext,
        _query: &QueryCacheKey,
        _output_changed: bool,
    ) {
    }

    /// Called when an asset is requested (START event).
    ///
    /// This is called BEFORE the locator executes. Child queries called by
    /// the locator will appear as children of this asset in the trace tree.
    #[inline]
    fn on_asset_requested(&self, _ctx: &SpanContext, _asset: &AssetCacheKey) {}

    /// Called when an asset locator finishes execution.
    ///
    /// This is the "end" event for assets, corresponding to `on_query_end` for queries.
    /// Called after the locator executes with the final state.
    #[inline]
    fn on_asset_located(
        &self,
        _ctx: &SpanContext,
        _asset: &AssetCacheKey,
        _state: TracerAssetState,
    ) {
    }

    /// Called when an asset is resolved with a value.
    #[inline]
    fn on_asset_resolved(&self, _asset: &AssetCacheKey, _changed: bool) {}

    /// Called when an asset is invalidated.
    #[inline]
    fn on_asset_invalidated(&self, _asset: &AssetCacheKey) {}

    /// Called when a query is invalidated.
    #[inline]
    fn on_query_invalidated(&self, _query: &QueryCacheKey, _reason: InvalidationReason) {}

    /// Called when a dependency cycle is detected.
    ///
    /// The path can contain both queries and assets since cycles may involve asset locators.
    #[inline]
    fn on_cycle_detected(&self, _path: &[FullCacheKey]) {}

    /// Called when a query is accessed, providing the [`FullCacheKey`] for GC tracking.
    ///
    /// This is called at the start of each query execution, before `on_query_start`.
    /// Use this to track access times or reference counts for garbage collection.
    ///
    /// # Example
    ///
    /// ```ignore
    /// use query_flow::{FullCacheKey, Tracer, SpanId};
    /// use std::collections::HashMap;
    /// use std::sync::Mutex;
    /// use std::time::Instant;
    ///
    /// struct GcTracer {
    ///     access_times: Mutex<HashMap<FullCacheKey, Instant>>,
    /// }
    ///
    /// impl Tracer for GcTracer {
    ///     fn new_span_id(&self) -> SpanId { SpanId(0) }
    ///
    ///     fn on_query_key(&self, full_key: &FullCacheKey) {
    ///         self.access_times.lock().unwrap()
    ///             .insert(full_key.clone(), Instant::now());
    ///     }
    /// }
    /// ```
    #[inline]
    fn on_query_key(&self, _full_key: &FullCacheKey) {}
}

/// Zero-cost tracer that discards all events.
///
/// This is the default tracer for [`QueryRuntime`](crate::QueryRuntime).
pub struct NoopTracer;

impl Tracer for NoopTracer {
    #[inline(always)]
    fn new_span_id(&self) -> SpanId {
        // ZERO is valid because all callbacks are no-ops, so no one observes these IDs.
        // This avoids atomic counter overhead.
        SpanId::ZERO
    }

    #[inline(always)]
    fn new_trace_id(&self) -> TraceId {
        TraceId::ZERO
    }
    // All other methods use the default empty implementations
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::key::QueryCacheKey;
    use std::sync::atomic::AtomicUsize;
    use std::sync::atomic::Ordering;
    use std::sync::Arc;

    struct CountingTracer {
        start_count: AtomicUsize,
        end_count: AtomicUsize,
    }

    impl CountingTracer {
        fn new() -> Self {
            Self {
                start_count: AtomicUsize::new(0),
                end_count: AtomicUsize::new(0),
            }
        }
    }

    impl Tracer for CountingTracer {
        fn new_span_id(&self) -> SpanId {
            SpanId(1)
        }

        fn new_trace_id(&self) -> TraceId {
            TraceId(1)
        }

        fn on_query_start(&self, _ctx: &SpanContext, _query: &QueryCacheKey) {
            self.start_count.fetch_add(1, Ordering::Relaxed);
        }

        fn on_query_end(
            &self,
            _ctx: &SpanContext,
            _query: &QueryCacheKey,
            _result: ExecutionResult,
        ) {
            self.end_count.fetch_add(1, Ordering::Relaxed);
        }
    }

    #[test]
    fn test_noop_tracer_returns_zero() {
        let tracer = NoopTracer;
        assert_eq!(tracer.new_span_id(), SpanId::ZERO);
        assert_eq!(tracer.new_trace_id(), TraceId::ZERO);
    }

    #[test]
    fn test_counting_tracer() {
        let tracer = CountingTracer::new();
        let key = QueryCacheKey::new(("TestQuery",));

        let ctx1 = SpanContext {
            span_id: SpanId(1),
            trace_id: TraceId(1),
            parent_span_id: None,
        };
        let ctx2 = SpanContext {
            span_id: SpanId(2),
            trace_id: TraceId(1),
            parent_span_id: Some(SpanId(1)),
        };

        tracer.on_query_start(&ctx1, &key);
        tracer.on_query_start(&ctx2, &key);
        tracer.on_query_end(&ctx1, &key, ExecutionResult::Changed);

        assert_eq!(tracer.start_count.load(Ordering::Relaxed), 2);
        assert_eq!(tracer.end_count.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn test_tracer_is_send_sync() {
        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<NoopTracer>();
        assert_send_sync::<Arc<CountingTracer>>();
    }
}
