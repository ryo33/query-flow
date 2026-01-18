//! Tracer trait for observing query-flow execution.
//!
//! This module defines the [`Tracer`] trait and related types for observing
//! query execution. The default [`NoopTracer`] provides zero-cost when tracing
//! is not needed.
//!
//! # Example
//!
//! ```ignore
//! use query_flow::{QueryRuntime, Tracer, SpanId, QueryCacheKey};
//!
//! // Custom tracer implementation
//! struct MyTracer;
//!
//! impl Tracer for MyTracer {
//!     fn new_span_id(&self) -> SpanId {
//!         SpanId(1)
//!     }
//!
//!     fn on_query_start(&self, span_id: SpanId, query: &QueryCacheKey) {
//!         println!("Query started: {:?}", query);
//!     }
//! }
//!
//! let runtime = QueryRuntime::with_tracer(MyTracer);
//! ```

use serde::{Deserialize, Serialize};
use std::sync::atomic::{AtomicU64, Ordering};

use crate::key::{AssetCacheKey, FullCacheKey, QueryCacheKey};

/// Unique identifier for a query execution span.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct SpanId(pub u64);

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
    /// This is the only required method. Called at the start of each query execution.
    fn new_span_id(&self) -> SpanId;

    /// Called when a query execution starts.
    ///
    /// Use `query.type_name()` to get the query type and `query.debug_repr()` for the key.
    #[inline]
    fn on_query_start(&self, _span_id: SpanId, _query: &QueryCacheKey) {}

    /// Called when cache validity is checked.
    #[inline]
    fn on_cache_check(&self, _span_id: SpanId, _query: &QueryCacheKey, _valid: bool) {}

    /// Called when a query execution ends.
    #[inline]
    fn on_query_end(&self, _span_id: SpanId, _query: &QueryCacheKey, _result: ExecutionResult) {}

    /// Called when a query dependency is registered during execution.
    #[inline]
    fn on_dependency_registered(
        &self,
        _span_id: SpanId,
        _parent: &FullCacheKey,
        _dependency: &FullCacheKey,
    ) {
    }

    /// Called when an asset dependency is registered during execution.
    #[inline]
    fn on_asset_dependency_registered(
        &self,
        _span_id: SpanId,
        _parent: &FullCacheKey,
        _asset: &FullCacheKey,
    ) {
    }

    /// Called when early cutoff comparison is performed.
    #[inline]
    fn on_early_cutoff_check(
        &self,
        _span_id: SpanId,
        _query: &QueryCacheKey,
        _output_changed: bool,
    ) {
    }

    /// Called when an asset is requested.
    #[inline]
    fn on_asset_requested(&self, _asset: &AssetCacheKey, _state: TracerAssetState) {}

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

    /// Called when a missing dependency error occurs.
    #[inline]
    fn on_missing_dependency(&self, _query: &QueryCacheKey, _dependency_description: &str) {}
}

/// Zero-cost tracer that discards all events.
///
/// This is the default tracer for [`QueryRuntime`](crate::QueryRuntime).
pub struct NoopTracer;

/// Global span counter for NoopTracer.
static NOOP_SPAN_COUNTER: AtomicU64 = AtomicU64::new(1);

impl Tracer for NoopTracer {
    #[inline(always)]
    fn new_span_id(&self) -> SpanId {
        SpanId(NOOP_SPAN_COUNTER.fetch_add(1, Ordering::Relaxed))
    }
    // All other methods use the default empty implementations
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::key::QueryCacheKey;
    use std::sync::atomic::AtomicUsize;
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

        fn on_query_start(&self, _span_id: SpanId, _query: &QueryCacheKey) {
            self.start_count.fetch_add(1, Ordering::Relaxed);
        }

        fn on_query_end(&self, _span_id: SpanId, _query: &QueryCacheKey, _result: ExecutionResult) {
            self.end_count.fetch_add(1, Ordering::Relaxed);
        }
    }

    #[test]
    fn test_noop_tracer_span_id() {
        let tracer = NoopTracer;
        let id1 = tracer.new_span_id();
        let id2 = tracer.new_span_id();
        assert_ne!(id1, id2);
    }

    #[test]
    fn test_counting_tracer() {
        let tracer = CountingTracer::new();
        let key = QueryCacheKey::new(("TestQuery",));

        tracer.on_query_start(SpanId(1), &key);
        tracer.on_query_start(SpanId(2), &key);
        tracer.on_query_end(SpanId(1), &key, ExecutionResult::Changed);

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
