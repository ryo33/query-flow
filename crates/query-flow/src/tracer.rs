//! Tracer trait for observing query-flow execution.
//!
//! This module defines the [`Tracer`] trait and related types for observing
//! query execution. The default [`NoopTracer`] provides zero-cost when tracing
//! is not needed.
//!
//! # Example
//!
//! ```ignore
//! use query_flow::{QueryRuntime, Tracer, SpanId};
//!
//! // Custom tracer implementation
//! struct MyTracer;
//!
//! impl Tracer for MyTracer {
//!     fn new_span_id(&self) -> SpanId {
//!         SpanId(1)
//!     }
//!
//!     fn on_query_start(&self, span_id: SpanId, query: TracerQueryKey) {
//!         println!("Query started: {:?}", query);
//!     }
//! }
//!
//! let runtime = QueryRuntime::with_tracer(MyTracer);
//! ```

use serde::{Deserialize, Serialize};
use std::sync::atomic::{AtomicU64, Ordering};

use crate::key::FullCacheKey;

/// Unique identifier for a query execution span.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct SpanId(pub u64);

/// Represents a query key in a type-erased manner for tracing.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TracerQueryKey {
    /// The query type name (e.g., "calc::ParseExpr")
    pub query_type: &'static str,
    /// Debug representation of the cache key (e.g., "(\"main.txt\",)")
    pub cache_key_debug: String,
}

impl TracerQueryKey {
    /// Create a new tracer query key.
    #[inline]
    pub fn new(query_type: &'static str, cache_key_debug: impl Into<String>) -> Self {
        Self {
            query_type,
            cache_key_debug: cache_key_debug.into(),
        }
    }
}

/// Represents an asset key in a type-erased manner for tracing.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TracerAssetKey {
    /// The asset type name (e.g., "calc::SourceFile")
    pub asset_type: &'static str,
    /// Debug representation of the key (e.g., "SourceFile(\"main.txt\")")
    pub key_debug: String,
}

impl TracerAssetKey {
    /// Create a new tracer asset key.
    #[inline]
    pub fn new(asset_type: &'static str, key_debug: impl Into<String>) -> Self {
        Self {
            asset_type,
            key_debug: key_debug.into(),
        }
    }
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
    DependencyChanged { dep: TracerQueryKey },
    /// An asset dependency was updated.
    AssetChanged { asset: TracerAssetKey },
    /// Manual invalidation was triggered.
    ManualInvalidation,
    /// An asset was removed.
    AssetRemoved { asset: TracerAssetKey },
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
    #[inline]
    fn on_query_start(&self, _span_id: SpanId, _query: TracerQueryKey) {}

    /// Called when cache validity is checked.
    #[inline]
    fn on_cache_check(&self, _span_id: SpanId, _query: TracerQueryKey, _valid: bool) {}

    /// Called when a query execution ends.
    #[inline]
    fn on_query_end(&self, _span_id: SpanId, _query: TracerQueryKey, _result: ExecutionResult) {}

    /// Called when a query dependency is registered during execution.
    #[inline]
    fn on_dependency_registered(
        &self,
        _span_id: SpanId,
        _parent: TracerQueryKey,
        _dependency: TracerQueryKey,
    ) {
    }

    /// Called when an asset dependency is registered during execution.
    #[inline]
    fn on_asset_dependency_registered(
        &self,
        _span_id: SpanId,
        _parent: TracerQueryKey,
        _asset: TracerAssetKey,
    ) {
    }

    /// Called when early cutoff comparison is performed.
    #[inline]
    fn on_early_cutoff_check(
        &self,
        _span_id: SpanId,
        _query: TracerQueryKey,
        _output_changed: bool,
    ) {
    }

    /// Called when an asset is requested.
    #[inline]
    fn on_asset_requested(&self, _asset: TracerAssetKey, _state: TracerAssetState) {}

    /// Called when an asset is resolved with a value.
    #[inline]
    fn on_asset_resolved(&self, _asset: TracerAssetKey, _changed: bool) {}

    /// Called when an asset is invalidated.
    #[inline]
    fn on_asset_invalidated(&self, _asset: TracerAssetKey) {}

    /// Called when a query is invalidated.
    #[inline]
    fn on_query_invalidated(&self, _query: TracerQueryKey, _reason: InvalidationReason) {}

    /// Called when a dependency cycle is detected.
    #[inline]
    fn on_cycle_detected(&self, _path: Vec<TracerQueryKey>) {}

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

        fn on_query_start(&self, _span_id: SpanId, _query: TracerQueryKey) {
            self.start_count.fetch_add(1, Ordering::Relaxed);
        }

        fn on_query_end(&self, _span_id: SpanId, _query: TracerQueryKey, _result: ExecutionResult) {
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
        let key = TracerQueryKey::new("TestQuery", "()");

        tracer.on_query_start(SpanId(1), key.clone());
        tracer.on_query_start(SpanId(2), key.clone());
        tracer.on_query_end(SpanId(1), key, ExecutionResult::Changed);

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
