//! Event sink trait and implementations.
//!
//! The `EventSink` trait defines the interface for receiving flow events.
//! Implementations can collect events for testing, write to files, or
//! forward to the `tracing` crate.

use crate::events::FlowEvent;

/// Trait for receiving flow events.
///
/// Implementations of this trait can process events in various ways:
/// - Collect for testing (see `EventCollector`)
/// - Write to file for later analysis
/// - Forward to `tracing` crate
///
/// # Example
///
/// ```ignore
/// use query_flow_inspector::{EventSink, FlowEvent};
///
/// struct PrintSink;
///
/// impl EventSink for PrintSink {
///     fn emit(&self, event: FlowEvent) {
///         println!("{:?}", event);
///     }
/// }
/// ```
pub trait EventSink: Send + Sync + 'static {
    /// Called when an event occurs.
    fn emit(&self, event: FlowEvent);

    /// Called at the end of a top-level query to flush buffered events.
    ///
    /// The default implementation does nothing.
    fn flush(&self) {}
}

/// Null sink that discards all events.
///
/// Used when tracing is disabled or no sink is configured.
pub struct NullSink;

impl EventSink for NullSink {
    fn emit(&self, _event: FlowEvent) {}
}

/// A sink that forwards events to multiple child sinks.
pub struct MultiplexSink {
    sinks: Vec<Box<dyn EventSink>>,
}

impl MultiplexSink {
    pub fn new(sinks: Vec<Box<dyn EventSink>>) -> Self {
        Self { sinks }
    }
}

impl EventSink for MultiplexSink {
    fn emit(&self, event: FlowEvent) {
        for sink in &self.sinks {
            sink.emit(event.clone());
        }
    }

    fn flush(&self) {
        for sink in &self.sinks {
            sink.flush();
        }
    }
}

/// A sink that filters events before forwarding.
pub struct FilterSink<F, S>
where
    F: Fn(&FlowEvent) -> bool + Send + Sync + 'static,
    S: EventSink,
{
    filter: F,
    inner: S,
}

impl<F, S> FilterSink<F, S>
where
    F: Fn(&FlowEvent) -> bool + Send + Sync + 'static,
    S: EventSink,
{
    pub fn new(filter: F, inner: S) -> Self {
        Self { filter, inner }
    }
}

impl<F, S> EventSink for FilterSink<F, S>
where
    F: Fn(&FlowEvent) -> bool + Send + Sync + 'static,
    S: EventSink,
{
    fn emit(&self, event: FlowEvent) {
        if (self.filter)(&event) {
            self.inner.emit(event);
        }
    }

    fn flush(&self) {
        self.inner.flush();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::events::{QueryKey, SpanId};
    use std::sync::atomic::{AtomicU32, Ordering};
    use std::sync::Arc;

    struct CountingSink {
        count: AtomicU32,
    }

    impl CountingSink {
        fn new() -> Self {
            Self {
                count: AtomicU32::new(0),
            }
        }

        fn count(&self) -> u32 {
            self.count.load(Ordering::SeqCst)
        }
    }

    impl EventSink for CountingSink {
        fn emit(&self, _event: FlowEvent) {
            self.count.fetch_add(1, Ordering::SeqCst);
        }
    }

    #[test]
    fn test_null_sink() {
        let sink = NullSink;
        sink.emit(FlowEvent::QueryStart {
            span_id: SpanId(1),
            query: QueryKey::new("Test", "()"),
        });
        // No panic = success
    }

    #[test]
    fn test_multiplex_sink() {
        let sink1 = Arc::new(CountingSink::new());
        let sink2 = Arc::new(CountingSink::new());

        // We need to clone for the multiplex sink
        struct ArcSink(Arc<CountingSink>);
        impl EventSink for ArcSink {
            fn emit(&self, event: FlowEvent) {
                self.0.emit(event);
            }
        }

        let multiplex = MultiplexSink::new(vec![
            Box::new(ArcSink(sink1.clone())),
            Box::new(ArcSink(sink2.clone())),
        ]);

        multiplex.emit(FlowEvent::QueryStart {
            span_id: SpanId(1),
            query: QueryKey::new("Test", "()"),
        });

        assert_eq!(sink1.count(), 1);
        assert_eq!(sink2.count(), 1);
    }

    #[test]
    fn test_filter_sink() {
        let inner = CountingSink::new();
        let filter_sink = FilterSink::new(
            |e| matches!(e, FlowEvent::QueryStart { .. }),
            inner,
        );

        // This should pass the filter
        filter_sink.emit(FlowEvent::QueryStart {
            span_id: SpanId(1),
            query: QueryKey::new("Test", "()"),
        });

        // This should be filtered out
        filter_sink.emit(FlowEvent::AssetInvalidated {
            asset: crate::events::AssetKey::new("Test", "()"),
        });

        assert_eq!(filter_sink.inner.count(), 1);
    }
}
