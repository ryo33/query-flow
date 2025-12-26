//! Event collector for testing.
//!
//! `EventCollector` accumulates events for later inspection and assertion.
//! This is the primary tool for testing query-flow behavior.

use parking_lot::Mutex;

use crate::events::{ExecutionTrace, FlowEvent};
use crate::sink::EventSink;

/// Event collector for testing - accumulates events for assertions.
///
/// # Example
///
/// ```ignore
/// use query_flow_inspector::{EventCollector, with_sink, FlowEvent};
/// use std::sync::Arc;
///
/// let collector = Arc::new(EventCollector::new());
///
/// with_sink(collector.clone(), || {
///     // Run queries here
/// });
///
/// let trace = collector.trace();
/// assert!(trace.events.len() > 0);
/// ```
#[derive(Debug, Default)]
pub struct EventCollector {
    events: Mutex<Vec<FlowEvent>>,
}

impl EventCollector {
    /// Create a new empty event collector.
    pub fn new() -> Self {
        Self::default()
    }

    /// Get collected events as an execution trace.
    pub fn trace(&self) -> ExecutionTrace {
        ExecutionTrace {
            events: self.events.lock().clone(),
        }
    }

    /// Get collected events as a vector.
    pub fn events(&self) -> Vec<FlowEvent> {
        self.events.lock().clone()
    }

    /// Clear all collected events.
    pub fn clear(&self) {
        self.events.lock().clear();
    }

    /// Take collected events, clearing the collector.
    pub fn take(&self) -> Vec<FlowEvent> {
        std::mem::take(&mut *self.events.lock())
    }

    /// Get the number of collected events.
    pub fn len(&self) -> usize {
        self.events.lock().len()
    }

    /// Check if no events have been collected.
    pub fn is_empty(&self) -> bool {
        self.events.lock().is_empty()
    }
}

impl EventSink for EventCollector {
    fn emit(&self, event: FlowEvent) {
        self.events.lock().push(event);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::events::{ExecutionResult, QueryKey, SpanId};
    use std::time::Duration;

    #[test]
    fn test_collector_basic() {
        let collector = EventCollector::new();
        assert!(collector.is_empty());

        collector.emit(FlowEvent::QueryStart {
            span_id: SpanId(1),
            query: QueryKey::new("Test", "()"),
        });

        assert_eq!(collector.len(), 1);
        assert!(!collector.is_empty());
    }

    #[test]
    fn test_collector_trace() {
        let collector = EventCollector::new();

        collector.emit(FlowEvent::QueryStart {
            span_id: SpanId(1),
            query: QueryKey::new("Test", "()"),
        });
        collector.emit(FlowEvent::QueryEnd {
            span_id: SpanId(1),
            query: QueryKey::new("Test", "()"),
            result: ExecutionResult::Changed,
            duration: Duration::from_millis(10),
        });

        let trace = collector.trace();
        assert_eq!(trace.events.len(), 2);
    }

    #[test]
    fn test_collector_clear() {
        let collector = EventCollector::new();

        collector.emit(FlowEvent::QueryStart {
            span_id: SpanId(1),
            query: QueryKey::new("Test", "()"),
        });

        assert_eq!(collector.len(), 1);
        collector.clear();
        assert_eq!(collector.len(), 0);
    }

    #[test]
    fn test_collector_take() {
        let collector = EventCollector::new();

        collector.emit(FlowEvent::QueryStart {
            span_id: SpanId(1),
            query: QueryKey::new("Test", "()"),
        });

        let events = collector.take();
        assert_eq!(events.len(), 1);
        assert!(collector.is_empty());
    }
}
