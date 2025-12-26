//! Span ID generation for query-flow tracing.
//!
//! This module provides unique span ID generation for tracking query executions.

use std::sync::atomic::{AtomicU64, Ordering};

use crate::events::SpanId;

static SPAN_COUNTER: AtomicU64 = AtomicU64::new(1);

/// Generate a new unique span ID.
pub fn new_span_id() -> SpanId {
    SpanId(SPAN_COUNTER.fetch_add(1, Ordering::Relaxed))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_span_id_uniqueness() {
        let id1 = new_span_id();
        let id2 = new_span_id();
        let id3 = new_span_id();

        assert_ne!(id1, id2);
        assert_ne!(id2, id3);
        assert_ne!(id1, id3);
    }

    #[test]
    fn test_span_id_monotonic() {
        let id1 = new_span_id();
        let id2 = new_span_id();

        assert!(id2.0 > id1.0);
    }
}
