//! Integration tests for the Flow Inspector.
//!
//! These tests verify that events are correctly emitted during query execution.

#![cfg(feature = "inspector")]

use std::sync::Arc;

use query_flow::{asset_key, query, QueryContext, QueryError, QueryRuntime};
use query_flow_inspector::{EventCollector, ExecutionResult, FlowEvent};

// ============================================================================
// Test Queries
// ============================================================================

#[query]
fn simple_add(ctx: &mut QueryContext, a: i32, b: i32) -> Result<i32, QueryError> {
    let _ = ctx;
    Ok(a + b)
}

#[query]
fn double(ctx: &mut QueryContext, x: i32) -> Result<i32, QueryError> {
    let _ = ctx;
    Ok(x * 2)
}

#[query]
fn add_then_double(ctx: &mut QueryContext, a: i32, b: i32) -> Result<i32, QueryError> {
    let sum = ctx.query(SimpleAdd::new(*a, *b))?;
    let doubled = ctx.query(Double::new(*sum))?;
    Ok(*doubled)
}

// Test asset
#[asset_key(asset = String, durability = stable)]
pub struct TestSource(pub String);

#[query]
fn process_source(ctx: &mut QueryContext, name: String) -> Result<String, QueryError> {
    let source = ctx
        .asset(&TestSource(name.clone()))?
        .map(|s| (*s).clone())
        .suspend()?;
    Ok(format!("processed: {}", source))
}

// ============================================================================
// Tests
// ============================================================================

#[test]
fn test_simple_query_events() {
    let collector = Arc::new(EventCollector::new());
    let runtime = QueryRuntime::new();
    runtime.set_sink(Some(collector.clone()));

    let result = runtime.query(SimpleAdd::new(1, 2)).unwrap();
    assert_eq!(*result, 3);

    let trace = collector.trace();

    // Should have: QueryStart, CacheCheck(false), EarlyCutoffCheck, QueryEnd
    assert!(
        trace.events.len() >= 3,
        "Expected at least 3 events, got {}",
        trace.events.len()
    );

    // Verify QueryStart
    assert!(
        trace.has_event(|e| matches!(e, FlowEvent::QueryStart { query, .. }
        if query.query_type.contains("SimpleAdd")))
    );

    // Verify CacheCheck(false) - first query is never cached
    assert!(trace.has_event(|e| matches!(e, FlowEvent::CacheCheck { valid: false, .. })));

    // Verify QueryEnd with Changed (first execution always changes)
    assert!(trace.has_event(|e| matches!(
        e,
        FlowEvent::QueryEnd {
            result: ExecutionResult::Changed,
            ..
        }
    )));
}

#[test]
fn test_cached_query_events() {
    let collector = Arc::new(EventCollector::new());
    let runtime = QueryRuntime::new();

    // First query to populate cache (without tracing)
    let _ = runtime.query(SimpleAdd::new(1, 2));

    // Second query should hit cache (with tracing)
    runtime.set_sink(Some(collector.clone()));
    let result = runtime.query(SimpleAdd::new(1, 2)).unwrap();
    assert_eq!(*result, 3);

    let trace = collector.trace();

    // Should have: QueryStart, CacheCheck(true), QueryEnd(CacheHit)
    assert!(trace.has_event(|e| matches!(e, FlowEvent::CacheCheck { valid: true, .. })));
    assert!(trace.has_event(|e| matches!(
        e,
        FlowEvent::QueryEnd {
            result: ExecutionResult::CacheHit,
            ..
        }
    )));
}

#[test]
fn test_dependent_query_events() {
    let collector = Arc::new(EventCollector::new());
    let runtime = QueryRuntime::new();
    runtime.set_sink(Some(collector.clone()));

    let result = runtime.query(AddThenDouble::new(2, 3)).unwrap();
    assert_eq!(*result, 10); // (2+3)*2 = 10

    let trace = collector.trace();

    // Should have events for all three queries
    let query_starts: Vec<_> = trace.query_starts().collect();
    assert!(
        query_starts.len() >= 3,
        "Expected at least 3 query starts, got {}",
        query_starts.len()
    );

    // Verify we see AddThenDouble, SimpleAdd, and Double
    assert!(
        trace.has_event(|e| matches!(e, FlowEvent::QueryStart { query, .. }
        if query.query_type.contains("AddThenDouble")))
    );
    assert!(
        trace.has_event(|e| matches!(e, FlowEvent::QueryStart { query, .. }
        if query.query_type.contains("SimpleAdd")))
    );
    assert!(
        trace.has_event(|e| matches!(e, FlowEvent::QueryStart { query, .. }
        if query.query_type.contains("Double")))
    );

    // NEW: Verify DependencyRegistered events
    assert!(trace.has_event(|e| matches!(e, FlowEvent::DependencyRegistered { parent, dependency, .. }
        if parent.query_type.contains("AddThenDouble") && dependency.query_type.contains("SimpleAdd"))));
    assert!(trace.has_event(
        |e| matches!(e, FlowEvent::DependencyRegistered { parent, dependency, .. }
        if parent.query_type.contains("AddThenDouble") && dependency.query_type.contains("Double"))
    ));
}

#[test]
fn test_asset_events() {
    let collector = Arc::new(EventCollector::new());
    let runtime = QueryRuntime::new();

    // Resolve asset first
    runtime.resolve_asset(TestSource("test".to_string()), "hello".to_string());

    runtime.set_sink(Some(collector.clone()));
    let result = runtime
        .query(ProcessSource::new("test".to_string()))
        .unwrap();
    assert_eq!(*result, "processed: hello");

    let trace = collector.trace();

    // Should have AssetDependencyRegistered event
    assert!(trace.has_event(
        |e| matches!(e, FlowEvent::AssetDependencyRegistered { asset, .. }
        if asset.asset_type.contains("TestSource"))
    ));

    // Should have AssetRequested event
    assert!(trace.has_event(|e| matches!(e, FlowEvent::AssetRequested { .. })));
}

#[test]
fn test_asset_resolution_events() {
    let collector = Arc::new(EventCollector::new());
    let runtime = QueryRuntime::new();
    runtime.set_sink(Some(collector.clone()));

    runtime.resolve_asset(TestSource("new".to_string()), "content".to_string());

    let trace = collector.trace();

    // Should have AssetResolved event
    assert!(trace.has_event(|e| matches!(e, FlowEvent::AssetResolved { changed: true, .. })));
}

#[test]
fn test_asset_invalidation_events() {
    let collector = Arc::new(EventCollector::new());
    let runtime = QueryRuntime::new();

    runtime.resolve_asset(TestSource("test".to_string()), "content".to_string());

    runtime.set_sink(Some(collector.clone()));
    runtime.invalidate_asset(&TestSource("test".to_string()));

    let trace = collector.trace();

    // Should have AssetInvalidated event
    assert!(
        trace.has_event(|e| matches!(e, FlowEvent::AssetInvalidated { asset, .. }
        if asset.asset_type.contains("TestSource")))
    );
}

#[test]
fn test_early_cutoff_events() {
    let collector = Arc::new(EventCollector::new());
    let runtime = QueryRuntime::new();
    runtime.set_sink(Some(collector.clone()));

    let result = runtime.query(SimpleAdd::new(5, 5)).unwrap();
    assert_eq!(*result, 10);

    let trace = collector.trace();

    // First execution should have EarlyCutoffCheck with output_changed=true (no previous value)
    assert!(trace.has_event(|e| matches!(
        e,
        FlowEvent::EarlyCutoffCheck {
            output_changed: true,
            ..
        }
    )));
}

#[test]
fn test_cycle_detection_events() {
    // Create mutually recursive queries
    struct CycleA(i32);
    struct CycleB(i32);

    impl query_flow::Query for CycleA {
        type CacheKey = i32;
        type Output = i32;

        fn cache_key(&self) -> Self::CacheKey {
            self.0
        }

        fn query(&self, ctx: &mut QueryContext) -> Result<Self::Output, QueryError> {
            let b = ctx.query(CycleB(self.0))?;
            Ok(*b + 1)
        }

        fn output_eq(old: &Self::Output, new: &Self::Output) -> bool {
            old == new
        }
    }

    impl query_flow::Query for CycleB {
        type CacheKey = i32;
        type Output = i32;

        fn cache_key(&self) -> Self::CacheKey {
            self.0
        }

        fn query(&self, ctx: &mut QueryContext) -> Result<Self::Output, QueryError> {
            let a = ctx.query(CycleA(self.0))?;
            Ok(*a + 1)
        }

        fn output_eq(old: &Self::Output, new: &Self::Output) -> bool {
            old == new
        }
    }

    let collector = Arc::new(EventCollector::new());
    let runtime = QueryRuntime::new();
    runtime.set_sink(Some(collector.clone()));

    let result = runtime.query(CycleA(1));
    assert!(matches!(result, Err(QueryError::Cycle { .. })));

    let trace = collector.trace();

    // Should have CycleDetected event
    assert!(trace.has_event(|e| matches!(e, FlowEvent::CycleDetected { .. })));

    // Should have QueryEnd with CycleDetected result
    assert!(trace.has_event(|e| matches!(
        e,
        FlowEvent::QueryEnd {
            result: ExecutionResult::CycleDetected,
            ..
        }
    )));
}

#[test]
fn test_query_invalidation_events() {
    let collector = Arc::new(EventCollector::new());
    let runtime = QueryRuntime::new();

    // Populate cache
    runtime.query(SimpleAdd::new(1, 2)).unwrap();

    // Invalidate with tracing
    runtime.set_sink(Some(collector.clone()));
    runtime.invalidate::<SimpleAdd>(&(1, 2));

    let trace = collector.trace();

    // Should have QueryInvalidated event
    assert!(
        trace.has_event(|e| matches!(e, FlowEvent::QueryInvalidated { query, .. }
        if query.query_type.contains("SimpleAdd")))
    );
}

// Serialization tests are in query-flow-inspector crate
