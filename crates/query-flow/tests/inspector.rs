//! Integration tests for the Flow Inspector.
//!
//! These tests verify that events are correctly emitted during query execution.

#![cfg(feature = "inspector")]

use std::sync::Arc;

use query_flow::{asset_key, query, QueryContext, QueryError, QueryRuntime};
use query_flow_inspector::{
    to_kinds, AssetKey, AssetState, EventCollector, EventKind, ExecutionResult, QueryKey,
};

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
    let sum = ctx.query(SimpleAdd::new(a, b))?;
    let doubled = ctx.query(Double::new(*sum))?;
    Ok(*doubled)
}

// Test asset
#[asset_key(asset = String, durability = stable)]
pub struct TestSource(pub String);

#[query]
fn process_source(ctx: &mut QueryContext, name: String) -> Result<String, QueryError> {
    let source = ctx.asset(TestSource(name.clone()))?.suspend()?;
    Ok(format!("processed: {}", source))
}

// ============================================================================
// Helper
// ============================================================================

fn q(query_type: &str, cache_key_debug: &str) -> QueryKey {
    QueryKey::new(query_type, cache_key_debug)
}

fn a(asset_type: &str, key_debug: &str) -> AssetKey {
    AssetKey::new(asset_type, key_debug)
}

// ============================================================================
// Tests
// ============================================================================

#[test]
fn test_simple_query_events() {
    use EventKind::*;
    use ExecutionResult::*;

    let collector = Arc::new(EventCollector::new());
    let runtime = QueryRuntime::new();
    runtime.set_sink(Some(collector.clone()));

    let result = runtime.query(SimpleAdd::new(1, 2)).unwrap();
    assert_eq!(*result, 3);

    assert_eq!(
        to_kinds(&collector.trace()),
        vec![
            QueryStart {
                query: q("inspector::SimpleAdd", "inspector::SimpleAdd((1, 2))")
            },
            CacheCheck {
                query: q("inspector::SimpleAdd", "inspector::SimpleAdd((1, 2))"),
                valid: false
            },
            EarlyCutoffCheck {
                query: q("inspector::SimpleAdd", "inspector::SimpleAdd((1, 2))"),
                output_changed: true
            },
            QueryEnd {
                query: q("inspector::SimpleAdd", "inspector::SimpleAdd((1, 2))"),
                result: Changed
            },
        ]
    );
}

#[test]
fn test_cached_query_events() {
    use EventKind::*;
    use ExecutionResult::*;

    let collector = Arc::new(EventCollector::new());
    let runtime = QueryRuntime::new();

    // First query to populate cache (without tracing)
    let _ = runtime.query(SimpleAdd::new(1, 2));

    // Second query should hit cache (with tracing)
    runtime.set_sink(Some(collector.clone()));
    let result = runtime.query(SimpleAdd::new(1, 2)).unwrap();
    assert_eq!(*result, 3);

    assert_eq!(
        to_kinds(&collector.trace()),
        vec![
            QueryStart {
                query: q("inspector::SimpleAdd", "inspector::SimpleAdd((1, 2))")
            },
            CacheCheck {
                query: q("inspector::SimpleAdd", "inspector::SimpleAdd((1, 2))"),
                valid: true
            },
            QueryEnd {
                query: q("inspector::SimpleAdd", "inspector::SimpleAdd((1, 2))"),
                result: CacheHit
            },
        ]
    );
}

#[test]
fn test_dependent_query_events() {
    use EventKind::*;
    use ExecutionResult::*;

    let collector = Arc::new(EventCollector::new());
    let runtime = QueryRuntime::new();
    runtime.set_sink(Some(collector.clone()));

    let result = runtime.query(AddThenDouble::new(2, 3)).unwrap();
    assert_eq!(*result, 10); // (2+3)*2 = 10

    assert_eq!(
        to_kinds(&collector.trace()),
        vec![
            QueryStart {
                query: q(
                    "inspector::AddThenDouble",
                    "inspector::AddThenDouble((2, 3))"
                )
            },
            CacheCheck {
                query: q(
                    "inspector::AddThenDouble",
                    "inspector::AddThenDouble((2, 3))"
                ),
                valid: false
            },
            // SimpleAdd(2, 3) = 5
            DependencyRegistered {
                parent: q(
                    "inspector::AddThenDouble",
                    "inspector::AddThenDouble((2, 3))"
                ),
                dependency: q("inspector::SimpleAdd", "inspector::SimpleAdd((2, 3))"),
            },
            QueryStart {
                query: q("inspector::SimpleAdd", "inspector::SimpleAdd((2, 3))")
            },
            CacheCheck {
                query: q("inspector::SimpleAdd", "inspector::SimpleAdd((2, 3))"),
                valid: false
            },
            EarlyCutoffCheck {
                query: q("inspector::SimpleAdd", "inspector::SimpleAdd((2, 3))"),
                output_changed: true
            },
            QueryEnd {
                query: q("inspector::SimpleAdd", "inspector::SimpleAdd((2, 3))"),
                result: Changed
            },
            // Double(5) = 10
            DependencyRegistered {
                parent: q(
                    "inspector::AddThenDouble",
                    "inspector::AddThenDouble((2, 3))"
                ),
                dependency: q("inspector::Double", "inspector::Double(5)"),
            },
            QueryStart {
                query: q("inspector::Double", "inspector::Double(5)")
            },
            CacheCheck {
                query: q("inspector::Double", "inspector::Double(5)"),
                valid: false
            },
            EarlyCutoffCheck {
                query: q("inspector::Double", "inspector::Double(5)"),
                output_changed: true
            },
            QueryEnd {
                query: q("inspector::Double", "inspector::Double(5)"),
                result: Changed
            },
            // AddThenDouble completes
            EarlyCutoffCheck {
                query: q(
                    "inspector::AddThenDouble",
                    "inspector::AddThenDouble((2, 3))"
                ),
                output_changed: true
            },
            QueryEnd {
                query: q(
                    "inspector::AddThenDouble",
                    "inspector::AddThenDouble((2, 3))"
                ),
                result: Changed
            },
        ]
    );
}

#[test]
fn test_asset_events() {
    use EventKind::*;
    use ExecutionResult::*;

    let collector = Arc::new(EventCollector::new());
    let runtime = QueryRuntime::new();

    // Resolve asset first
    runtime.resolve_asset(TestSource("test".to_string()), "hello".to_string());

    runtime.set_sink(Some(collector.clone()));
    let result = runtime
        .query(ProcessSource::new("test".to_string()))
        .unwrap();
    assert_eq!(*result, "processed: hello");

    assert_eq!(
        to_kinds(&collector.trace()),
        vec![
            QueryStart {
                query: q(
                    "inspector::ProcessSource",
                    "inspector::ProcessSource(\"test\")"
                )
            },
            CacheCheck {
                query: q(
                    "inspector::ProcessSource",
                    "inspector::ProcessSource(\"test\")"
                ),
                valid: false
            },
            AssetDependencyRegistered {
                parent: q(
                    "inspector::ProcessSource",
                    "inspector::ProcessSource(\"test\")"
                ),
                asset: a("inspector::TestSource", "TestSource(\"test\")"),
            },
            AssetRequested {
                asset: a("inspector::TestSource", "TestSource(\"test\")"),
                state: AssetState::Ready
            },
            EarlyCutoffCheck {
                query: q(
                    "inspector::ProcessSource",
                    "inspector::ProcessSource(\"test\")"
                ),
                output_changed: true
            },
            QueryEnd {
                query: q(
                    "inspector::ProcessSource",
                    "inspector::ProcessSource(\"test\")"
                ),
                result: Changed
            },
        ]
    );
}

#[test]
fn test_asset_resolution_events() {
    use EventKind::*;

    let collector = Arc::new(EventCollector::new());
    let runtime = QueryRuntime::new();
    runtime.set_sink(Some(collector.clone()));

    runtime.resolve_asset(TestSource("new".to_string()), "content".to_string());

    assert_eq!(
        to_kinds(&collector.trace()),
        vec![AssetResolved {
            asset: a("inspector::TestSource", "TestSource(\"new\")"),
            changed: true
        }]
    );
}

#[test]
fn test_asset_invalidation_events() {
    use EventKind::*;

    let collector = Arc::new(EventCollector::new());
    let runtime = QueryRuntime::new();

    runtime.resolve_asset(TestSource("test".to_string()), "content".to_string());

    runtime.set_sink(Some(collector.clone()));
    runtime.invalidate_asset(&TestSource("test".to_string()));

    assert_eq!(
        to_kinds(&collector.trace()),
        vec![AssetInvalidated {
            asset: a("inspector::TestSource", "TestSource(\"test\")")
        }]
    );
}

#[test]
fn test_early_cutoff_events() {
    use EventKind::*;
    use ExecutionResult::*;

    let collector = Arc::new(EventCollector::new());
    let runtime = QueryRuntime::new();
    runtime.set_sink(Some(collector.clone()));

    let result = runtime.query(SimpleAdd::new(5, 5)).unwrap();
    assert_eq!(*result, 10);

    assert_eq!(
        to_kinds(&collector.trace()),
        vec![
            QueryStart {
                query: q("inspector::SimpleAdd", "inspector::SimpleAdd((5, 5))")
            },
            CacheCheck {
                query: q("inspector::SimpleAdd", "inspector::SimpleAdd((5, 5))"),
                valid: false
            },
            EarlyCutoffCheck {
                query: q("inspector::SimpleAdd", "inspector::SimpleAdd((5, 5))"),
                output_changed: true
            },
            QueryEnd {
                query: q("inspector::SimpleAdd", "inspector::SimpleAdd((5, 5))"),
                result: Changed
            },
        ]
    );
}

#[test]
fn test_cycle_detection_events() {
    use EventKind::*;

    // Create mutually recursive queries
    #[derive(Clone)]
    struct CycleA(i32);
    #[derive(Clone)]
    struct CycleB(i32);

    impl query_flow::Query for CycleA {
        type CacheKey = i32;
        type Output = i32;

        fn cache_key(&self) -> Self::CacheKey {
            self.0
        }

        fn query(self, ctx: &mut QueryContext) -> Result<Self::Output, QueryError> {
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

        fn query(self, ctx: &mut QueryContext) -> Result<Self::Output, QueryError> {
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

    assert_eq!(
        to_kinds(&collector.trace()),
        vec![
            QueryStart {
                query: q(
                    "inspector::test_cycle_detection_events::CycleA",
                    "inspector::test_cycle_detection_events::CycleA(1)"
                )
            },
            CacheCheck {
                query: q(
                    "inspector::test_cycle_detection_events::CycleA",
                    "inspector::test_cycle_detection_events::CycleA(1)"
                ),
                valid: false
            },
            DependencyRegistered {
                parent: q(
                    "inspector::test_cycle_detection_events::CycleA",
                    "inspector::test_cycle_detection_events::CycleA(1)"
                ),
                dependency: q(
                    "inspector::test_cycle_detection_events::CycleB",
                    "inspector::test_cycle_detection_events::CycleB(1)"
                ),
            },
            QueryStart {
                query: q(
                    "inspector::test_cycle_detection_events::CycleB",
                    "inspector::test_cycle_detection_events::CycleB(1)"
                )
            },
            CacheCheck {
                query: q(
                    "inspector::test_cycle_detection_events::CycleB",
                    "inspector::test_cycle_detection_events::CycleB(1)"
                ),
                valid: false
            },
            DependencyRegistered {
                parent: q(
                    "inspector::test_cycle_detection_events::CycleB",
                    "inspector::test_cycle_detection_events::CycleB(1)"
                ),
                dependency: q(
                    "inspector::test_cycle_detection_events::CycleA",
                    "inspector::test_cycle_detection_events::CycleA(1)"
                ),
            },
            QueryStart {
                query: q(
                    "inspector::test_cycle_detection_events::CycleA",
                    "inspector::test_cycle_detection_events::CycleA(1)"
                )
            },
            EventKind::CycleDetected {
                path: vec![
                    q("", "inspector::test_cycle_detection_events::CycleA(1)"),
                    q("", "inspector::test_cycle_detection_events::CycleB(1)"),
                    q("", "inspector::test_cycle_detection_events::CycleA(1)"),
                ]
            },
            QueryEnd {
                query: q(
                    "inspector::test_cycle_detection_events::CycleA",
                    "inspector::test_cycle_detection_events::CycleA(1)"
                ),
                result: ExecutionResult::CycleDetected
            },
            QueryEnd {
                query: q(
                    "inspector::test_cycle_detection_events::CycleB",
                    "inspector::test_cycle_detection_events::CycleB(1)"
                ),
                result: ExecutionResult::CycleDetected
            },
            QueryEnd {
                query: q(
                    "inspector::test_cycle_detection_events::CycleA",
                    "inspector::test_cycle_detection_events::CycleA(1)"
                ),
                result: ExecutionResult::CycleDetected
            },
        ]
    );
}

#[test]
fn test_query_invalidation_events() {
    use query_flow_inspector::InvalidationReason;
    use EventKind::*;

    let collector = Arc::new(EventCollector::new());
    let runtime = QueryRuntime::new();

    // Populate cache
    runtime.query(SimpleAdd::new(1, 2)).unwrap();

    // Invalidate with tracing
    runtime.set_sink(Some(collector.clone()));
    runtime.invalidate::<SimpleAdd>(&(1, 2));

    assert_eq!(
        to_kinds(&collector.trace()),
        vec![QueryInvalidated {
            query: q("inspector::SimpleAdd", "inspector::SimpleAdd((1, 2))"),
            reason: InvalidationReason::ManualInvalidation,
        }]
    );
}
