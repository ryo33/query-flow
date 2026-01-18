//! Integration tests for the Flow Inspector.
//!
//! These tests verify that events are correctly emitted during query execution.

use std::sync::Arc;

use query_flow::{asset_key, query, Db, DurabilityLevel, QueryError, QueryRuntime};
use query_flow_inspector::{
    to_kinds, AssetKey, AssetState, EventCollector, EventKind, EventSinkTracer, ExecutionResult,
    QueryKey,
};

// ============================================================================
// Test Queries
// ============================================================================

#[query]
fn simple_add(db: &impl Db, a: i32, b: i32) -> Result<i32, QueryError> {
    let _ = db;
    Ok(a + b)
}

#[query]
fn double(db: &impl Db, x: i32) -> Result<i32, QueryError> {
    let _ = db;
    Ok(x * 2)
}

#[query]
fn add_then_double(db: &impl Db, a: i32, b: i32) -> Result<i32, QueryError> {
    let sum = db.query(SimpleAdd::new(a, b))?;
    let doubled = db.query(Double::new(*sum))?;
    Ok(*doubled)
}

// Test asset
#[asset_key(asset = String)]
pub struct TestSource(pub String);

#[query]
fn process_source(db: &impl Db, name: String) -> Result<String, QueryError> {
    let source = db.asset(TestSource(name.clone()))?;
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
    let tracer = EventSinkTracer::new(collector.clone());
    let runtime = QueryRuntime::with_tracer(tracer);

    let result = runtime.query(SimpleAdd::new(1, 2)).unwrap();
    assert_eq!(*result, 3);

    assert_eq!(
        to_kinds(&collector.trace()),
        vec![
            QueryStart {
                query: q("inspector::SimpleAdd", "SimpleAdd { a: 1, b: 2 }")
            },
            CacheCheck {
                query: q("inspector::SimpleAdd", "SimpleAdd { a: 1, b: 2 }"),
                valid: false
            },
            EarlyCutoffCheck {
                query: q("inspector::SimpleAdd", "SimpleAdd { a: 1, b: 2 }"),
                output_changed: true
            },
            QueryEnd {
                query: q("inspector::SimpleAdd", "SimpleAdd { a: 1, b: 2 }"),
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
    let tracer = EventSinkTracer::new(collector.clone());
    let runtime = QueryRuntime::with_tracer(tracer);

    // First query to populate cache (clear events after)
    let _ = runtime.query(SimpleAdd::new(1, 2));
    collector.clear();

    // Second query should hit cache
    let result = runtime.query(SimpleAdd::new(1, 2)).unwrap();
    assert_eq!(*result, 3);

    assert_eq!(
        to_kinds(&collector.trace()),
        vec![
            QueryStart {
                query: q("inspector::SimpleAdd", "SimpleAdd { a: 1, b: 2 }")
            },
            CacheCheck {
                query: q("inspector::SimpleAdd", "SimpleAdd { a: 1, b: 2 }"),
                valid: true
            },
            QueryEnd {
                query: q("inspector::SimpleAdd", "SimpleAdd { a: 1, b: 2 }"),
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
    let tracer = EventSinkTracer::new(collector.clone());
    let runtime = QueryRuntime::with_tracer(tracer);

    let result = runtime.query(AddThenDouble::new(2, 3)).unwrap();
    assert_eq!(*result, 10); // (2+3)*2 = 10

    assert_eq!(
        to_kinds(&collector.trace()),
        vec![
            QueryStart {
                query: q("inspector::AddThenDouble", "AddThenDouble { a: 2, b: 3 }")
            },
            CacheCheck {
                query: q("inspector::AddThenDouble", "AddThenDouble { a: 2, b: 3 }"),
                valid: false
            },
            // SimpleAdd(2, 3) = 5
            DependencyRegistered {
                parent: q("inspector::AddThenDouble", "AddThenDouble { a: 2, b: 3 }"),
                dependency: q("inspector::SimpleAdd", "SimpleAdd { a: 2, b: 3 }"),
            },
            QueryStart {
                query: q("inspector::SimpleAdd", "SimpleAdd { a: 2, b: 3 }")
            },
            CacheCheck {
                query: q("inspector::SimpleAdd", "SimpleAdd { a: 2, b: 3 }"),
                valid: false
            },
            EarlyCutoffCheck {
                query: q("inspector::SimpleAdd", "SimpleAdd { a: 2, b: 3 }"),
                output_changed: true
            },
            QueryEnd {
                query: q("inspector::SimpleAdd", "SimpleAdd { a: 2, b: 3 }"),
                result: Changed
            },
            // Double(5) = 10
            DependencyRegistered {
                parent: q("inspector::AddThenDouble", "AddThenDouble { a: 2, b: 3 }"),
                dependency: q("inspector::Double", "Double { x: 5 }"),
            },
            QueryStart {
                query: q("inspector::Double", "Double { x: 5 }")
            },
            CacheCheck {
                query: q("inspector::Double", "Double { x: 5 }"),
                valid: false
            },
            EarlyCutoffCheck {
                query: q("inspector::Double", "Double { x: 5 }"),
                output_changed: true
            },
            QueryEnd {
                query: q("inspector::Double", "Double { x: 5 }"),
                result: Changed
            },
            // AddThenDouble completes
            EarlyCutoffCheck {
                query: q("inspector::AddThenDouble", "AddThenDouble { a: 2, b: 3 }"),
                output_changed: true
            },
            QueryEnd {
                query: q("inspector::AddThenDouble", "AddThenDouble { a: 2, b: 3 }"),
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
    let tracer = EventSinkTracer::new(collector.clone());
    let runtime = QueryRuntime::with_tracer(tracer);

    // Resolve asset first (clear events after)
    runtime.resolve_asset(
        TestSource("test".to_string()),
        "hello".to_string(),
        DurabilityLevel::Volatile,
    );
    collector.clear();

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
                    "ProcessSource { name: \"test\" }"
                )
            },
            CacheCheck {
                query: q(
                    "inspector::ProcessSource",
                    "ProcessSource { name: \"test\" }"
                ),
                valid: false
            },
            AssetDependencyRegistered {
                parent: q(
                    "inspector::ProcessSource",
                    "ProcessSource { name: \"test\" }"
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
                    "ProcessSource { name: \"test\" }"
                ),
                output_changed: true
            },
            QueryEnd {
                query: q(
                    "inspector::ProcessSource",
                    "ProcessSource { name: \"test\" }"
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
    let tracer = EventSinkTracer::new(collector.clone());
    let runtime = QueryRuntime::with_tracer(tracer);

    runtime.resolve_asset(
        TestSource("new".to_string()),
        "content".to_string(),
        DurabilityLevel::Volatile,
    );

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
    let tracer = EventSinkTracer::new(collector.clone());
    let runtime = QueryRuntime::with_tracer(tracer);

    runtime.resolve_asset(
        TestSource("test".to_string()),
        "content".to_string(),
        DurabilityLevel::Volatile,
    );
    collector.clear();

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
    let tracer = EventSinkTracer::new(collector.clone());
    let runtime = QueryRuntime::with_tracer(tracer);

    let result = runtime.query(SimpleAdd::new(5, 5)).unwrap();
    assert_eq!(*result, 10);

    assert_eq!(
        to_kinds(&collector.trace()),
        vec![
            QueryStart {
                query: q("inspector::SimpleAdd", "SimpleAdd { a: 5, b: 5 }")
            },
            CacheCheck {
                query: q("inspector::SimpleAdd", "SimpleAdd { a: 5, b: 5 }"),
                valid: false
            },
            EarlyCutoffCheck {
                query: q("inspector::SimpleAdd", "SimpleAdd { a: 5, b: 5 }"),
                output_changed: true
            },
            QueryEnd {
                query: q("inspector::SimpleAdd", "SimpleAdd { a: 5, b: 5 }"),
                result: Changed
            },
        ]
    );
}

#[test]
fn test_cycle_detection_events() {
    use EventKind::*;

    // Create mutually recursive queries
    #[derive(Clone, Debug, Hash, PartialEq, Eq)]
    struct CycleA(i32);
    #[derive(Clone, Debug, Hash, PartialEq, Eq)]
    struct CycleB(i32);

    impl query_flow::Query for CycleA {
        type Output = i32;

        fn query(self, db: &impl Db) -> Result<Arc<Self::Output>, QueryError> {
            let b = db.query(CycleB(self.0))?;
            Ok(Arc::new(*b + 1))
        }

        fn output_eq(old: &Self::Output, new: &Self::Output) -> bool {
            old == new
        }
    }

    impl query_flow::Query for CycleB {
        type Output = i32;

        fn query(self, db: &impl Db) -> Result<Arc<Self::Output>, QueryError> {
            let a = db.query(CycleA(self.0))?;
            Ok(Arc::new(*a + 1))
        }

        fn output_eq(old: &Self::Output, new: &Self::Output) -> bool {
            old == new
        }
    }

    let collector = Arc::new(EventCollector::new());
    let tracer = EventSinkTracer::new(collector.clone());
    let runtime = QueryRuntime::with_tracer(tracer);

    let result = runtime.query(CycleA(1));
    assert!(matches!(result, Err(QueryError::Cycle { .. })));

    assert_eq!(
        to_kinds(&collector.trace()),
        vec![
            QueryStart {
                query: q(
                    "inspector::test_cycle_detection_events::CycleA",
                    "CycleA(1)"
                )
            },
            CacheCheck {
                query: q(
                    "inspector::test_cycle_detection_events::CycleA",
                    "CycleA(1)"
                ),
                valid: false
            },
            DependencyRegistered {
                parent: q(
                    "inspector::test_cycle_detection_events::CycleA",
                    "CycleA(1)"
                ),
                dependency: q(
                    "inspector::test_cycle_detection_events::CycleB",
                    "CycleB(1)"
                ),
            },
            QueryStart {
                query: q(
                    "inspector::test_cycle_detection_events::CycleB",
                    "CycleB(1)"
                )
            },
            CacheCheck {
                query: q(
                    "inspector::test_cycle_detection_events::CycleB",
                    "CycleB(1)"
                ),
                valid: false
            },
            DependencyRegistered {
                parent: q(
                    "inspector::test_cycle_detection_events::CycleB",
                    "CycleB(1)"
                ),
                dependency: q(
                    "inspector::test_cycle_detection_events::CycleA",
                    "CycleA(1)"
                ),
            },
            QueryStart {
                query: q(
                    "inspector::test_cycle_detection_events::CycleA",
                    "CycleA(1)"
                )
            },
            EventKind::CycleDetected {
                path: vec![q("", "CycleA(1)"), q("", "CycleB(1)"), q("", "CycleA(1)"),]
            },
            QueryEnd {
                query: q(
                    "inspector::test_cycle_detection_events::CycleA",
                    "CycleA(1)"
                ),
                result: ExecutionResult::CycleDetected
            },
            QueryEnd {
                query: q(
                    "inspector::test_cycle_detection_events::CycleB",
                    "CycleB(1)"
                ),
                result: ExecutionResult::CycleDetected
            },
            QueryEnd {
                query: q(
                    "inspector::test_cycle_detection_events::CycleA",
                    "CycleA(1)"
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
    let tracer = EventSinkTracer::new(collector.clone());
    let runtime = QueryRuntime::with_tracer(tracer);

    // Populate cache (clear events after)
    runtime.query(SimpleAdd::new(1, 2)).unwrap();
    collector.clear();

    // Invalidate
    runtime.invalidate(&SimpleAdd::new(1, 2));

    assert_eq!(
        to_kinds(&collector.trace()),
        vec![QueryInvalidated {
            query: q("inspector::SimpleAdd", "SimpleAdd { a: 1, b: 2 }"),
            reason: InvalidationReason::ManualInvalidation,
        }]
    );
}
