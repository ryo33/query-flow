//! Tests for the external GC primitives: the `Tracer::on_query_key` access
//! hook and the `remove_if_unused` reclamation path.

use std::sync::Mutex;

use query_flow::{query, Db, FullCacheKey, QueryError, QueryRuntime, SpanId, TraceId, Tracer};

#[query]
fn leaf(db: &impl Db, x: i32) -> Result<i32, QueryError> {
    let _ = db;
    Ok(x)
}

#[query]
fn root(db: &impl Db, x: i32) -> Result<i32, QueryError> {
    Ok(*db.query(Leaf::new(x))? + 1)
}

/// Records every key passed to `on_query_key`, in order.
#[derive(Default)]
struct KeyTracer {
    keys: Mutex<Vec<FullCacheKey>>,
}

impl Tracer for KeyTracer {
    fn new_span_id(&self) -> SpanId {
        SpanId(0)
    }

    fn new_trace_id(&self) -> TraceId {
        TraceId(0)
    }

    fn on_query_key(&self, full_key: &FullCacheKey) {
        self.keys.lock().unwrap().push(full_key.clone());
    }
}

#[test]
fn on_query_key_fires_for_each_query_access() {
    let runtime = QueryRuntime::with_tracer(KeyTracer::default());

    runtime.query(Root::new(1)).unwrap();

    // Root plus the Leaf it pulled in.
    assert_eq!(runtime.tracer().keys.lock().unwrap().len(), 2);
}

#[test]
fn on_query_key_fires_on_cache_hits_too() {
    let runtime = QueryRuntime::with_tracer(KeyTracer::default());

    runtime.query(Leaf::new(1)).unwrap();
    let after_first = runtime.tracer().keys.lock().unwrap().len();

    // A cache hit still counts as an access, otherwise an LRU tracker would
    // evict entries that are being read constantly.
    runtime.query(Leaf::new(1)).unwrap();
    assert_eq!(runtime.tracer().keys.lock().unwrap().len(), after_first + 1);
}

#[test]
fn removing_a_dependent_makes_its_dependency_reclaimable() {
    let runtime = QueryRuntime::new();
    runtime.query(Root::new(1)).unwrap();

    // Leaf is pinned while Root depends on it.
    assert!(!runtime.remove_query_if_unused(&Leaf::new(1)));

    // Removing Root releases the reverse edge it held on Leaf.
    assert!(runtime.remove_query_if_unused(&Root::new(1)));
    assert!(runtime.remove_query_if_unused(&Leaf::new(1)));
}

#[test]
fn gc_sweep_reclaims_every_query() {
    let runtime = QueryRuntime::new();
    runtime.query(Root::new(1)).unwrap();
    runtime.query(Root::new(2)).unwrap();

    // Repeated sweeps peel the graph from the roots down.
    for _ in 0..4 {
        for key in runtime.query_keys() {
            runtime.remove_if_unused(&key);
        }
    }

    assert!(
        runtime.query_keys().is_empty(),
        "leftover keys: {:?}",
        runtime.query_keys()
    );
}

#[test]
fn reclaimed_queries_still_recompute_correctly() {
    let runtime = QueryRuntime::new();
    assert_eq!(*runtime.query(Root::new(1)).unwrap(), 2);

    assert!(runtime.remove_query_if_unused(&Root::new(1)));
    assert!(runtime.remove_query_if_unused(&Leaf::new(1)));

    // Recomputing from an empty cache must produce the same answer.
    assert_eq!(*runtime.query(Root::new(1)).unwrap(), 2);
}
