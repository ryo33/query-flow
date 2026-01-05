//! Benchmark: Vec vs IndexSet for cycle detection stack.
//!
//! Compares:
//! - Vec<Key> with iter().any() for contains, push(), pop()
//! - IndexSet<Key> with contains(), insert(), pop()

use std::any::TypeId;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

use ahash::AHasher;
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use indexmap::IndexSet;
use std::hint::black_box;

/// Simulates FullCacheKey structure.
#[derive(Clone)]
struct Key {
    query_type: TypeId,
    key_hash: u64,
    #[allow(dead_code)]
    debug_repr: Arc<str>,
}

impl Key {
    fn new(id: u64) -> Self {
        let mut hasher = AHasher::default();
        id.hash(&mut hasher);
        Self {
            query_type: TypeId::of::<()>(),
            key_hash: hasher.finish(),
            debug_repr: Arc::from(format!("Key({})", id)),
        }
    }
}

impl Hash for Key {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.query_type.hash(state);
        self.key_hash.hash(state);
    }
}

impl PartialEq for Key {
    fn eq(&self, other: &Self) -> bool {
        self.query_type == other.query_type && self.key_hash == other.key_hash
    }
}

impl Eq for Key {}

/// Simulate cycle check + push + pop pattern with Vec.
fn vec_cycle_check(stack: &mut Vec<Key>, key: Key) -> bool {
    // Check for cycle
    let has_cycle = stack.iter().any(|k| k == &key);
    if has_cycle {
        return true;
    }
    // Push
    stack.push(key);
    // Pop
    stack.pop();
    false
}

/// Simulate cycle check + push + pop pattern with IndexSet.
fn indexset_cycle_check(stack: &mut IndexSet<Key, ahash::RandomState>, key: Key) -> bool {
    // Check for cycle
    let has_cycle = stack.contains(&key);
    if has_cycle {
        return true;
    }
    // Insert
    stack.insert(key);
    // Pop
    stack.pop();
    false
}

fn benchmark_stack_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("cycle_detection");

    // Test with different stack depths
    for depth in [1, 2, 4, 8, 16, 32] {
        // Prepare keys
        let keys: Vec<Key> = (0..depth).map(Key::new).collect();
        let new_key = Key::new(depth); // Key not in stack

        // Vec benchmark
        group.bench_with_input(BenchmarkId::new("vec", depth), &depth, |b, _| {
            let mut stack: Vec<Key> = keys.clone();
            b.iter(|| {
                vec_cycle_check(black_box(&mut stack), black_box(new_key.clone()));
                // Restore stack for next iteration
                stack.push(new_key.clone());
                stack.pop();
            });
        });

        // IndexSet benchmark
        group.bench_with_input(BenchmarkId::new("indexset", depth), &depth, |b, _| {
            let mut stack: IndexSet<Key, ahash::RandomState> =
                IndexSet::with_hasher(ahash::RandomState::new());
            for key in &keys {
                stack.insert(key.clone());
            }
            b.iter(|| {
                indexset_cycle_check(black_box(&mut stack), black_box(new_key.clone()));
                // Restore stack for next iteration
                stack.insert(new_key.clone());
                stack.pop();
            });
        });
    }

    group.finish();
}

criterion_group!(benches, benchmark_stack_operations);
criterion_main!(benches);
