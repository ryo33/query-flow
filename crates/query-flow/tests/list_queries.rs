//! Tests for list_queries and list_asset_keys functionality.

use std::sync::atomic::{AtomicU32, Ordering};

use query_flow::{AssetKey, Db, Query, QueryError, QueryRuntime};

// Simple query that doubles a value
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct DoubleQuery {
    value: i32,
}

impl Query for DoubleQuery {
    type CacheKey = i32;
    type Output = i32;

    fn cache_key(&self) -> Self::CacheKey {
        self.value
    }

    fn query(self, _db: &impl Db) -> Result<Self::Output, QueryError> {
        Ok(self.value * 2)
    }

    fn output_eq(old: &Self::Output, new: &Self::Output) -> bool {
        old == new
    }
}

// Asset key for testing list_asset_keys
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct ConfigFile(String);

impl AssetKey for ConfigFile {
    type Asset = String;

    fn asset_eq(old: &Self::Asset, new: &Self::Asset) -> bool {
        old == new
    }
}

// Query that lists all config files
#[derive(Clone)]
struct ListConfigsQuery;

impl Query for ListConfigsQuery {
    type CacheKey = ();
    type Output = Vec<String>;

    fn cache_key(&self) -> Self::CacheKey {}

    fn query(self, db: &impl Db) -> Result<Self::Output, QueryError> {
        let keys = db.list_asset_keys::<ConfigFile>();
        let mut names: Vec<String> = keys.iter().map(|k| k.0.clone()).collect();
        names.sort();
        Ok(names)
    }

    fn output_eq(old: &Self::Output, new: &Self::Output) -> bool {
        old == new
    }
}

#[test]
fn test_list_queries_basic() {
    // Query that aggregates all DoubleQuery results using list_queries
    #[derive(Clone)]
    struct AggregateQuery;

    impl Query for AggregateQuery {
        type CacheKey = ();
        type Output = Vec<i32>;

        fn cache_key(&self) -> Self::CacheKey {}

        fn query(self, db: &impl Db) -> Result<Self::Output, QueryError> {
            let queries = db.list_queries::<DoubleQuery>();
            let mut results = Vec::new();
            for q in queries {
                results.push(*db.query(q)?);
            }
            results.sort();
            Ok(results)
        }

        fn output_eq(old: &Self::Output, new: &Self::Output) -> bool {
            old == new
        }
    }

    let runtime = QueryRuntime::new();

    // Execute some queries
    runtime.query(DoubleQuery { value: 1 }).unwrap();
    runtime.query(DoubleQuery { value: 2 }).unwrap();
    runtime.query(DoubleQuery { value: 3 }).unwrap();

    // Aggregate should see all three
    let result = runtime.query(AggregateQuery).unwrap();
    assert_eq!(*result, vec![2, 4, 6]);
}

#[test]
fn test_list_queries_invalidation_on_add() {
    static AGGREGATE_COUNT: AtomicU32 = AtomicU32::new(0);

    // Query that aggregates all DoubleQuery results using list_queries
    #[derive(Clone)]
    struct TrackedAggregateQuery;

    impl Query for TrackedAggregateQuery {
        type CacheKey = ();
        type Output = Vec<i32>;

        fn cache_key(&self) -> Self::CacheKey {}

        fn query(self, db: &impl Db) -> Result<Self::Output, QueryError> {
            AGGREGATE_COUNT.fetch_add(1, Ordering::SeqCst);
            let queries = db.list_queries::<DoubleQuery>();
            let mut results = Vec::new();
            for q in queries {
                results.push(*db.query(q)?);
            }
            results.sort();
            Ok(results)
        }

        fn output_eq(old: &Self::Output, new: &Self::Output) -> bool {
            old == new
        }
    }

    let runtime = QueryRuntime::new();
    AGGREGATE_COUNT.store(0, Ordering::SeqCst);

    // Execute initial queries
    runtime.query(DoubleQuery { value: 1 }).unwrap();
    runtime.query(DoubleQuery { value: 2 }).unwrap();

    // First aggregate
    let result = runtime.query(TrackedAggregateQuery).unwrap();
    assert_eq!(*result, vec![2, 4]);
    assert_eq!(AGGREGATE_COUNT.load(Ordering::SeqCst), 1);

    // Cache hit - should not recompute
    let result = runtime.query(TrackedAggregateQuery).unwrap();
    assert_eq!(*result, vec![2, 4]);
    assert_eq!(AGGREGATE_COUNT.load(Ordering::SeqCst), 1);

    // Add a new query - this should invalidate the aggregate
    runtime.query(DoubleQuery { value: 3 }).unwrap();

    // Should recompute with the new query
    let result = runtime.query(TrackedAggregateQuery).unwrap();
    assert_eq!(*result, vec![2, 4, 6]);
    assert_eq!(AGGREGATE_COUNT.load(Ordering::SeqCst), 2);
}

#[test]
fn test_list_queries_no_invalidation_on_value_change() {
    static AGGREGATE_COUNT: AtomicU32 = AtomicU32::new(0);

    // Query that only uses list_queries, not individual queries
    #[derive(Clone)]
    struct ListOnlyQuery;

    impl Query for ListOnlyQuery {
        type CacheKey = ();
        type Output = usize;

        fn cache_key(&self) -> Self::CacheKey {}

        fn query(self, db: &impl Db) -> Result<Self::Output, QueryError> {
            AGGREGATE_COUNT.fetch_add(1, Ordering::SeqCst);
            let queries = db.list_queries::<DoubleQuery>();
            // Just count, don't query individual ones
            Ok(queries.len())
        }

        fn output_eq(old: &Self::Output, new: &Self::Output) -> bool {
            old == new
        }
    }

    let runtime = QueryRuntime::new();
    AGGREGATE_COUNT.store(0, Ordering::SeqCst);

    // Execute initial query
    runtime.query(DoubleQuery { value: 1 }).unwrap();

    // First list-only query
    let result = runtime.query(ListOnlyQuery).unwrap();
    assert_eq!(*result, 1);
    assert_eq!(AGGREGATE_COUNT.load(Ordering::SeqCst), 1);

    // Invalidate the individual query (not the set)
    runtime.invalidate::<DoubleQuery>(&1);

    // The list-only query should still be cached because:
    // 1. It doesn't depend on individual query values
    // 2. The SET didn't change (no add/remove)
    let result = runtime.query(ListOnlyQuery).unwrap();
    assert_eq!(*result, 1);
    assert_eq!(AGGREGATE_COUNT.load(Ordering::SeqCst), 1);
}

#[test]
fn test_list_queries_individual_dependency() {
    #[derive(Clone)]
    struct AggregateQuery2;

    impl Query for AggregateQuery2 {
        type CacheKey = ();
        type Output = Vec<i32>;

        fn cache_key(&self) -> Self::CacheKey {}

        fn query(self, db: &impl Db) -> Result<Self::Output, QueryError> {
            let queries = db.list_queries::<DoubleQuery>();
            let mut results = Vec::new();
            for q in queries {
                results.push(*db.query(q)?);
            }
            results.sort();
            Ok(results)
        }

        fn output_eq(old: &Self::Output, new: &Self::Output) -> bool {
            old == new
        }
    }

    let runtime = QueryRuntime::new();

    // Execute queries
    runtime.query(DoubleQuery { value: 1 }).unwrap();
    runtime.query(DoubleQuery { value: 2 }).unwrap();

    // Aggregate depends on both the set and individual queries
    let result = runtime.query(AggregateQuery2).unwrap();
    assert_eq!(*result, vec![2, 4]);

    // Invalidate an individual query
    runtime.invalidate::<DoubleQuery>(&1);

    // Re-execute individual query with same key
    runtime.query(DoubleQuery { value: 1 }).unwrap();

    // Aggregate should still work correctly
    let result = runtime.query(AggregateQuery2).unwrap();
    assert_eq!(*result, vec![2, 4]);
}

#[test]
fn test_list_asset_keys_basic() {
    let runtime = QueryRuntime::new();

    // Resolve some assets
    runtime.resolve_asset(ConfigFile("app.json".to_string()), "{}".to_string());
    runtime.resolve_asset(ConfigFile("db.json".to_string()), "{}".to_string());

    // List should see both
    let result = runtime.query(ListConfigsQuery).unwrap();
    assert_eq!(*result, vec!["app.json", "db.json"]);
}

#[test]
fn test_list_asset_keys_invalidation_on_remove() {
    static LIST_COUNT: AtomicU32 = AtomicU32::new(0);

    #[derive(Clone)]
    struct TrackedListConfigs;

    impl Query for TrackedListConfigs {
        type CacheKey = ();
        type Output = Vec<String>;

        fn cache_key(&self) -> Self::CacheKey {}

        fn query(self, db: &impl Db) -> Result<Self::Output, QueryError> {
            LIST_COUNT.fetch_add(1, Ordering::SeqCst);
            let keys = db.list_asset_keys::<ConfigFile>();
            let mut names: Vec<String> = keys.iter().map(|k| k.0.clone()).collect();
            names.sort();
            Ok(names)
        }

        fn output_eq(old: &Self::Output, new: &Self::Output) -> bool {
            old == new
        }
    }

    let runtime = QueryRuntime::new();
    LIST_COUNT.store(0, Ordering::SeqCst);

    // Resolve assets
    runtime.resolve_asset(ConfigFile("app.json".to_string()), "{}".to_string());
    runtime.resolve_asset(ConfigFile("db.json".to_string()), "{}".to_string());

    // First list
    let result = runtime.query(TrackedListConfigs).unwrap();
    assert_eq!(*result, vec!["app.json", "db.json"]);
    assert_eq!(LIST_COUNT.load(Ordering::SeqCst), 1);

    // Cache hit
    let result = runtime.query(TrackedListConfigs).unwrap();
    assert_eq!(*result, vec!["app.json", "db.json"]);
    assert_eq!(LIST_COUNT.load(Ordering::SeqCst), 1);

    // Remove an asset - should invalidate list
    runtime.remove_asset(&ConfigFile("db.json".to_string()));

    // Should recompute
    let result = runtime.query(TrackedListConfigs).unwrap();
    assert_eq!(*result, vec!["app.json"]);
    assert_eq!(LIST_COUNT.load(Ordering::SeqCst), 2);
}

#[test]
fn test_list_asset_keys_no_invalidation_on_value_change() {
    static LIST_COUNT: AtomicU32 = AtomicU32::new(0);

    #[derive(Clone)]
    struct TrackedListConfigs2;

    impl Query for TrackedListConfigs2 {
        type CacheKey = ();
        type Output = Vec<String>;

        fn cache_key(&self) -> Self::CacheKey {}

        fn query(self, db: &impl Db) -> Result<Self::Output, QueryError> {
            LIST_COUNT.fetch_add(1, Ordering::SeqCst);
            let keys = db.list_asset_keys::<ConfigFile>();
            let mut names: Vec<String> = keys.iter().map(|k| k.0.clone()).collect();
            names.sort();
            Ok(names)
        }

        fn output_eq(old: &Self::Output, new: &Self::Output) -> bool {
            old == new
        }
    }

    let runtime = QueryRuntime::new();
    LIST_COUNT.store(0, Ordering::SeqCst);

    // Resolve asset
    runtime.resolve_asset(ConfigFile("app.json".to_string()), "v1".to_string());

    // First list
    let result = runtime.query(TrackedListConfigs2).unwrap();
    assert_eq!(*result, vec!["app.json"]);
    assert_eq!(LIST_COUNT.load(Ordering::SeqCst), 1);

    // Update asset value (same key, different value)
    runtime.resolve_asset(ConfigFile("app.json".to_string()), "v2".to_string());

    // List should still be cached because the SET didn't change
    let result = runtime.query(TrackedListConfigs2).unwrap();
    assert_eq!(*result, vec!["app.json"]);
    assert_eq!(LIST_COUNT.load(Ordering::SeqCst), 1);
}

#[test]
fn test_list_asset_keys_with_individual_asset_dependency() {
    static CONTENT_COUNT: AtomicU32 = AtomicU32::new(0);

    // Query that lists all config files and reads their contents
    #[derive(Clone)]
    struct AllConfigContents;

    impl Query for AllConfigContents {
        type CacheKey = ();
        type Output = Vec<(String, String)>;

        fn cache_key(&self) -> Self::CacheKey {}

        fn query(self, db: &impl Db) -> Result<Self::Output, QueryError> {
            CONTENT_COUNT.fetch_add(1, Ordering::SeqCst);
            let keys = db.list_asset_keys::<ConfigFile>();
            let mut results = Vec::new();
            for key in keys {
                let key_name = key.0.clone();
                if let Some(content) = db.asset(key)?.get() {
                    results.push((key_name, (**content).clone()));
                }
            }
            results.sort();
            Ok(results)
        }

        fn output_eq(old: &Self::Output, new: &Self::Output) -> bool {
            old == new
        }
    }

    let runtime = QueryRuntime::new();
    CONTENT_COUNT.store(0, Ordering::SeqCst);

    // Resolve assets
    runtime.resolve_asset(ConfigFile("app.json".to_string()), "v1".to_string());

    // First query
    let result = runtime.query(AllConfigContents).unwrap();
    assert_eq!(*result, vec![("app.json".to_string(), "v1".to_string())]);
    assert_eq!(CONTENT_COUNT.load(Ordering::SeqCst), 1);

    // Update asset value - should invalidate because we depend on individual assets too
    runtime.resolve_asset(ConfigFile("app.json".to_string()), "v2".to_string());

    // Should recompute because of individual asset dependency
    let result = runtime.query(AllConfigContents).unwrap();
    assert_eq!(*result, vec![("app.json".to_string(), "v2".to_string())]);
    assert_eq!(CONTENT_COUNT.load(Ordering::SeqCst), 2);
}

#[test]
fn test_list_queries_empty() {
    #[derive(Clone)]
    struct AggregateQuery3;

    impl Query for AggregateQuery3 {
        type CacheKey = ();
        type Output = Vec<i32>;

        fn cache_key(&self) -> Self::CacheKey {}

        fn query(self, db: &impl Db) -> Result<Self::Output, QueryError> {
            let queries = db.list_queries::<DoubleQuery>();
            let mut results = Vec::new();
            for q in queries {
                results.push(*db.query(q)?);
            }
            results.sort();
            Ok(results)
        }

        fn output_eq(old: &Self::Output, new: &Self::Output) -> bool {
            old == new
        }
    }

    let runtime = QueryRuntime::new();

    // Query aggregate before any DoubleQuery has been executed
    let result = runtime.query(AggregateQuery3).unwrap();
    assert_eq!(*result, Vec::<i32>::new());
}

#[test]
fn test_list_asset_keys_empty() {
    let runtime = QueryRuntime::new();

    // Query list before any assets have been resolved
    let result = runtime.query(ListConfigsQuery).unwrap();
    assert_eq!(*result, Vec::<String>::new());
}

#[test]
fn test_list_asset_keys_invalidation_on_add() {
    static LIST_COUNT: AtomicU32 = AtomicU32::new(0);

    #[derive(Clone)]
    struct TrackedListConfigs3;

    impl Query for TrackedListConfigs3 {
        type CacheKey = ();
        type Output = Vec<String>;

        fn cache_key(&self) -> Self::CacheKey {}

        fn query(self, db: &impl Db) -> Result<Self::Output, QueryError> {
            LIST_COUNT.fetch_add(1, Ordering::SeqCst);
            let keys = db.list_asset_keys::<ConfigFile>();
            let mut names: Vec<String> = keys.iter().map(|k| k.0.clone()).collect();
            names.sort();
            Ok(names)
        }

        fn output_eq(old: &Self::Output, new: &Self::Output) -> bool {
            old == new
        }
    }

    let runtime = QueryRuntime::new();
    LIST_COUNT.store(0, Ordering::SeqCst);

    // Resolve first asset
    runtime.resolve_asset(ConfigFile("app.json".to_string()), "{}".to_string());

    // First list
    let result = runtime.query(TrackedListConfigs3).unwrap();
    assert_eq!(*result, vec!["app.json"]);
    assert_eq!(LIST_COUNT.load(Ordering::SeqCst), 1);

    // Add another asset - should invalidate list
    runtime.resolve_asset(ConfigFile("db.json".to_string()), "{}".to_string());

    // Should recompute
    let result = runtime.query(TrackedListConfigs3).unwrap();
    assert_eq!(*result, vec!["app.json", "db.json"]);
    assert_eq!(LIST_COUNT.load(Ordering::SeqCst), 2);
}
