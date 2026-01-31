//! Tests for generic query composition - queries that take other queries as arguments.
//!
//! This tests the pattern where a query receives other query types as generic parameters,
//! executes them, and combines their results.

use query_flow::{query, Cachable, Db, Query, QueryError, QueryRuntime};

// =============================================================================
// Basic Numeric Queries (building blocks)
// =============================================================================

#[query]
fn constant(db: &impl Db, value: i32) -> Result<i32, QueryError> {
    let _ = db;
    Ok(value)
}

#[query]
fn double(db: &impl Db, value: i32) -> Result<i32, QueryError> {
    let _ = db;
    Ok(value * 2)
}

#[query]
fn square(db: &impl Db, value: i32) -> Result<i32, QueryError> {
    let _ = db;
    Ok(value * value)
}

// =============================================================================
// Query Composition: Add Two Queries
// =============================================================================

/// A query that takes two other queries and adds their results.
///
/// Both T and U must:
/// - Be Query types with i32 output
/// - Be Cachable (for the struct fields)
#[query]
fn add_queries<T, U>(db: &impl Db, query1: T, query2: U) -> Result<i32, QueryError>
where
    T: Query<Output = i32> + Cachable,
    U: Query<Output = i32> + Cachable,
{
    let result1 = db.query(query1)?;
    let result2 = db.query(query2)?;
    Ok(*result1 + *result2)
}

#[test]
fn test_add_two_constant_queries() {
    let runtime = QueryRuntime::new();

    let result = runtime.query(AddQueries::new(Constant::new(10), Constant::new(20)));
    assert_eq!(*result.unwrap(), 30);
}

#[test]
fn test_add_different_query_types() {
    let runtime = QueryRuntime::new();

    // Add a constant and a doubled value
    let result = runtime.query(AddQueries::new(
        Constant::new(5), // 5
        Double::new(10),  // 20
    ));
    assert_eq!(*result.unwrap(), 25);
}

#[test]
fn test_add_queries_caching() {
    let runtime = QueryRuntime::new();

    // First call
    let result1 = runtime.query(AddQueries::new(Constant::new(1), Constant::new(2)));
    // Second call with same queries - should hit cache
    let result2 = runtime.query(AddQueries::new(Constant::new(1), Constant::new(2)));

    assert!(std::sync::Arc::ptr_eq(&result1.unwrap(), &result2.unwrap()));
}

// =============================================================================
// Query Composition: Apply Function to Query Result
// =============================================================================

/// A query that applies a transformation to another query's result.
#[query]
fn map_query<T, F>(db: &impl Db, inner: T, func: F) -> Result<i32, QueryError>
where
    T: Query<Output = i32> + Cachable,
    F: Fn(i32) -> i32 + Cachable,
{
    let result = db.query(inner)?;
    Ok(func(*result))
}

#[test]
fn test_map_query_with_closure() {
    let runtime = QueryRuntime::new();

    // Note: Only fn pointers are Cachable, not closures with captures
    fn add_one(x: i32) -> i32 {
        x + 1
    }

    let result = runtime.query(MapQuery::new(Constant::new(10), add_one as fn(i32) -> i32));
    assert_eq!(*result.unwrap(), 11);
}

// =============================================================================
// Query Composition: Chain of Queries
// =============================================================================

/// Execute query T, then use its result as input to query U.
#[query]
fn chain<T, U>(db: &impl Db, first: T, second_factory: U) -> Result<i32, QueryError>
where
    T: Query<Output = i32> + Cachable,
    U: Fn(i32) -> Double + Cachable,
{
    let first_result = db.query(first)?;
    let second_query = second_factory(*first_result);
    let second_result = db.query(second_query)?;
    Ok(*second_result)
}

#[test]
fn test_chain_queries() {
    let runtime = QueryRuntime::new();

    // Constant(5) -> Double(5) = 10
    fn make_double(x: i32) -> Double {
        Double::new(x)
    }

    let result = runtime.query(Chain::new(
        Constant::new(5),
        make_double as fn(i32) -> Double,
    ));
    assert_eq!(*result.unwrap(), 10);
}

// =============================================================================
// Query Composition: Reduce Multiple Queries
// =============================================================================

/// Sum the results of multiple queries of the same type.
#[query]
fn sum_queries<T>(db: &impl Db, queries: Vec<T>) -> Result<i32, QueryError>
where
    T: Query<Output = i32> + Cachable,
{
    let mut sum = 0;
    for q in queries {
        sum += *db.query(q)?;
    }
    Ok(sum)
}

#[test]
fn test_sum_multiple_queries() {
    let runtime = QueryRuntime::new();

    let result = runtime.query(SumQueries::new(vec![
        Constant::new(1),
        Constant::new(2),
        Constant::new(3),
        Constant::new(4),
    ]));
    assert_eq!(*result.unwrap(), 10);
}

#[test]
fn test_sum_empty_queries() {
    let runtime = QueryRuntime::new();

    let result = runtime.query(SumQueries::<Constant>::new(vec![]));
    assert_eq!(*result.unwrap(), 0);
}

// =============================================================================
// Query Composition: Conditional Execution
// =============================================================================

/// Execute one of two queries based on a condition.
#[query]
fn select_query<T, U>(
    db: &impl Db,
    condition: bool,
    if_true: T,
    if_false: U,
) -> Result<i32, QueryError>
where
    T: Query<Output = i32> + Cachable,
    U: Query<Output = i32> + Cachable,
{
    if condition {
        Ok(*db.query(if_true)?)
    } else {
        Ok(*db.query(if_false)?)
    }
}

#[test]
fn test_select_true_branch() {
    let runtime = QueryRuntime::new();

    let result = runtime.query(SelectQuery::new(
        true,
        Constant::new(100),
        Constant::new(200),
    ));
    assert_eq!(*result.unwrap(), 100);
}

#[test]
fn test_select_false_branch() {
    let runtime = QueryRuntime::new();

    let result = runtime.query(SelectQuery::new(
        false,
        Constant::new(100),
        Constant::new(200),
    ));
    assert_eq!(*result.unwrap(), 200);
}

// =============================================================================
// Query Composition: Nested Composition
// =============================================================================

#[test]
fn test_deeply_nested_composition() {
    let runtime = QueryRuntime::new();

    // ((5 + 10) + (3 * 3)) = 15 + 9 = 24
    let inner1 = AddQueries::new(Constant::new(5), Constant::new(10));
    let inner2 = Square::new(3);

    let result = runtime.query(AddQueries::new(inner1, inner2));
    assert_eq!(*result.unwrap(), 24);
}

// =============================================================================
// Query Composition: Generic Output Types
// =============================================================================

/// A wrapper that can hold any query result.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct QueryResult<T> {
    value: T,
    computed: bool,
}

/// Execute a query and wrap its result.
#[query]
fn wrap_result<T>(db: &impl Db, inner: T) -> Result<QueryResult<i32>, QueryError>
where
    T: Query<Output = i32> + Cachable,
{
    let value = *db.query(inner)?;
    Ok(QueryResult {
        value,
        computed: true,
    })
}

#[test]
fn test_wrap_query_result() {
    let runtime = QueryRuntime::new();

    let result = runtime.query(WrapResult::new(Constant::new(42)));
    let wrapped = result.unwrap();
    assert_eq!(wrapped.value, 42);
    assert!(wrapped.computed);
}

// =============================================================================
// Query Composition: Error Propagation
// =============================================================================

#[query]
fn failing_query(db: &impl Db, should_fail: bool) -> Result<i32, QueryError> {
    let _ = db;
    if should_fail {
        Err(anyhow::anyhow!("intentional failure").into())
    } else {
        Ok(42)
    }
}

#[test]
fn test_composed_query_propagates_error() {
    let runtime = QueryRuntime::new();

    // One of the inner queries fails
    let result = runtime.query(AddQueries::new(Constant::new(10), FailingQuery::new(true)));

    assert!(result.is_err());
}

#[test]
fn test_composed_query_succeeds_when_all_succeed() {
    let runtime = QueryRuntime::new();

    let result = runtime.query(AddQueries::new(Constant::new(10), FailingQuery::new(false)));

    assert_eq!(*result.unwrap(), 52); // 10 + 42
}
