//! Tests for generic query support.
//!
//! Note: According to the design, the macro does NOT automatically add bounds.
//! Users must specify the required bounds:
//!
//! - For type parameters used in fields: `T: Cachable` (provides Hash + Eq + Clone + Debug + Send + Sync + 'static)
//! - For type parameters only in output: `T: QueryOutput` (provides PartialEq + Send + Sync + 'static)

use query_flow::{query, Cachable, Db, QueryError, QueryOutput, QueryRuntime};

// =============================================================================
// Helper Types
// =============================================================================

/// A simple wrapper type for testing generic parameters
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
struct Wrapper<T>(T);

// =============================================================================
// Generic Query: Output Only (PhantomData)
// =============================================================================

/// A generic query where T is only used in the output (PhantomData case).
/// Uses std::str::FromStr - a real stdlib trait.
#[query]
fn parse_from_str<T>(db: &impl Db, text: String) -> Result<T, QueryError>
where
    T: std::str::FromStr + QueryOutput,
    T::Err: std::fmt::Display,
{
    let _ = db;
    text.parse::<T>()
        .map_err(|e| anyhow::anyhow!("parse error: {}", e).into())
}

#[test]
fn test_generic_query_different_types() {
    let runtime = QueryRuntime::new();

    // Parse as i32
    let int_result = runtime.query(ParseFromStr::<i32>::new("42".to_string()));
    assert_eq!(*int_result.unwrap(), 42);

    // Parse as u64
    let uint_result = runtime.query(ParseFromStr::<u64>::new("12345".to_string()));
    assert_eq!(*uint_result.unwrap(), 12345);

    // Parse as f64
    let float_result = runtime.query(ParseFromStr::<f64>::new("3.14".to_string()));
    assert!((*float_result.unwrap() - 3.14).abs() < 0.001);
}

#[test]
fn test_generic_query_type_determines_cache_key() {
    let runtime = QueryRuntime::new();

    // Same input string, different types should be different cache entries
    let text = "42".to_string();

    let i32_result = runtime.query(ParseFromStr::<i32>::new(text.clone()));
    assert_eq!(*i32_result.unwrap(), 42i32);

    let u64_result = runtime.query(ParseFromStr::<u64>::new(text.clone()));
    assert_eq!(*u64_result.unwrap(), 42u64);

    // Both should be cached independently (different TypeIds)
    let i32_again = runtime.query(ParseFromStr::<i32>::new(text.clone()));
    assert_eq!(*i32_again.unwrap(), 42i32);

    let u64_again = runtime.query(ParseFromStr::<u64>::new(text));
    assert_eq!(*u64_again.unwrap(), 42u64);
}

// =============================================================================
// Generic Query: Type Parameter in Field
// =============================================================================

/// A generic query where T is used as a field type.
/// Cachable provides Hash + Eq + Clone + Debug + Send + Sync + 'static.
#[query]
fn wrap_value<T: Cachable>(db: &impl Db, value: T) -> Result<Wrapper<T>, QueryError> {
    let _ = db;
    Ok(Wrapper(value))
}

#[test]
fn test_generic_query_with_type_in_field() {
    let runtime = QueryRuntime::new();

    let str_result = runtime.query(WrapValue::new("hello".to_string()));
    assert_eq!(*str_result.unwrap(), Wrapper("hello".to_string()));

    let int_result = runtime.query(WrapValue::new(42i32));
    assert_eq!(*int_result.unwrap(), Wrapper(42));
}

#[test]
fn test_generic_query_caching_with_type_in_field() {
    let runtime = QueryRuntime::new();

    // First call
    let result1 = runtime.query(WrapValue::new("test".to_string()));
    assert_eq!(*result1.unwrap(), Wrapper("test".to_string()));

    // Second call with same value - should hit cache
    let result2 = runtime.query(WrapValue::new("test".to_string()));
    assert_eq!(*result2.unwrap(), Wrapper("test".to_string()));

    // Different value - should be a new cache entry
    let result3 = runtime.query(WrapValue::new("other".to_string()));
    assert_eq!(*result3.unwrap(), Wrapper("other".to_string()));
}

// =============================================================================
// Generic Query: Multiple Type Parameters
// =============================================================================

/// A generic query with multiple type parameters.
/// T is used in field (Cachable), U is only in output (QueryOutput).
#[query]
fn convert<T: Cachable, U: QueryOutput + From<T>>(
    db: &impl Db,
    input: T,
) -> Result<U, QueryError> {
    let _ = db;
    Ok(U::from(input))
}

#[test]
fn test_generic_query_multiple_params() {
    let runtime = QueryRuntime::new();

    // Convert i32 to i64
    let result = runtime.query(Convert::<i32, i64>::new(42));
    assert_eq!(*result.unwrap(), 42i64);

    // Convert u8 to u32
    let result2 = runtime.query(Convert::<u8, u32>::new(255));
    assert_eq!(*result2.unwrap(), 255u32);
}

// =============================================================================
// Generic Query: With Where Clause
// =============================================================================

/// A generic query with where clause.
/// This is a simpler example that doesn't have unused type params in phantom data.
#[query]
fn format_value<T>(db: &impl Db, value: T) -> Result<String, QueryError>
where
    T: Cachable + std::fmt::Display,
{
    let _ = db;
    Ok(format!("formatted: {}", value))
}

#[test]
fn test_generic_query_with_where_clause() {
    let runtime = QueryRuntime::new();

    let result = runtime.query(FormatValue::new("hello".to_string()));
    assert_eq!(*result.unwrap(), "formatted: hello");

    let result2 = runtime.query(FormatValue::new(42i32));
    assert_eq!(*result2.unwrap(), "formatted: 42");
}

// =============================================================================
// Generic Query: Dependencies Between Generic Queries
// =============================================================================

#[query]
fn get_length<T: Cachable + AsRef<str>>(db: &impl Db, value: T) -> Result<usize, QueryError> {
    let _ = db;
    Ok(value.as_ref().len())
}

#[query]
fn get_double_length<T: Cachable + AsRef<str>>(
    db: &impl Db,
    value: T,
) -> Result<usize, QueryError> {
    let len = db.query(GetLength::new(value))?;
    Ok(*len * 2)
}

#[test]
fn test_generic_query_dependencies() {
    let runtime = QueryRuntime::new();

    let len = runtime.query(GetLength::new("hello".to_string()));
    assert_eq!(*len.unwrap(), 5);

    let double_len = runtime.query(GetDoubleLength::new("hello".to_string()));
    assert_eq!(*double_len.unwrap(), 10);
}

// =============================================================================
// Generic Query: With Custom Debug
// =============================================================================

#[query(debug = "{Self}({id})")]
fn fetch_by_id<T: Cachable + Default>(db: &impl Db, id: u64) -> Result<T, QueryError> {
    let _ = db;
    let _ = id;
    Ok(T::default())
}

#[test]
fn test_generic_query_with_custom_debug() {
    let query = FetchById::<String>::new(42);
    let debug_str = format!("{:?}", query);
    assert_eq!(debug_str, "FetchById(42)");
}

#[test]
fn test_generic_query_custom_debug_execution() {
    let runtime = QueryRuntime::new();

    let result = runtime.query(FetchById::<i32>::new(1));
    assert_eq!(*result.unwrap(), 0); // Default for i32
}

// =============================================================================
// Generic Query: Singleton
// =============================================================================

#[query(singleton)]
fn get_config<T: Cachable + Default>(db: &impl Db, _format: String) -> Result<T, QueryError> {
    let _ = db;
    Ok(T::default())
}

#[test]
fn test_generic_singleton_query() {
    let runtime = QueryRuntime::new();

    // All instances with same T share one cache entry
    let result1 = runtime.query(GetConfig::<String>::new("json".to_string()));
    assert_eq!(*result1.unwrap(), String::default());

    let result2 = runtime.query(GetConfig::<String>::new("yaml".to_string()));
    assert_eq!(*result2.unwrap(), String::default());

    // Different T is a different cache entry
    let result3 = runtime.query(GetConfig::<Vec<u8>>::new("json".to_string()));
    assert_eq!(*result3.unwrap(), Vec::<u8>::default());
}

// =============================================================================
// Generic Query: With Keys Subset
// =============================================================================

#[query(keys(key))]
fn lookup_with_opts<T: Cachable + Default>(
    db: &impl Db,
    key: String,
    verbose: bool,
) -> Result<T, QueryError> {
    let _ = (db, key, verbose);
    Ok(T::default())
}

#[test]
fn test_generic_query_with_keys() {
    let runtime = QueryRuntime::new();

    // Same key but different verbose value should hit cache
    let result1 = runtime.query(LookupWithOpts::<String>::new("test".to_string(), false));
    assert_eq!(*result1.unwrap(), String::default());

    let result2 = runtime.query(LookupWithOpts::<String>::new("test".to_string(), true));
    assert_eq!(*result2.unwrap(), String::default());

    // Different key is a different cache entry
    let result3 = runtime.query(LookupWithOpts::<String>::new("other".to_string(), false));
    assert_eq!(*result3.unwrap(), String::default());
}

// =============================================================================
// Generic Query: Error Case
// =============================================================================

#[test]
fn test_generic_query_error() {
    let runtime = QueryRuntime::new();

    // Invalid string for i32 parsing
    let result = runtime.query(ParseFromStr::<i32>::new("not_a_number".to_string()));
    assert!(result.is_err());
}

// =============================================================================
// Generic Query: Const Generics
// =============================================================================

#[query]
fn fixed_buffer<const N: usize>(db: &impl Db, seed: u8) -> Result<[u8; N], QueryError> {
    let _ = db;
    Ok([seed; N])
}

#[test]
fn test_const_generic_query() {
    let runtime = QueryRuntime::new();

    // Different const values produce different types
    let result4 = runtime.query(FixedBuffer::<4>::new(42));
    assert_eq!(*result4.unwrap(), [42u8; 4]);

    let result8 = runtime.query(FixedBuffer::<8>::new(42));
    assert_eq!(*result8.unwrap(), [42u8; 8]);
}

#[test]
fn test_const_generic_caching() {
    let runtime = QueryRuntime::new();

    // Same const and seed should hit cache
    let result1 = runtime.query(FixedBuffer::<4>::new(1));
    let result2 = runtime.query(FixedBuffer::<4>::new(1));
    assert_eq!(*result1.unwrap(), *result2.unwrap());

    // Different const is a different cache entry
    let result3 = runtime.query(FixedBuffer::<8>::new(1));
    assert_eq!(result3.unwrap().len(), 8);
}

// =============================================================================
// Generic Query: Combined Type and Const Generics
// =============================================================================

#[query]
fn create_array<T: Cachable + Default + Copy, const N: usize>(
    db: &impl Db,
    _marker: String,
) -> Result<[T; N], QueryError> {
    let _ = db;
    Ok([T::default(); N])
}

#[test]
fn test_combined_type_and_const_generics() {
    let runtime = QueryRuntime::new();

    let int_array = runtime.query(CreateArray::<i32, 3>::new("test".to_string()));
    assert_eq!(*int_array.unwrap(), [0i32; 3]);

    let byte_array = runtime.query(CreateArray::<u8, 5>::new("test".to_string()));
    assert_eq!(*byte_array.unwrap(), [0u8; 5]);
}

// =============================================================================
// Verify TypeId Distinguishes Generic Instantiations
// =============================================================================

use query_flow::QueryCacheKey;
use std::any::TypeId;

#[test]
fn test_type_id_distinguishes_generic_instantiations() {
    // Verify that different generic instantiations have different TypeIds
    let type_id_i32 = TypeId::of::<ParseFromStr<i32>>();
    let type_id_u64 = TypeId::of::<ParseFromStr<u64>>();
    let type_id_f64 = TypeId::of::<ParseFromStr<f64>>();

    // All should be different
    assert_ne!(type_id_i32, type_id_u64);
    assert_ne!(type_id_i32, type_id_f64);
    assert_ne!(type_id_u64, type_id_f64);
}

#[test]
fn test_query_cache_key_includes_type_id() {
    // Create cache keys with same field values but different type params
    let text = "42".to_string();

    let key_i32 = QueryCacheKey::new(ParseFromStr::<i32>::new(text.clone()));
    let key_u64 = QueryCacheKey::new(ParseFromStr::<u64>::new(text.clone()));

    // QueryCacheKey should distinguish them via query_type (TypeId)
    assert_ne!(key_i32.query_type(), key_u64.query_type());

    // And they should not be equal
    assert_ne!(key_i32, key_u64);
}

#[test]
fn test_cache_returns_same_arc_for_generic_hit() {
    let runtime = QueryRuntime::new();

    // First query
    let result1 = runtime
        .query(ParseFromStr::<i32>::new("42".to_string()))
        .unwrap();
    // Second query with same type and data - should return same Arc
    let result2 = runtime
        .query(ParseFromStr::<i32>::new("42".to_string()))
        .unwrap();

    // Verify same Arc (pointer equality)
    assert!(std::sync::Arc::ptr_eq(&result1, &result2));
}

// =============================================================================
// Verify Cachable and QueryOutput traits work
// =============================================================================

#[test]
fn test_cachable_trait() {
    // Cachable is an alias for CacheKey (Hash + Eq + Debug + Send + Sync + 'static)
    fn assert_cachable<T: Cachable>() {}

    assert_cachable::<String>();
    assert_cachable::<i32>();
    assert_cachable::<(u64, String)>();
}

#[test]
fn test_query_output_trait() {
    // QueryOutput provides PartialEq + Send + Sync + 'static
    fn assert_query_output<T: QueryOutput>() {}

    assert_query_output::<String>();
    assert_query_output::<Vec<u8>>();
    assert_query_output::<i32>();
}
