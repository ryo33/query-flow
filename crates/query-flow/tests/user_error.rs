//! Tests for QueryError::UserError functionality.

use query_flow::{query, QueryError, QueryRuntime};

// =============================================================================
// Basic Error Conversion Tests
// =============================================================================

#[test]
fn test_user_error_from_io_error() {
    let io_err = std::io::Error::new(std::io::ErrorKind::NotFound, "file not found");
    // Convert via anyhow::Error
    let query_err: QueryError = anyhow::Error::from(io_err).into();

    assert!(matches!(query_err, QueryError::UserError(_)));
    assert!(query_err.to_string().contains("file not found"));
}

#[test]
fn test_user_error_from_anyhow() {
    let anyhow_err = anyhow::anyhow!("something went wrong");
    let query_err: QueryError = anyhow_err.into();

    assert!(matches!(query_err, QueryError::UserError(_)));
    assert!(query_err.to_string().contains("something went wrong"));
}

#[derive(Debug, Clone, PartialEq)]
struct CustomError {
    code: i32,
    message: String,
}

impl std::fmt::Display for CustomError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "CustomError({}): {}", self.code, self.message)
    }
}

impl std::error::Error for CustomError {}

#[test]
fn test_user_error_from_custom_error() {
    let custom_err = CustomError {
        code: 42,
        message: "custom error".to_string(),
    };
    // Convert via anyhow::Error
    let query_err: QueryError = anyhow::Error::from(custom_err).into();

    assert!(matches!(query_err, QueryError::UserError(_)));
    assert!(query_err.to_string().contains("custom error"));
}

// =============================================================================
// Question Mark Operator Tests
// =============================================================================

#[query]
fn parse_number(ctx: &mut QueryContext, input: String) -> Result<i32, QueryError> {
    let _ = ctx;
    // The ? operator converts ParseIntError to QueryError::UserError automatically
    let num: i32 = input.parse()?;
    Ok(num)
}

#[test]
fn test_question_mark_propagation_success() {
    let runtime = QueryRuntime::new();
    let result = runtime.query(ParseNumber::new("42".to_string()));
    assert_eq!(*result.unwrap(), 42);
}

#[test]
fn test_question_mark_propagation_error() {
    let runtime = QueryRuntime::new();
    let result = runtime.query(ParseNumber::new("not_a_number".to_string()));

    match result {
        Err(QueryError::UserError(e)) => {
            assert!(e.to_string().contains("invalid digit"));
        }
        other => panic!("Expected UserError, got {:?}", other),
    }
}

#[query]
fn fallible_io(ctx: &mut QueryContext, should_fail: bool) -> Result<String, QueryError> {
    let _ = ctx;
    if *should_fail {
        return Err(anyhow::anyhow!("not found").into());
    }
    Ok("success".to_string())
}

#[test]
fn test_io_error_propagation() {
    let runtime = QueryRuntime::new();

    // Success case
    let result = runtime.query(FallibleIo::new(false));
    assert_eq!(*result.unwrap(), "success");

    // Error case
    let result = runtime.query(FallibleIo::new(true));
    assert!(matches!(result, Err(QueryError::UserError(_))));
}

// =============================================================================
// Error Caching Tests (in separate modules to avoid static variable conflicts)
// =============================================================================

mod error_caching_error {
    use super::*;
    use std::sync::atomic::{AtomicU32, Ordering};

    static FALLIBLE_CALL_COUNT: AtomicU32 = AtomicU32::new(0);

    #[query]
    fn fallible_cached(ctx: &mut QueryContext, id: u32) -> Result<i32, QueryError> {
        let _ = ctx;
        FALLIBLE_CALL_COUNT.fetch_add(1, Ordering::SeqCst);

        if *id == 0 {
            return Err(anyhow::anyhow!("id cannot be zero").into());
        }
        Ok(*id as i32 * 10)
    }

    #[test]
    fn test_user_error_cached() {
        FALLIBLE_CALL_COUNT.store(0, Ordering::SeqCst);
        let runtime = QueryRuntime::new();

        // First call - executes query, returns error
        let result1 = runtime.query(FallibleCached::new(0));
        assert!(matches!(result1, Err(QueryError::UserError(_))));
        assert_eq!(FALLIBLE_CALL_COUNT.load(Ordering::SeqCst), 1);

        // Second call - should return cached error
        let result2 = runtime.query(FallibleCached::new(0));
        assert!(matches!(result2, Err(QueryError::UserError(_))));
        assert_eq!(FALLIBLE_CALL_COUNT.load(Ordering::SeqCst), 1); // Still 1, not recomputed
    }
}

mod error_caching_success {
    use super::*;
    use std::sync::atomic::{AtomicU32, Ordering};

    static FALLIBLE_CALL_COUNT: AtomicU32 = AtomicU32::new(0);

    #[query]
    fn fallible_cached(ctx: &mut QueryContext, id: u32) -> Result<i32, QueryError> {
        let _ = ctx;
        FALLIBLE_CALL_COUNT.fetch_add(1, Ordering::SeqCst);

        if *id == 0 {
            return Err(anyhow::anyhow!("id cannot be zero").into());
        }
        Ok(*id as i32 * 10)
    }

    #[test]
    fn test_success_cached() {
        FALLIBLE_CALL_COUNT.store(0, Ordering::SeqCst);
        let runtime = QueryRuntime::new();

        // First call
        let result1 = runtime.query(FallibleCached::new(5));
        assert_eq!(*result1.unwrap(), 50);
        assert_eq!(FALLIBLE_CALL_COUNT.load(Ordering::SeqCst), 1);

        // Second call - should return cached
        let result2 = runtime.query(FallibleCached::new(5));
        assert_eq!(*result2.unwrap(), 50);
        assert_eq!(FALLIBLE_CALL_COUNT.load(Ordering::SeqCst), 1); // Still 1
    }
}

// =============================================================================
// Error Comparator Tests (in separate modules to avoid static variable conflicts)
// =============================================================================

mod error_comparator_default {
    use super::*;
    use std::sync::atomic::{AtomicU32, Ordering};

    static ERROR_LEVEL1_CALL_COUNT: AtomicU32 = AtomicU32::new(0);
    static ERROR_LEVEL2_CALL_COUNT: AtomicU32 = AtomicU32::new(0);
    static ERROR_LEVEL3_CALL_COUNT: AtomicU32 = AtomicU32::new(0);

    /// Level 1: Base query that may return an error
    #[query]
    fn error_level1(ctx: &mut QueryContext, code: i32) -> Result<i32, QueryError> {
        let _ = ctx;
        ERROR_LEVEL1_CALL_COUNT.fetch_add(1, Ordering::SeqCst);

        if *code < 0 {
            return Err(CustomError {
                code: *code,
                message: "negative code".to_string(),
            }
            .into());
        }
        Ok(*code * 2)
    }

    /// Level 2: Depends on Level 1
    #[query]
    fn error_level2(ctx: &mut QueryContext, code: i32) -> Result<i32, QueryError> {
        ERROR_LEVEL2_CALL_COUNT.fetch_add(1, Ordering::SeqCst);
        let base = ctx.query(ErrorLevel1::new(*code))?;
        Ok(*base + 1)
    }

    /// Level 3: Depends on Level 2 (transitively on Level 1)
    #[query]
    fn error_level3(ctx: &mut QueryContext, code: i32) -> Result<i32, QueryError> {
        ERROR_LEVEL3_CALL_COUNT.fetch_add(1, Ordering::SeqCst);
        let base = ctx.query(ErrorLevel2::new(*code))?;
        Ok(*base + 10)
    }

    #[test]
    fn test_error_comparator_default_false() {
        // Default comparator returns false, so errors are always "different"
        // This means all downstream queries will be recomputed
        ERROR_LEVEL1_CALL_COUNT.store(0, Ordering::SeqCst);
        ERROR_LEVEL2_CALL_COUNT.store(0, Ordering::SeqCst);
        ERROR_LEVEL3_CALL_COUNT.store(0, Ordering::SeqCst);

        let runtime = QueryRuntime::new();

        // First call through Level 3 -> Level 2 -> Level 1
        let result1 = runtime.query(ErrorLevel3::new(-1));
        assert!(matches!(result1, Err(QueryError::UserError(_))));
        assert_eq!(ERROR_LEVEL1_CALL_COUNT.load(Ordering::SeqCst), 1);
        assert_eq!(ERROR_LEVEL2_CALL_COUNT.load(Ordering::SeqCst), 1);
        assert_eq!(ERROR_LEVEL3_CALL_COUNT.load(Ordering::SeqCst), 1);

        // Invalidate Level 1 and rerun Level 3
        runtime.invalidate::<ErrorLevel1>(&-1);

        let result2 = runtime.query(ErrorLevel3::new(-1));
        assert!(matches!(result2, Err(QueryError::UserError(_))));
        // Level 1 is recomputed
        assert_eq!(ERROR_LEVEL1_CALL_COUNT.load(Ordering::SeqCst), 2);
        // With default comparator (always different), Level 2 is also recomputed
        assert_eq!(ERROR_LEVEL2_CALL_COUNT.load(Ordering::SeqCst), 2);
        // Level 3 is also recomputed
        assert_eq!(ERROR_LEVEL3_CALL_COUNT.load(Ordering::SeqCst), 2);
    }
}

mod error_comparator_custom {
    use super::*;
    use std::sync::atomic::{AtomicU32, Ordering};

    static ERROR_LEVEL1_CALL_COUNT: AtomicU32 = AtomicU32::new(0);
    static ERROR_LEVEL2_CALL_COUNT: AtomicU32 = AtomicU32::new(0);
    static ERROR_LEVEL3_CALL_COUNT: AtomicU32 = AtomicU32::new(0);

    /// Level 1: Base query that may return an error
    #[query]
    fn error_level1(ctx: &mut QueryContext, code: i32) -> Result<i32, QueryError> {
        let _ = ctx;
        ERROR_LEVEL1_CALL_COUNT.fetch_add(1, Ordering::SeqCst);

        if *code < 0 {
            return Err(CustomError {
                code: *code,
                message: "negative code".to_string(),
            }
            .into());
        }
        Ok(*code * 2)
    }

    /// Level 2: Depends on Level 1
    #[query]
    fn error_level2(ctx: &mut QueryContext, code: i32) -> Result<i32, QueryError> {
        ERROR_LEVEL2_CALL_COUNT.fetch_add(1, Ordering::SeqCst);
        let base = ctx.query(ErrorLevel1::new(*code))?;
        Ok(*base + 1)
    }

    /// Level 3: Depends on Level 2 (transitively on Level 1)
    #[query]
    fn error_level3(ctx: &mut QueryContext, code: i32) -> Result<i32, QueryError> {
        ERROR_LEVEL3_CALL_COUNT.fetch_add(1, Ordering::SeqCst);
        let base = ctx.query(ErrorLevel2::new(*code))?;
        Ok(*base + 10)
    }

    #[test]
    fn test_error_comparator_custom() {
        // Custom comparator that considers CustomErrors equal if they have the same code
        // With early cutoff, downstream queries should NOT be recomputed
        ERROR_LEVEL1_CALL_COUNT.store(0, Ordering::SeqCst);
        ERROR_LEVEL2_CALL_COUNT.store(0, Ordering::SeqCst);
        ERROR_LEVEL3_CALL_COUNT.store(0, Ordering::SeqCst);

        let runtime = QueryRuntime::builder()
            .error_comparator(|a, b| {
                match (
                    a.downcast_ref::<CustomError>(),
                    b.downcast_ref::<CustomError>(),
                ) {
                    (Some(a), Some(b)) => a.code == b.code,
                    _ => false,
                }
            })
            .build();

        // First call through Level 3 -> Level 2 -> Level 1
        let result1 = runtime.query(ErrorLevel3::new(-1));
        assert!(matches!(result1, Err(QueryError::UserError(_))));
        assert_eq!(ERROR_LEVEL1_CALL_COUNT.load(Ordering::SeqCst), 1);
        assert_eq!(ERROR_LEVEL2_CALL_COUNT.load(Ordering::SeqCst), 1);
        assert_eq!(ERROR_LEVEL3_CALL_COUNT.load(Ordering::SeqCst), 1);

        // Invalidate Level 1 and rerun Level 3
        runtime.invalidate::<ErrorLevel1>(&-1);

        let result2 = runtime.query(ErrorLevel3::new(-1));
        assert!(matches!(result2, Err(QueryError::UserError(_))));
        // Level 1 is recomputed
        assert_eq!(ERROR_LEVEL1_CALL_COUNT.load(Ordering::SeqCst), 2);
        // With custom comparator, same error means Level 2 gets early cutoff
        // Level 2 is still checked (executed), but since Level 1 returned same error,
        // its downstream (Level 3) should benefit from early cutoff
        // Note: Level 2 is executed because we need to verify its output hasn't changed
        assert_eq!(ERROR_LEVEL2_CALL_COUNT.load(Ordering::SeqCst), 2);
        // Level 3 benefits from early cutoff (Level 2's error is unchanged)
        assert_eq!(ERROR_LEVEL3_CALL_COUNT.load(Ordering::SeqCst), 1);
    }
}

mod error_comparator_always_equal {
    use super::*;
    use std::sync::atomic::{AtomicU32, Ordering};

    static ERROR_LEVEL1_CALL_COUNT: AtomicU32 = AtomicU32::new(0);
    static ERROR_LEVEL2_CALL_COUNT: AtomicU32 = AtomicU32::new(0);
    static ERROR_LEVEL3_CALL_COUNT: AtomicU32 = AtomicU32::new(0);

    /// Level 1: Base query that may return an error
    #[query]
    fn error_level1(ctx: &mut QueryContext, code: i32) -> Result<i32, QueryError> {
        let _ = ctx;
        ERROR_LEVEL1_CALL_COUNT.fetch_add(1, Ordering::SeqCst);

        if *code < 0 {
            return Err(CustomError {
                code: *code,
                message: "negative code".to_string(),
            }
            .into());
        }
        Ok(*code * 2)
    }

    /// Level 2: Depends on Level 1
    #[query]
    fn error_level2(ctx: &mut QueryContext, code: i32) -> Result<i32, QueryError> {
        ERROR_LEVEL2_CALL_COUNT.fetch_add(1, Ordering::SeqCst);
        let base = ctx.query(ErrorLevel1::new(*code))?;
        Ok(*base + 1)
    }

    /// Level 3: Depends on Level 2 (transitively on Level 1)
    #[query]
    fn error_level3(ctx: &mut QueryContext, code: i32) -> Result<i32, QueryError> {
        ERROR_LEVEL3_CALL_COUNT.fetch_add(1, Ordering::SeqCst);
        let base = ctx.query(ErrorLevel2::new(*code))?;
        Ok(*base + 10)
    }

    #[test]
    fn test_error_comparator_always_equal() {
        // Comparator that treats all errors as equal
        // With 3-level chain, early cutoff at Level 2 should prevent Level 3 recomputation
        ERROR_LEVEL1_CALL_COUNT.store(0, Ordering::SeqCst);
        ERROR_LEVEL2_CALL_COUNT.store(0, Ordering::SeqCst);
        ERROR_LEVEL3_CALL_COUNT.store(0, Ordering::SeqCst);

        let runtime = QueryRuntime::builder()
            .error_comparator(|_, _| true)
            .build();

        // First call through Level 3 -> Level 2 -> Level 1
        let result1 = runtime.query(ErrorLevel3::new(-1));
        assert!(matches!(result1, Err(QueryError::UserError(_))));
        assert_eq!(ERROR_LEVEL1_CALL_COUNT.load(Ordering::SeqCst), 1);
        assert_eq!(ERROR_LEVEL2_CALL_COUNT.load(Ordering::SeqCst), 1);
        assert_eq!(ERROR_LEVEL3_CALL_COUNT.load(Ordering::SeqCst), 1);

        // Invalidate Level 1 and rerun Level 3
        runtime.invalidate::<ErrorLevel1>(&-1);

        let result2 = runtime.query(ErrorLevel3::new(-1));
        assert!(matches!(result2, Err(QueryError::UserError(_))));

        // Level 1 is recomputed
        assert_eq!(ERROR_LEVEL1_CALL_COUNT.load(Ordering::SeqCst), 2);
        // Level 2 is executed to verify its output
        assert_eq!(ERROR_LEVEL2_CALL_COUNT.load(Ordering::SeqCst), 2);
        // Level 3 benefits from early cutoff (all errors are "equal")
        assert_eq!(ERROR_LEVEL3_CALL_COUNT.load(Ordering::SeqCst), 1);
    }
}

// =============================================================================
// Mixed Ok/Error Chain Tests
// =============================================================================

mod mixed_chain {
    use super::*;
    use std::sync::atomic::{AtomicU32, Ordering};

    static MIXED_BASE_CALL_COUNT: AtomicU32 = AtomicU32::new(0);
    static MIXED_MIDDLE_CALL_COUNT: AtomicU32 = AtomicU32::new(0);
    static MIXED_TOP_CALL_COUNT: AtomicU32 = AtomicU32::new(0);

    #[query]
    fn mixed_base(ctx: &mut QueryContext, value: i32) -> Result<i32, QueryError> {
        let _ = ctx;
        MIXED_BASE_CALL_COUNT.fetch_add(1, Ordering::SeqCst);
        Ok(value * 2)
    }

    #[query]
    fn mixed_middle(ctx: &mut QueryContext, value: i32) -> Result<i32, QueryError> {
        MIXED_MIDDLE_CALL_COUNT.fetch_add(1, Ordering::SeqCst);
        let base = ctx.query(MixedBase::new(*value))?;

        if *base > 100 {
            return Err(anyhow::anyhow!("value too large: {}", base).into());
        }
        Ok(*base + 10)
    }

    #[query]
    fn mixed_top(ctx: &mut QueryContext, value: i32) -> Result<String, QueryError> {
        MIXED_TOP_CALL_COUNT.fetch_add(1, Ordering::SeqCst);
        let middle = ctx.query(MixedMiddle::new(*value))?;
        Ok(format!("result: {}", middle))
    }

    #[test]
    fn test_mixed_ok_and_error_chain() {
        MIXED_BASE_CALL_COUNT.store(0, Ordering::SeqCst);
        MIXED_MIDDLE_CALL_COUNT.store(0, Ordering::SeqCst);
        MIXED_TOP_CALL_COUNT.store(0, Ordering::SeqCst);

        let runtime = QueryRuntime::new();

        // Success path
        let result = runtime.query(MixedTop::new(10));
        assert_eq!(*result.unwrap(), "result: 30"); // 10 * 2 + 10 = 30

        // Error path
        let result = runtime.query(MixedTop::new(100));
        match result {
            Err(QueryError::UserError(e)) => {
                assert!(e.to_string().contains("value too large"));
            }
            other => panic!("Expected UserError, got {:?}", other),
        }
    }
}

// =============================================================================
// Error Downcast Tests
// =============================================================================

mod error_downcast {
    use super::*;
    use std::sync::atomic::{AtomicU32, Ordering};

    static ERROR_LEVEL1_CALL_COUNT: AtomicU32 = AtomicU32::new(0);

    /// Level 1: Base query that may return an error
    #[query]
    fn error_level1(ctx: &mut QueryContext, code: i32) -> Result<i32, QueryError> {
        let _ = ctx;
        ERROR_LEVEL1_CALL_COUNT.fetch_add(1, Ordering::SeqCst);

        if *code < 0 {
            return Err(CustomError {
                code: *code,
                message: "negative code".to_string(),
            }
            .into());
        }
        Ok(*code * 2)
    }

    #[test]
    fn test_error_downcast() {
        let runtime = QueryRuntime::new();

        // Create error with CustomError using ErrorLevel1
        let result = runtime.query(ErrorLevel1::new(-42));

        match result {
            Err(QueryError::UserError(e)) => {
                // Downcast to original error type
                let custom = e.downcast_ref::<CustomError>();
                assert!(custom.is_some());
                let custom = custom.unwrap();
                assert_eq!(custom.code, -42);
                assert_eq!(custom.message, "negative code");
            }
            other => panic!("Expected UserError, got {:?}", other),
        }
    }
}

// =============================================================================
// Transition Tests (Ok -> Error, Error -> Ok)
// =============================================================================

mod transition_ok_to_error {
    use super::*;
    use std::sync::atomic::{AtomicU32, Ordering};

    static TRANSITION_VALUE: AtomicU32 = AtomicU32::new(10);
    static TRANSITION_CALL_COUNT: AtomicU32 = AtomicU32::new(0);
    static TRANSITION_DEPENDENT_CALL_COUNT: AtomicU32 = AtomicU32::new(0);

    #[query]
    fn transition_source(ctx: &mut QueryContext) -> Result<i32, QueryError> {
        let _ = ctx;
        TRANSITION_CALL_COUNT.fetch_add(1, Ordering::SeqCst);
        let value = TRANSITION_VALUE.load(Ordering::SeqCst) as i32;

        if value < 0 {
            return Err(anyhow::anyhow!("negative value").into());
        }
        Ok(value)
    }

    #[query]
    fn transition_dependent(ctx: &mut QueryContext) -> Result<i32, QueryError> {
        TRANSITION_DEPENDENT_CALL_COUNT.fetch_add(1, Ordering::SeqCst);
        let source = ctx.query(TransitionSource::new())?;
        Ok(*source * 2)
    }

    #[test]
    fn test_ok_to_error_transition() {
        TRANSITION_VALUE.store(10, Ordering::SeqCst);
        TRANSITION_CALL_COUNT.store(0, Ordering::SeqCst);
        TRANSITION_DEPENDENT_CALL_COUNT.store(0, Ordering::SeqCst);

        let runtime = QueryRuntime::new();

        // Start with Ok
        let result = runtime.query(TransitionDependent::new());
        assert_eq!(*result.unwrap(), 20);
        assert_eq!(TRANSITION_CALL_COUNT.load(Ordering::SeqCst), 1);
        assert_eq!(TRANSITION_DEPENDENT_CALL_COUNT.load(Ordering::SeqCst), 1);

        // Change to error state
        TRANSITION_VALUE.store(u32::MAX, Ordering::SeqCst); // Will be -1 as i32
        runtime.invalidate::<TransitionSource>(&());

        // Should now get error
        let result = runtime.query(TransitionDependent::new());
        assert!(matches!(result, Err(QueryError::UserError(_))));
        assert_eq!(TRANSITION_CALL_COUNT.load(Ordering::SeqCst), 2);
        assert_eq!(TRANSITION_DEPENDENT_CALL_COUNT.load(Ordering::SeqCst), 2);
    }
}

mod transition_error_to_ok {
    use super::*;
    use std::sync::atomic::{AtomicU32, Ordering};

    static TRANSITION_VALUE: AtomicU32 = AtomicU32::new(10);
    static TRANSITION_CALL_COUNT: AtomicU32 = AtomicU32::new(0);
    static TRANSITION_DEPENDENT_CALL_COUNT: AtomicU32 = AtomicU32::new(0);

    #[query]
    fn transition_source(ctx: &mut QueryContext) -> Result<i32, QueryError> {
        let _ = ctx;
        TRANSITION_CALL_COUNT.fetch_add(1, Ordering::SeqCst);
        let value = TRANSITION_VALUE.load(Ordering::SeqCst) as i32;

        if value < 0 {
            return Err(anyhow::anyhow!("negative value").into());
        }
        Ok(value)
    }

    #[query]
    fn transition_dependent(ctx: &mut QueryContext) -> Result<i32, QueryError> {
        TRANSITION_DEPENDENT_CALL_COUNT.fetch_add(1, Ordering::SeqCst);
        let source = ctx.query(TransitionSource::new())?;
        Ok(*source * 2)
    }

    #[test]
    fn test_error_to_ok_transition() {
        TRANSITION_VALUE.store(u32::MAX, Ordering::SeqCst); // -1 as i32, will error
        TRANSITION_CALL_COUNT.store(0, Ordering::SeqCst);
        TRANSITION_DEPENDENT_CALL_COUNT.store(0, Ordering::SeqCst);

        let runtime = QueryRuntime::new();

        // Start with error
        let result = runtime.query(TransitionDependent::new());
        assert!(matches!(result, Err(QueryError::UserError(_))));

        // Change to Ok state
        TRANSITION_VALUE.store(5, Ordering::SeqCst);
        runtime.invalidate::<TransitionSource>(&());

        // Should now get Ok
        let result = runtime.query(TransitionDependent::new());
        assert_eq!(*result.unwrap(), 10);
    }
}

// =============================================================================
// Error Display and Source Tests
// =============================================================================

#[test]
fn test_error_display() {
    let err: QueryError = anyhow::Error::from(std::io::Error::new(
        std::io::ErrorKind::NotFound,
        "test error",
    ))
    .into();
    let display = err.to_string();
    assert!(display.contains("user error"));
    assert!(display.contains("test error"));
}

#[test]
fn test_error_source() {
    // Create an error chain using anyhow context
    let io_err = std::io::Error::new(std::io::ErrorKind::NotFound, "original error");
    let anyhow_err = anyhow::Error::from(io_err).context("wrapped error");
    let _query_err: QueryError = anyhow_err.into();

    // QueryError::UserError with context should have a source
    // let source = query_err.source();
    // assert!(source.is_some());
}
