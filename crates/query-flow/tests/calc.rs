//! Calc example: A simple expression evaluator demonstrating query-flow.
//!
//! This example is inspired by salsa-rs's calc example, showing:
//! - Input queries (source text)
//! - Derived queries (parsing, evaluation)
//! - Incremental recomputation
//! - Early cutoff optimization

use query_flow::{query, Query, QueryContext, QueryError, QueryRuntime};
use std::collections::HashMap;
use std::sync::{Arc, RwLock};

// ============================================================================
// Expression AST
// ============================================================================

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Number(i64),
    Variable(String),
    BinOp {
        op: BinOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
}

// ============================================================================
// Input Storage (simulates external inputs like file contents)
// ============================================================================

/// Storage for input values that can change between queries.
/// In a real application, this might be file contents, user input, etc.
#[derive(Default)]
pub struct InputStorage {
    /// Source text for each "file" (identified by name)
    sources: RwLock<HashMap<String, String>>,
    /// Variable bindings
    variables: RwLock<HashMap<String, i64>>,
}

impl InputStorage {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn set_source(&self, name: &str, source: &str) {
        self.sources
            .write()
            .unwrap()
            .insert(name.to_string(), source.to_string());
    }

    pub fn get_source(&self, name: &str) -> Option<String> {
        self.sources.read().unwrap().get(name).cloned()
    }

    pub fn set_variable(&self, name: &str, value: i64) {
        self.variables
            .write()
            .unwrap()
            .insert(name.to_string(), value);
    }

    pub fn get_variable(&self, name: &str) -> Option<i64> {
        self.variables.read().unwrap().get(name).copied()
    }
}

// We'll use a thread-local to access inputs from queries
thread_local! {
    static INPUTS: std::cell::RefCell<Option<Arc<InputStorage>>> = const { std::cell::RefCell::new(None) };
}

fn with_inputs<R>(f: impl FnOnce(&InputStorage) -> R) -> R {
    INPUTS.with(|inputs| {
        let inputs = inputs.borrow();
        let inputs = inputs.as_ref().expect("InputStorage not set");
        f(inputs)
    })
}

fn set_inputs(storage: Arc<InputStorage>) {
    INPUTS.with(|inputs| {
        *inputs.borrow_mut() = Some(storage);
    });
}

// ============================================================================
// Queries
// ============================================================================

/// Query to get source text for a file.
/// This is an "input" query - its value comes from external storage.
#[query(durability = 1)]
fn source_text(ctx: &mut QueryContext, file_name: String) -> Result<String, QueryError> {
    let _ = ctx;
    Ok(with_inputs(|inputs| {
        inputs
            .get_source(&file_name)
            .unwrap_or_else(|| String::new())
    }))
}

/// Query to get a variable's value.
#[query(durability = 1)]
fn variable_value(ctx: &mut QueryContext, var_name: String) -> Result<i64, QueryError> {
    let _ = ctx;
    Ok(with_inputs(|inputs| inputs.get_variable(&var_name).unwrap_or(0)))
}

/// Parse source text into an expression.
#[query]
fn parse_expr(ctx: &mut QueryContext, file_name: String) -> Result<Expr, QueryError> {
    let source = ctx.query(SourceText::new(file_name.clone()))?;
    Ok(parse(&source))
}

/// Evaluate an expression from a file.
#[query]
fn eval_file(ctx: &mut QueryContext, file_name: String) -> Result<i64, QueryError> {
    let expr = ctx.query(ParseExpr::new(file_name.clone()))?;
    eval_expr(ctx, &expr)
}

// ============================================================================
// Parser (simple recursive descent)
// ============================================================================

fn parse(input: &str) -> Expr {
    let input = input.trim();
    parse_additive(input).0
}

fn parse_additive(input: &str) -> (Expr, &str) {
    let (mut lhs, mut rest) = parse_multiplicative(input);

    loop {
        let rest_trimmed = rest.trim_start();
        if let Some(remaining) = rest_trimmed.strip_prefix('+') {
            let (rhs, new_rest) = parse_multiplicative(remaining);
            lhs = Expr::BinOp {
                op: BinOp::Add,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            };
            rest = new_rest;
        } else if let Some(remaining) = rest_trimmed.strip_prefix('-') {
            let (rhs, new_rest) = parse_multiplicative(remaining);
            lhs = Expr::BinOp {
                op: BinOp::Sub,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            };
            rest = new_rest;
        } else {
            break;
        }
    }

    (lhs, rest)
}

fn parse_multiplicative(input: &str) -> (Expr, &str) {
    let (mut lhs, mut rest) = parse_primary(input);

    loop {
        let rest_trimmed = rest.trim_start();
        if let Some(remaining) = rest_trimmed.strip_prefix('*') {
            let (rhs, new_rest) = parse_primary(remaining);
            lhs = Expr::BinOp {
                op: BinOp::Mul,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            };
            rest = new_rest;
        } else if let Some(remaining) = rest_trimmed.strip_prefix('/') {
            let (rhs, new_rest) = parse_primary(remaining);
            lhs = Expr::BinOp {
                op: BinOp::Div,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            };
            rest = new_rest;
        } else {
            break;
        }
    }

    (lhs, rest)
}

fn parse_primary(input: &str) -> (Expr, &str) {
    let input = input.trim_start();

    if let Some(rest) = input.strip_prefix('(') {
        let (expr, rest) = parse_additive(rest);
        let rest = rest.trim_start().strip_prefix(')').unwrap_or(rest);
        return (expr, rest);
    }

    // Try to parse a number
    let num_end = input
        .find(|c: char| !c.is_ascii_digit() && c != '-')
        .unwrap_or(input.len());

    if num_end > 0 {
        if let Ok(n) = input[..num_end].parse::<i64>() {
            return (Expr::Number(n), &input[num_end..]);
        }
    }

    // Try to parse a variable name
    let var_end = input
        .find(|c: char| !c.is_alphanumeric() && c != '_')
        .unwrap_or(input.len());

    if var_end > 0 {
        let var_name = &input[..var_end];
        return (Expr::Variable(var_name.to_string()), &input[var_end..]);
    }

    // Fallback
    (Expr::Number(0), input)
}

// ============================================================================
// Evaluator
// ============================================================================

fn eval_expr(ctx: &mut QueryContext, expr: &Expr) -> Result<i64, QueryError> {
    match expr {
        Expr::Number(n) => Ok(*n),
        Expr::Variable(name) => {
            let value = ctx.query(VariableValue::new(name.clone()))?;
            Ok(*value)
        }
        Expr::BinOp { op, lhs, rhs } => {
            let lhs_val = eval_expr(ctx, lhs)?;
            let rhs_val = eval_expr(ctx, rhs)?;
            Ok(match op {
                BinOp::Add => lhs_val + rhs_val,
                BinOp::Sub => lhs_val - rhs_val,
                BinOp::Mul => lhs_val * rhs_val,
                BinOp::Div => {
                    if rhs_val == 0 {
                        0
                    } else {
                        lhs_val / rhs_val
                    }
                }
            })
        }
    }
}

// ============================================================================
// Tests
// ============================================================================

#[test]
fn test_simple_expression() {
    let inputs = Arc::new(InputStorage::new());
    inputs.set_source("main", "1 + 2 * 3");

    set_inputs(inputs);

    let runtime = QueryRuntime::new();
    let result = runtime
        .query(EvalFile::new("main".to_string()))
        .unwrap();

    // 1 + (2 * 3) = 7
    assert_eq!(*result, 7);
}

#[test]
fn test_with_variables() {
    let inputs = Arc::new(InputStorage::new());
    inputs.set_source("main", "x + y * 2");
    inputs.set_variable("x", 10);
    inputs.set_variable("y", 5);

    set_inputs(inputs);

    let runtime = QueryRuntime::new();
    let result = runtime
        .query(EvalFile::new("main".to_string()))
        .unwrap();

    // 10 + (5 * 2) = 20
    assert_eq!(*result, 20);
}

#[test]
fn test_parentheses() {
    let inputs = Arc::new(InputStorage::new());
    inputs.set_source("main", "(1 + 2) * 3");

    set_inputs(inputs);

    let runtime = QueryRuntime::new();
    let result = runtime
        .query(EvalFile::new("main".to_string()))
        .unwrap();

    // (1 + 2) * 3 = 9
    assert_eq!(*result, 9);
}

#[test]
fn test_caching() {
    use std::sync::atomic::{AtomicU32, Ordering};

    static PARSE_COUNT: AtomicU32 = AtomicU32::new(0);

    // Custom parse query that tracks call count
    struct TrackedParse {
        file_name: String,
    }

    impl Query for TrackedParse {
        type CacheKey = String;
        type Output = Expr;

        fn cache_key(&self) -> Self::CacheKey {
            self.file_name.clone()
        }

        fn query(&self, ctx: &mut QueryContext) -> Result<Self::Output, QueryError> {
            PARSE_COUNT.fetch_add(1, Ordering::SeqCst);
            let source = ctx.query(SourceText::new(self.file_name.clone()))?;
            Ok(parse(&source))
        }

        fn output_eq(old: &Self::Output, new: &Self::Output) -> bool {
            old == new
        }
    }

    let inputs = Arc::new(InputStorage::new());
    inputs.set_source("main", "1 + 2");

    set_inputs(inputs);

    let runtime = QueryRuntime::new();

    // First query - should parse
    let _ = runtime
        .query(TrackedParse {
            file_name: "main".to_string(),
        })
        .unwrap();
    assert_eq!(PARSE_COUNT.load(Ordering::SeqCst), 1);

    // Second query - should be cached
    let _ = runtime
        .query(TrackedParse {
            file_name: "main".to_string(),
        })
        .unwrap();
    assert_eq!(PARSE_COUNT.load(Ordering::SeqCst), 1); // Still 1!
}

#[test]
fn test_complex_expression() {
    let inputs = Arc::new(InputStorage::new());
    inputs.set_source("main", "((2 + 3) * 4 - 5) / 3");

    set_inputs(inputs);

    let runtime = QueryRuntime::new();
    let result = runtime
        .query(EvalFile::new("main".to_string()))
        .unwrap();

    // ((2 + 3) * 4 - 5) / 3 = (5 * 4 - 5) / 3 = (20 - 5) / 3 = 15 / 3 = 5
    assert_eq!(*result, 5);
}

#[test]
fn test_multiple_files() {
    let inputs = Arc::new(InputStorage::new());
    inputs.set_source("a", "10");
    inputs.set_source("b", "20 + 5");
    inputs.set_source("c", "3 * 3");

    set_inputs(inputs);

    let runtime = QueryRuntime::new();

    let a = runtime.query(EvalFile::new("a".to_string())).unwrap();
    let b = runtime.query(EvalFile::new("b".to_string())).unwrap();
    let c = runtime.query(EvalFile::new("c".to_string())).unwrap();

    assert_eq!(*a, 10);
    assert_eq!(*b, 25);
    assert_eq!(*c, 9);
}

#[test]
fn test_dependency_chain() {
    // This test demonstrates a chain of queries:
    // source_text -> parse_expr -> eval_file

    let inputs = Arc::new(InputStorage::new());
    inputs.set_source("expr", "a * b + c");
    inputs.set_variable("a", 2);
    inputs.set_variable("b", 3);
    inputs.set_variable("c", 4);

    set_inputs(inputs);

    let runtime = QueryRuntime::new();
    let result = runtime
        .query(EvalFile::new("expr".to_string()))
        .unwrap();

    // 2 * 3 + 4 = 10
    assert_eq!(*result, 10);
}

#[test]
fn test_subtraction_and_division() {
    let inputs = Arc::new(InputStorage::new());
    inputs.set_source("main", "100 - 50 / 2");

    set_inputs(inputs);

    let runtime = QueryRuntime::new();
    let result = runtime
        .query(EvalFile::new("main".to_string()))
        .unwrap();

    // 100 - (50 / 2) = 100 - 25 = 75
    assert_eq!(*result, 75);
}

#[test]
fn test_variable_only() {
    let inputs = Arc::new(InputStorage::new());
    inputs.set_source("main", "answer");
    inputs.set_variable("answer", 42);

    set_inputs(inputs);

    let runtime = QueryRuntime::new();
    let result = runtime
        .query(EvalFile::new("main".to_string()))
        .unwrap();

    assert_eq!(*result, 42);
}

#[test]
fn test_empty_source() {
    let inputs = Arc::new(InputStorage::new());
    // Don't set any source - should get empty string -> 0

    set_inputs(inputs);

    let runtime = QueryRuntime::new();
    let result = runtime
        .query(EvalFile::new("nonexistent".to_string()))
        .unwrap();

    assert_eq!(*result, 0);
}
