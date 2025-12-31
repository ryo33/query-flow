//! Calc example: A simple expression evaluator demonstrating query-flow.
//!
//! This example is inspired by salsa-rs's calc example, showing:
//! - Asset-based inputs (source text, variables)
//! - Derived queries (parsing, evaluation)
//! - Incremental recomputation
//! - Early cutoff optimization

use query_flow::{asset_key, query, Query, QueryContext, QueryError, QueryRuntime};

#[cfg(feature = "inspector")]
use std::sync::Arc;

#[cfg(feature = "inspector")]
use query_flow_inspector::{
    to_kinds, AssetKey, AssetState, EventCollector, EventKind, ExecutionResult, QueryKey,
};

#[cfg(feature = "inspector")]
fn q(query_type: &str, cache_key_debug: &str) -> QueryKey {
    QueryKey::new(query_type, cache_key_debug)
}

#[cfg(feature = "inspector")]
fn a(asset_type: &str, key_debug: &str) -> AssetKey {
    AssetKey::new(asset_type, key_debug)
}

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
// Asset Keys (external inputs)
// ============================================================================

/// Asset key for source file content.
#[asset_key(asset = String, durability = stable)]
pub struct SourceFile(pub String);

/// Asset key for variable bindings.
#[asset_key(asset = i64, durability = stable)]
pub struct Variable(pub String);

// ============================================================================
// Queries
// ============================================================================

/// Parse source text into an expression.
#[query]
fn parse_expr(ctx: &mut QueryContext, file_name: String) -> Result<Expr, QueryError> {
    // Get source from asset, default to empty string if not found
    let source = ctx
        .asset(SourceFile(file_name.clone()))?
        .into_inner()
        .map(|s| (*s).clone())
        .unwrap_or_default();
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
            // Get variable from asset, default to 0 if not found
            let value = ctx
                .asset(Variable(name.clone()))?
                .into_inner()
                .map(|v| *v)
                .unwrap_or(0);
            Ok(value)
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
    #[cfg(feature = "inspector")]
    let collector = Arc::new(EventCollector::new());

    let runtime = QueryRuntime::new();

    #[cfg(feature = "inspector")]
    runtime.set_sink(Some(collector.clone()));

    runtime.resolve_asset(SourceFile("main".to_string()), "1 + 2 * 3".to_string());

    let result = runtime.query(EvalFile::new("main".to_string())).unwrap();

    // 1 + (2 * 3) = 7
    assert_eq!(*result, 7);

    #[cfg(feature = "inspector")]
    {
        use EventKind::*;
        use ExecutionResult::*;

        assert_eq!(
            to_kinds(&collector.trace()),
            vec![
                AssetResolved {
                    asset: a("calc::SourceFile", "SourceFile(\"main\")"),
                    changed: true
                },
                QueryStart {
                    query: q("calc::EvalFile", "calc::EvalFile(\"main\")")
                },
                CacheCheck {
                    query: q("calc::EvalFile", "calc::EvalFile(\"main\")"),
                    valid: false
                },
                DependencyRegistered {
                    parent: q("calc::EvalFile", "calc::EvalFile(\"main\")"),
                    dependency: q("calc::ParseExpr", "calc::ParseExpr(\"main\")"),
                },
                QueryStart {
                    query: q("calc::ParseExpr", "calc::ParseExpr(\"main\")")
                },
                CacheCheck {
                    query: q("calc::ParseExpr", "calc::ParseExpr(\"main\")"),
                    valid: false
                },
                AssetDependencyRegistered {
                    parent: q("calc::ParseExpr", "calc::ParseExpr(\"main\")"),
                    asset: a("calc::SourceFile", "SourceFile(\"main\")"),
                },
                AssetRequested {
                    asset: a("calc::SourceFile", "SourceFile(\"main\")"),
                    state: AssetState::Ready
                },
                EarlyCutoffCheck {
                    query: q("calc::ParseExpr", "calc::ParseExpr(\"main\")"),
                    output_changed: true
                },
                QueryEnd {
                    query: q("calc::ParseExpr", "calc::ParseExpr(\"main\")"),
                    result: Changed
                },
                EarlyCutoffCheck {
                    query: q("calc::EvalFile", "calc::EvalFile(\"main\")"),
                    output_changed: true
                },
                QueryEnd {
                    query: q("calc::EvalFile", "calc::EvalFile(\"main\")"),
                    result: Changed
                },
            ]
        );
    }
}

#[test]
fn test_with_variables() {
    #[cfg(feature = "inspector")]
    let collector = Arc::new(EventCollector::new());

    let runtime = QueryRuntime::new();

    #[cfg(feature = "inspector")]
    runtime.set_sink(Some(collector.clone()));

    runtime.resolve_asset(SourceFile("main".to_string()), "x + y * 2".to_string());
    runtime.resolve_asset(Variable("x".to_string()), 10);
    runtime.resolve_asset(Variable("y".to_string()), 5);

    let result = runtime.query(EvalFile::new("main".to_string())).unwrap();

    // 10 + (5 * 2) = 20
    assert_eq!(*result, 20);

    #[cfg(feature = "inspector")]
    {
        use EventKind::*;
        use ExecutionResult::*;

        assert_eq!(
            to_kinds(&collector.trace()),
            vec![
                AssetResolved {
                    asset: a("calc::SourceFile", "SourceFile(\"main\")"),
                    changed: true
                },
                AssetResolved {
                    asset: a("calc::Variable", "Variable(\"x\")"),
                    changed: true
                },
                AssetResolved {
                    asset: a("calc::Variable", "Variable(\"y\")"),
                    changed: true
                },
                QueryStart {
                    query: q("calc::EvalFile", "calc::EvalFile(\"main\")")
                },
                CacheCheck {
                    query: q("calc::EvalFile", "calc::EvalFile(\"main\")"),
                    valid: false
                },
                DependencyRegistered {
                    parent: q("calc::EvalFile", "calc::EvalFile(\"main\")"),
                    dependency: q("calc::ParseExpr", "calc::ParseExpr(\"main\")"),
                },
                QueryStart {
                    query: q("calc::ParseExpr", "calc::ParseExpr(\"main\")")
                },
                CacheCheck {
                    query: q("calc::ParseExpr", "calc::ParseExpr(\"main\")"),
                    valid: false
                },
                AssetDependencyRegistered {
                    parent: q("calc::ParseExpr", "calc::ParseExpr(\"main\")"),
                    asset: a("calc::SourceFile", "SourceFile(\"main\")"),
                },
                AssetRequested {
                    asset: a("calc::SourceFile", "SourceFile(\"main\")"),
                    state: AssetState::Ready
                },
                EarlyCutoffCheck {
                    query: q("calc::ParseExpr", "calc::ParseExpr(\"main\")"),
                    output_changed: true
                },
                QueryEnd {
                    query: q("calc::ParseExpr", "calc::ParseExpr(\"main\")"),
                    result: Changed
                },
                // x variable lookup
                AssetDependencyRegistered {
                    parent: q("calc::EvalFile", "calc::EvalFile(\"main\")"),
                    asset: a("calc::Variable", "Variable(\"x\")"),
                },
                AssetRequested {
                    asset: a("calc::Variable", "Variable(\"x\")"),
                    state: AssetState::Ready
                },
                // y variable lookup
                AssetDependencyRegistered {
                    parent: q("calc::EvalFile", "calc::EvalFile(\"main\")"),
                    asset: a("calc::Variable", "Variable(\"y\")"),
                },
                AssetRequested {
                    asset: a("calc::Variable", "Variable(\"y\")"),
                    state: AssetState::Ready
                },
                EarlyCutoffCheck {
                    query: q("calc::EvalFile", "calc::EvalFile(\"main\")"),
                    output_changed: true
                },
                QueryEnd {
                    query: q("calc::EvalFile", "calc::EvalFile(\"main\")"),
                    result: Changed
                },
            ]
        );
    }
}

#[test]
fn test_parentheses() {
    #[cfg(feature = "inspector")]
    let collector = Arc::new(EventCollector::new());

    let runtime = QueryRuntime::new();

    #[cfg(feature = "inspector")]
    runtime.set_sink(Some(collector.clone()));

    runtime.resolve_asset(SourceFile("main".to_string()), "(1 + 2) * 3".to_string());

    let result = runtime.query(EvalFile::new("main".to_string())).unwrap();

    // (1 + 2) * 3 = 9
    assert_eq!(*result, 9);

    #[cfg(feature = "inspector")]
    {
        use EventKind::*;
        use ExecutionResult::*;

        assert_eq!(
            to_kinds(&collector.trace()),
            vec![
                AssetResolved {
                    asset: a("calc::SourceFile", "SourceFile(\"main\")"),
                    changed: true
                },
                QueryStart {
                    query: q("calc::EvalFile", "calc::EvalFile(\"main\")")
                },
                CacheCheck {
                    query: q("calc::EvalFile", "calc::EvalFile(\"main\")"),
                    valid: false
                },
                DependencyRegistered {
                    parent: q("calc::EvalFile", "calc::EvalFile(\"main\")"),
                    dependency: q("calc::ParseExpr", "calc::ParseExpr(\"main\")"),
                },
                QueryStart {
                    query: q("calc::ParseExpr", "calc::ParseExpr(\"main\")")
                },
                CacheCheck {
                    query: q("calc::ParseExpr", "calc::ParseExpr(\"main\")"),
                    valid: false
                },
                AssetDependencyRegistered {
                    parent: q("calc::ParseExpr", "calc::ParseExpr(\"main\")"),
                    asset: a("calc::SourceFile", "SourceFile(\"main\")"),
                },
                AssetRequested {
                    asset: a("calc::SourceFile", "SourceFile(\"main\")"),
                    state: AssetState::Ready
                },
                EarlyCutoffCheck {
                    query: q("calc::ParseExpr", "calc::ParseExpr(\"main\")"),
                    output_changed: true
                },
                QueryEnd {
                    query: q("calc::ParseExpr", "calc::ParseExpr(\"main\")"),
                    result: Changed
                },
                EarlyCutoffCheck {
                    query: q("calc::EvalFile", "calc::EvalFile(\"main\")"),
                    output_changed: true
                },
                QueryEnd {
                    query: q("calc::EvalFile", "calc::EvalFile(\"main\")"),
                    result: Changed
                },
            ]
        );
    }
}

#[test]
fn test_caching() {
    use std::sync::atomic::{AtomicU32, Ordering};

    static PARSE_COUNT: AtomicU32 = AtomicU32::new(0);

    // Custom parse query that tracks call count
    #[derive(Clone)]
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
            let source = ctx
                .asset(SourceFile(self.file_name.clone()))?
                .into_inner()
                .map(|s| (*s).clone())
                .unwrap_or_default();
            Ok(parse(&source))
        }

        fn output_eq(old: &Self::Output, new: &Self::Output) -> bool {
            old == new
        }
    }

    let runtime = QueryRuntime::new();
    runtime.resolve_asset(SourceFile("main".to_string()), "1 + 2".to_string());

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
    #[cfg(feature = "inspector")]
    let collector = Arc::new(EventCollector::new());

    let runtime = QueryRuntime::new();

    #[cfg(feature = "inspector")]
    runtime.set_sink(Some(collector.clone()));

    runtime.resolve_asset(
        SourceFile("main".to_string()),
        "((2 + 3) * 4 - 5) / 3".to_string(),
    );

    let result = runtime.query(EvalFile::new("main".to_string())).unwrap();

    // ((2 + 3) * 4 - 5) / 3 = (5 * 4 - 5) / 3 = (20 - 5) / 3 = 15 / 3 = 5
    assert_eq!(*result, 5);

    #[cfg(feature = "inspector")]
    {
        use EventKind::*;
        use ExecutionResult::*;

        assert_eq!(
            to_kinds(&collector.trace()),
            vec![
                AssetResolved {
                    asset: a("calc::SourceFile", "SourceFile(\"main\")"),
                    changed: true
                },
                QueryStart {
                    query: q("calc::EvalFile", "calc::EvalFile(\"main\")")
                },
                CacheCheck {
                    query: q("calc::EvalFile", "calc::EvalFile(\"main\")"),
                    valid: false
                },
                DependencyRegistered {
                    parent: q("calc::EvalFile", "calc::EvalFile(\"main\")"),
                    dependency: q("calc::ParseExpr", "calc::ParseExpr(\"main\")"),
                },
                QueryStart {
                    query: q("calc::ParseExpr", "calc::ParseExpr(\"main\")")
                },
                CacheCheck {
                    query: q("calc::ParseExpr", "calc::ParseExpr(\"main\")"),
                    valid: false
                },
                AssetDependencyRegistered {
                    parent: q("calc::ParseExpr", "calc::ParseExpr(\"main\")"),
                    asset: a("calc::SourceFile", "SourceFile(\"main\")"),
                },
                AssetRequested {
                    asset: a("calc::SourceFile", "SourceFile(\"main\")"),
                    state: AssetState::Ready
                },
                EarlyCutoffCheck {
                    query: q("calc::ParseExpr", "calc::ParseExpr(\"main\")"),
                    output_changed: true
                },
                QueryEnd {
                    query: q("calc::ParseExpr", "calc::ParseExpr(\"main\")"),
                    result: Changed
                },
                EarlyCutoffCheck {
                    query: q("calc::EvalFile", "calc::EvalFile(\"main\")"),
                    output_changed: true
                },
                QueryEnd {
                    query: q("calc::EvalFile", "calc::EvalFile(\"main\")"),
                    result: Changed
                },
            ]
        );
    }
}

#[test]
fn test_multiple_files() {
    #[cfg(feature = "inspector")]
    let collector = Arc::new(EventCollector::new());

    let runtime = QueryRuntime::new();

    #[cfg(feature = "inspector")]
    runtime.set_sink(Some(collector.clone()));

    runtime.resolve_asset(SourceFile("a".to_string()), "10".to_string());
    runtime.resolve_asset(SourceFile("b".to_string()), "20 + 5".to_string());
    runtime.resolve_asset(SourceFile("c".to_string()), "3 * 3".to_string());

    let result_a = runtime.query(EvalFile::new("a".to_string())).unwrap();
    let result_b = runtime.query(EvalFile::new("b".to_string())).unwrap();
    let result_c = runtime.query(EvalFile::new("c".to_string())).unwrap();

    assert_eq!(*result_a, 10);
    assert_eq!(*result_b, 25);
    assert_eq!(*result_c, 9);

    #[cfg(feature = "inspector")]
    {
        use EventKind::*;
        use ExecutionResult::*;

        assert_eq!(
            to_kinds(&collector.trace()),
            vec![
                // Asset resolutions
                AssetResolved {
                    asset: a("calc::SourceFile", "SourceFile(\"a\")"),
                    changed: true
                },
                AssetResolved {
                    asset: a("calc::SourceFile", "SourceFile(\"b\")"),
                    changed: true
                },
                AssetResolved {
                    asset: a("calc::SourceFile", "SourceFile(\"c\")"),
                    changed: true
                },
                // File "a"
                QueryStart {
                    query: q("calc::EvalFile", "calc::EvalFile(\"a\")")
                },
                CacheCheck {
                    query: q("calc::EvalFile", "calc::EvalFile(\"a\")"),
                    valid: false
                },
                DependencyRegistered {
                    parent: q("calc::EvalFile", "calc::EvalFile(\"a\")"),
                    dependency: q("calc::ParseExpr", "calc::ParseExpr(\"a\")"),
                },
                QueryStart {
                    query: q("calc::ParseExpr", "calc::ParseExpr(\"a\")")
                },
                CacheCheck {
                    query: q("calc::ParseExpr", "calc::ParseExpr(\"a\")"),
                    valid: false
                },
                AssetDependencyRegistered {
                    parent: q("calc::ParseExpr", "calc::ParseExpr(\"a\")"),
                    asset: a("calc::SourceFile", "SourceFile(\"a\")"),
                },
                AssetRequested {
                    asset: a("calc::SourceFile", "SourceFile(\"a\")"),
                    state: AssetState::Ready
                },
                EarlyCutoffCheck {
                    query: q("calc::ParseExpr", "calc::ParseExpr(\"a\")"),
                    output_changed: true
                },
                QueryEnd {
                    query: q("calc::ParseExpr", "calc::ParseExpr(\"a\")"),
                    result: Changed
                },
                EarlyCutoffCheck {
                    query: q("calc::EvalFile", "calc::EvalFile(\"a\")"),
                    output_changed: true
                },
                QueryEnd {
                    query: q("calc::EvalFile", "calc::EvalFile(\"a\")"),
                    result: Changed
                },
                // File "b"
                QueryStart {
                    query: q("calc::EvalFile", "calc::EvalFile(\"b\")")
                },
                CacheCheck {
                    query: q("calc::EvalFile", "calc::EvalFile(\"b\")"),
                    valid: false
                },
                DependencyRegistered {
                    parent: q("calc::EvalFile", "calc::EvalFile(\"b\")"),
                    dependency: q("calc::ParseExpr", "calc::ParseExpr(\"b\")"),
                },
                QueryStart {
                    query: q("calc::ParseExpr", "calc::ParseExpr(\"b\")")
                },
                CacheCheck {
                    query: q("calc::ParseExpr", "calc::ParseExpr(\"b\")"),
                    valid: false
                },
                AssetDependencyRegistered {
                    parent: q("calc::ParseExpr", "calc::ParseExpr(\"b\")"),
                    asset: a("calc::SourceFile", "SourceFile(\"b\")"),
                },
                AssetRequested {
                    asset: a("calc::SourceFile", "SourceFile(\"b\")"),
                    state: AssetState::Ready
                },
                EarlyCutoffCheck {
                    query: q("calc::ParseExpr", "calc::ParseExpr(\"b\")"),
                    output_changed: true
                },
                QueryEnd {
                    query: q("calc::ParseExpr", "calc::ParseExpr(\"b\")"),
                    result: Changed
                },
                EarlyCutoffCheck {
                    query: q("calc::EvalFile", "calc::EvalFile(\"b\")"),
                    output_changed: true
                },
                QueryEnd {
                    query: q("calc::EvalFile", "calc::EvalFile(\"b\")"),
                    result: Changed
                },
                // File "c"
                QueryStart {
                    query: q("calc::EvalFile", "calc::EvalFile(\"c\")")
                },
                CacheCheck {
                    query: q("calc::EvalFile", "calc::EvalFile(\"c\")"),
                    valid: false
                },
                DependencyRegistered {
                    parent: q("calc::EvalFile", "calc::EvalFile(\"c\")"),
                    dependency: q("calc::ParseExpr", "calc::ParseExpr(\"c\")"),
                },
                QueryStart {
                    query: q("calc::ParseExpr", "calc::ParseExpr(\"c\")")
                },
                CacheCheck {
                    query: q("calc::ParseExpr", "calc::ParseExpr(\"c\")"),
                    valid: false
                },
                AssetDependencyRegistered {
                    parent: q("calc::ParseExpr", "calc::ParseExpr(\"c\")"),
                    asset: a("calc::SourceFile", "SourceFile(\"c\")"),
                },
                AssetRequested {
                    asset: a("calc::SourceFile", "SourceFile(\"c\")"),
                    state: AssetState::Ready
                },
                EarlyCutoffCheck {
                    query: q("calc::ParseExpr", "calc::ParseExpr(\"c\")"),
                    output_changed: true
                },
                QueryEnd {
                    query: q("calc::ParseExpr", "calc::ParseExpr(\"c\")"),
                    result: Changed
                },
                EarlyCutoffCheck {
                    query: q("calc::EvalFile", "calc::EvalFile(\"c\")"),
                    output_changed: true
                },
                QueryEnd {
                    query: q("calc::EvalFile", "calc::EvalFile(\"c\")"),
                    result: Changed
                },
            ]
        );
    }
}

#[test]
fn test_dependency_chain() {
    // This test demonstrates a chain of dependencies:
    // SourceFile asset -> parse_expr query -> eval_file query
    // Variable assets -> eval_file query

    #[cfg(feature = "inspector")]
    let collector = Arc::new(EventCollector::new());

    let runtime = QueryRuntime::new();

    #[cfg(feature = "inspector")]
    runtime.set_sink(Some(collector.clone()));

    runtime.resolve_asset(SourceFile("expr".to_string()), "a * b + c".to_string());
    runtime.resolve_asset(Variable("a".to_string()), 2);
    runtime.resolve_asset(Variable("b".to_string()), 3);
    runtime.resolve_asset(Variable("c".to_string()), 4);

    let result = runtime.query(EvalFile::new("expr".to_string())).unwrap();

    // 2 * 3 + 4 = 10
    assert_eq!(*result, 10);

    #[cfg(feature = "inspector")]
    {
        use EventKind::*;
        use ExecutionResult::*;

        assert_eq!(
            to_kinds(&collector.trace()),
            vec![
                // Asset resolutions
                AssetResolved {
                    asset: a("calc::SourceFile", "SourceFile(\"expr\")"),
                    changed: true
                },
                AssetResolved {
                    asset: a("calc::Variable", "Variable(\"a\")"),
                    changed: true
                },
                AssetResolved {
                    asset: a("calc::Variable", "Variable(\"b\")"),
                    changed: true
                },
                AssetResolved {
                    asset: a("calc::Variable", "Variable(\"c\")"),
                    changed: true
                },
                // EvalFile query
                QueryStart {
                    query: q("calc::EvalFile", "calc::EvalFile(\"expr\")")
                },
                CacheCheck {
                    query: q("calc::EvalFile", "calc::EvalFile(\"expr\")"),
                    valid: false
                },
                DependencyRegistered {
                    parent: q("calc::EvalFile", "calc::EvalFile(\"expr\")"),
                    dependency: q("calc::ParseExpr", "calc::ParseExpr(\"expr\")"),
                },
                QueryStart {
                    query: q("calc::ParseExpr", "calc::ParseExpr(\"expr\")")
                },
                CacheCheck {
                    query: q("calc::ParseExpr", "calc::ParseExpr(\"expr\")"),
                    valid: false
                },
                AssetDependencyRegistered {
                    parent: q("calc::ParseExpr", "calc::ParseExpr(\"expr\")"),
                    asset: a("calc::SourceFile", "SourceFile(\"expr\")"),
                },
                AssetRequested {
                    asset: a("calc::SourceFile", "SourceFile(\"expr\")"),
                    state: AssetState::Ready
                },
                EarlyCutoffCheck {
                    query: q("calc::ParseExpr", "calc::ParseExpr(\"expr\")"),
                    output_changed: true
                },
                QueryEnd {
                    query: q("calc::ParseExpr", "calc::ParseExpr(\"expr\")"),
                    result: Changed
                },
                // Variable lookups
                AssetDependencyRegistered {
                    parent: q("calc::EvalFile", "calc::EvalFile(\"expr\")"),
                    asset: a("calc::Variable", "Variable(\"a\")"),
                },
                AssetRequested {
                    asset: a("calc::Variable", "Variable(\"a\")"),
                    state: AssetState::Ready
                },
                AssetDependencyRegistered {
                    parent: q("calc::EvalFile", "calc::EvalFile(\"expr\")"),
                    asset: a("calc::Variable", "Variable(\"b\")"),
                },
                AssetRequested {
                    asset: a("calc::Variable", "Variable(\"b\")"),
                    state: AssetState::Ready
                },
                AssetDependencyRegistered {
                    parent: q("calc::EvalFile", "calc::EvalFile(\"expr\")"),
                    asset: a("calc::Variable", "Variable(\"c\")"),
                },
                AssetRequested {
                    asset: a("calc::Variable", "Variable(\"c\")"),
                    state: AssetState::Ready
                },
                EarlyCutoffCheck {
                    query: q("calc::EvalFile", "calc::EvalFile(\"expr\")"),
                    output_changed: true
                },
                QueryEnd {
                    query: q("calc::EvalFile", "calc::EvalFile(\"expr\")"),
                    result: Changed
                },
            ]
        );
    }
}

#[test]
fn test_subtraction_and_division() {
    #[cfg(feature = "inspector")]
    let collector = Arc::new(EventCollector::new());

    let runtime = QueryRuntime::new();

    #[cfg(feature = "inspector")]
    runtime.set_sink(Some(collector.clone()));

    runtime.resolve_asset(SourceFile("main".to_string()), "100 - 50 / 2".to_string());

    let result = runtime.query(EvalFile::new("main".to_string())).unwrap();

    // 100 - (50 / 2) = 100 - 25 = 75
    assert_eq!(*result, 75);

    #[cfg(feature = "inspector")]
    {
        use EventKind::*;
        use ExecutionResult::*;

        assert_eq!(
            to_kinds(&collector.trace()),
            vec![
                AssetResolved {
                    asset: a("calc::SourceFile", "SourceFile(\"main\")"),
                    changed: true
                },
                QueryStart {
                    query: q("calc::EvalFile", "calc::EvalFile(\"main\")")
                },
                CacheCheck {
                    query: q("calc::EvalFile", "calc::EvalFile(\"main\")"),
                    valid: false
                },
                DependencyRegistered {
                    parent: q("calc::EvalFile", "calc::EvalFile(\"main\")"),
                    dependency: q("calc::ParseExpr", "calc::ParseExpr(\"main\")"),
                },
                QueryStart {
                    query: q("calc::ParseExpr", "calc::ParseExpr(\"main\")")
                },
                CacheCheck {
                    query: q("calc::ParseExpr", "calc::ParseExpr(\"main\")"),
                    valid: false
                },
                AssetDependencyRegistered {
                    parent: q("calc::ParseExpr", "calc::ParseExpr(\"main\")"),
                    asset: a("calc::SourceFile", "SourceFile(\"main\")"),
                },
                AssetRequested {
                    asset: a("calc::SourceFile", "SourceFile(\"main\")"),
                    state: AssetState::Ready
                },
                EarlyCutoffCheck {
                    query: q("calc::ParseExpr", "calc::ParseExpr(\"main\")"),
                    output_changed: true
                },
                QueryEnd {
                    query: q("calc::ParseExpr", "calc::ParseExpr(\"main\")"),
                    result: Changed
                },
                EarlyCutoffCheck {
                    query: q("calc::EvalFile", "calc::EvalFile(\"main\")"),
                    output_changed: true
                },
                QueryEnd {
                    query: q("calc::EvalFile", "calc::EvalFile(\"main\")"),
                    result: Changed
                },
            ]
        );
    }
}

#[test]
fn test_variable_only() {
    #[cfg(feature = "inspector")]
    let collector = Arc::new(EventCollector::new());

    let runtime = QueryRuntime::new();

    #[cfg(feature = "inspector")]
    runtime.set_sink(Some(collector.clone()));

    runtime.resolve_asset(SourceFile("main".to_string()), "answer".to_string());
    runtime.resolve_asset(Variable("answer".to_string()), 42);

    let result = runtime.query(EvalFile::new("main".to_string())).unwrap();

    assert_eq!(*result, 42);

    #[cfg(feature = "inspector")]
    {
        use EventKind::*;
        use ExecutionResult::*;

        assert_eq!(
            to_kinds(&collector.trace()),
            vec![
                AssetResolved {
                    asset: a("calc::SourceFile", "SourceFile(\"main\")"),
                    changed: true
                },
                AssetResolved {
                    asset: a("calc::Variable", "Variable(\"answer\")"),
                    changed: true
                },
                QueryStart {
                    query: q("calc::EvalFile", "calc::EvalFile(\"main\")")
                },
                CacheCheck {
                    query: q("calc::EvalFile", "calc::EvalFile(\"main\")"),
                    valid: false
                },
                DependencyRegistered {
                    parent: q("calc::EvalFile", "calc::EvalFile(\"main\")"),
                    dependency: q("calc::ParseExpr", "calc::ParseExpr(\"main\")"),
                },
                QueryStart {
                    query: q("calc::ParseExpr", "calc::ParseExpr(\"main\")")
                },
                CacheCheck {
                    query: q("calc::ParseExpr", "calc::ParseExpr(\"main\")"),
                    valid: false
                },
                AssetDependencyRegistered {
                    parent: q("calc::ParseExpr", "calc::ParseExpr(\"main\")"),
                    asset: a("calc::SourceFile", "SourceFile(\"main\")"),
                },
                AssetRequested {
                    asset: a("calc::SourceFile", "SourceFile(\"main\")"),
                    state: AssetState::Ready
                },
                EarlyCutoffCheck {
                    query: q("calc::ParseExpr", "calc::ParseExpr(\"main\")"),
                    output_changed: true
                },
                QueryEnd {
                    query: q("calc::ParseExpr", "calc::ParseExpr(\"main\")"),
                    result: Changed
                },
                AssetDependencyRegistered {
                    parent: q("calc::EvalFile", "calc::EvalFile(\"main\")"),
                    asset: a("calc::Variable", "Variable(\"answer\")"),
                },
                AssetRequested {
                    asset: a("calc::Variable", "Variable(\"answer\")"),
                    state: AssetState::Ready
                },
                EarlyCutoffCheck {
                    query: q("calc::EvalFile", "calc::EvalFile(\"main\")"),
                    output_changed: true
                },
                QueryEnd {
                    query: q("calc::EvalFile", "calc::EvalFile(\"main\")"),
                    result: Changed
                },
            ]
        );
    }
}

#[test]
fn test_empty_source() {
    #[cfg(feature = "inspector")]
    let collector = Arc::new(EventCollector::new());

    let runtime = QueryRuntime::new();

    #[cfg(feature = "inspector")]
    runtime.set_sink(Some(collector.clone()));

    // Don't set any source - should get empty string -> 0

    let result = runtime
        .query(EvalFile::new("nonexistent".to_string()))
        .unwrap();

    assert_eq!(*result, 0);

    #[cfg(feature = "inspector")]
    {
        use EventKind::*;
        use ExecutionResult::*;

        assert_eq!(
            to_kinds(&collector.trace()),
            vec![
                QueryStart {
                    query: q("calc::EvalFile", "calc::EvalFile(\"nonexistent\")")
                },
                CacheCheck {
                    query: q("calc::EvalFile", "calc::EvalFile(\"nonexistent\")"),
                    valid: false
                },
                DependencyRegistered {
                    parent: q("calc::EvalFile", "calc::EvalFile(\"nonexistent\")"),
                    dependency: q("calc::ParseExpr", "calc::ParseExpr(\"nonexistent\")"),
                },
                QueryStart {
                    query: q("calc::ParseExpr", "calc::ParseExpr(\"nonexistent\")")
                },
                CacheCheck {
                    query: q("calc::ParseExpr", "calc::ParseExpr(\"nonexistent\")"),
                    valid: false
                },
                AssetDependencyRegistered {
                    parent: q("calc::ParseExpr", "calc::ParseExpr(\"nonexistent\")"),
                    asset: a("calc::SourceFile", "SourceFile(\"nonexistent\")"),
                },
                AssetRequested {
                    asset: a("calc::SourceFile", "SourceFile(\"nonexistent\")"),
                    state: AssetState::Loading
                },
                EarlyCutoffCheck {
                    query: q("calc::ParseExpr", "calc::ParseExpr(\"nonexistent\")"),
                    output_changed: true
                },
                QueryEnd {
                    query: q("calc::ParseExpr", "calc::ParseExpr(\"nonexistent\")"),
                    result: Changed
                },
                EarlyCutoffCheck {
                    query: q("calc::EvalFile", "calc::EvalFile(\"nonexistent\")"),
                    output_changed: true
                },
                QueryEnd {
                    query: q("calc::EvalFile", "calc::EvalFile(\"nonexistent\")"),
                    result: Changed
                },
            ]
        );
    }
}
