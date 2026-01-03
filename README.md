# query-flow

[![GitHub](https://img.shields.io/badge/GitHub-ryo33/query--flow-222222)](https://github.com/ryo33/query-flow)
![MIT/Apache 2.0](https://img.shields.io/badge/license-MIT%2FApache--2.0-blue.svg)
[![Crates.io](https://img.shields.io/crates/v/query-flow)](https://crates.io/crates/query-flow)
[![docs.rs](https://img.shields.io/docsrs/query-flow)](https://docs.rs/query-flow)
![GitHub Repo stars](https://img.shields.io/github/stars/ryo33/query-flow?style=social)

A high-level query framework for incremental computation in Rust.

> [!WARNING]
> This is WIP

## Features

- **Async-agnostic queries**: Write sync query logic, run with sync or async runtime
- **Automatic caching**: Query results are cached and invalidated based on dependencies
- **Suspense pattern**: Handle async loading with `LoadingState` without coloring functions
- **Type-safe**: Per-query-type caching with compile-time guarantees
- **Early cutoff**: Skip downstream recomputation when values don't change
- **Lock-free**: Built on [whale](#whale), a lock-free dependency-tracking primitive

## Quick Start

```rust
use query_flow::{query, QueryContext, QueryError, QueryRuntime};

#[query]
fn add(ctx: &mut QueryContext, a: i32, b: i32) -> Result<i32, QueryError> {
    Ok(a + b)
}

let runtime = QueryRuntime::new();
let result = runtime.query(Add::new(1, 2)).unwrap();
assert_eq!(*result, 3);
```

## Defining Queries

### Using the `#[query]` Macro

The `#[query]` macro transforms a function into a query struct implementing the `Query` trait:

```rust
use query_flow::{query, QueryContext, QueryError};

// Basic query - generates `Add` struct
#[query]
fn add(ctx: &mut QueryContext, a: i32, b: i32) -> Result<i32, QueryError> {
    Ok(a + b)
}

// Query with dependencies
#[query]
fn double_sum(ctx: &mut QueryContext, a: i32, b: i32) -> Result<i32, QueryError> {
    let sum = ctx.query(Add::new(*a, *b))?;
    Ok(*sum * 2)
}
```

### Macro Options

```rust
// Selective cache keys - only `id` is part of the key
#[query(keys(id))]
fn fetch_user(db: &impl Db, id: u64, include_deleted: bool) -> Result<User, QueryError> {
    // Queries with same `id` share cache, regardless of `include_deleted`
}

// Custom struct name
#[query(name = "FetchUserById")]
fn fetch_user(db: &impl Db, id: u64) -> Result<User, QueryError> { ... }

// Custom output equality (for types without PartialEq)
#[query(output_eq = my_custom_eq)]
fn complex_query(db: &impl Db) -> Result<ComplexType, QueryError> { ... }
```

### Manual Query Implementation

For full control, implement the `Query` trait directly:

```rust
use query_flow::{Query, QueryContext, QueryError, Key};

struct Add { a: i32, b: i32 }

impl Query for Add {
    type CacheKey = (i32, i32);
    type Output = i32;

    fn cache_key(&self) -> Self::CacheKey {
        (self.a, self.b)
    }

    fn query(&self, _ctx: &mut QueryContext) -> Result<Self::Output, QueryError> {
        Ok(self.a + self.b)
    }

    fn output_eq(old: &Self::Output, new: &Self::Output) -> bool {
        old == new
    }
}
```

## Error Handling

query-flow supports both **system errors** and **user errors** through `QueryError`:

- **System errors**: `Suspend`, `Cycle`, `Cancelled`, `MissingDependency`
- **User errors**: `UserError(Arc<anyhow::Error>)` - cached like successful results

```rust
// User errors with ? operator - errors are automatically converted
#[query]
fn parse_int(ctx: &mut QueryContext, input: String) -> Result<i32, QueryError> {
    let num: i32 = input.parse()?;  // ParseIntError -> QueryError::UserError
    Ok(num)
}

// System errors propagate automatically
#[query]
fn process(ctx: &mut QueryContext, id: u64) -> Result<Output, QueryError> {
    let data = ctx.query(FetchData::new(id))?;  // Propagates Suspend, Cycle, UserError, etc.
    Ok(transform(*data))
}
```

### Error Comparator for Early Cutoff

By default, all `UserError` values are considered different (conservative). Use `QueryRuntimeBuilder` to customize:

```rust
let runtime = QueryRuntime::builder()
    .error_comparator(|a, b| {
        // Treat errors as equal if they have the same message
        a.to_string() == b.to_string()
    })
    .build();
```

## Assets: External Inputs

Assets represent external resources (files, network data) that queries can depend on:

### Defining Asset Keys

```rust
use query_flow::{asset_key, AssetKey};
use std::path::PathBuf;

// Using the macro
#[asset_key(asset = String)]
pub struct ConfigFile(pub PathBuf);

#[asset_key(asset = Vec<u8>)]
pub struct BinaryAsset(pub PathBuf);

// Manual implementation
pub struct TextureId(pub u32);

impl AssetKey for TextureId {
    type Asset = ImageData;

    fn asset_eq(old: &Self::Asset, new: &Self::Asset) -> bool {
        old.bytes == new.bytes
    }
}
```

### Using Assets in Queries

```rust
#[query]
fn process_config(ctx: &mut QueryContext, path: PathBuf) -> Result<Config, QueryError> {
    // Get asset - returns LoadingState<Arc<String>>
    let content = ctx.asset(&ConfigFile(path.clone()))?;

    // Suspend if not ready (propagates to caller)
    let content = content.suspend()?;

    // Parse and return
    Ok(parse_config(&content))
}
```

### Asset Loading Flow

```rust
use query_flow::DurabilityLevel;

let runtime = QueryRuntime::new();

// Optional: Register a locator for immediate resolution
runtime.register_asset_locator(MyFileLocator::new());

// Execute query - may return Err(Suspend) if assets are loading
match runtime.query(ProcessConfig::new(path)) {
    Ok(result) => println!("Done: {:?}", result),
    Err(QueryError::Suspend) => {
        // Handle pending assets
        for pending in runtime.pending_assets() {
            if let Some(path) = pending.key::<ConfigFile>() {
                let content = std::fs::read_to_string(&path.0)?;
                // Durability is specified at resolve time
                runtime.resolve_asset(path.clone(), content, DurabilityLevel::Volatile);
            }
        }
        // Retry query
        let result = runtime.query(ProcessConfig::new(path))?;
    }
    Err(e) => return Err(e),
}
```

### Asset Invalidation

```rust
// File was modified externally
runtime.invalidate_asset(&ConfigFile(path));
// Dependent queries will now suspend until resolved

// Remove asset entirely
runtime.remove_asset(&ConfigFile(path));
```

## Suspense Pattern

The suspense pattern allows sync query code to handle async operations:

```rust
/// LoadingState<T> represents async loading state
pub enum LoadingState<T> {
    Loading,
    Ready(T),
}

impl<T> LoadingState<T> {
    /// Convert to Result - Loading becomes Err(Suspend)
    pub fn suspend(self) -> Result<T, QueryError>;

    pub fn is_loading(&self) -> bool;
    pub fn is_ready(&self) -> bool;
    pub fn get(&self) -> Option<&T>;
    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> LoadingState<U>;
}
```

## Durability Levels

Durability is specified when resolving assets and helps optimize invalidation propagation:

| Level | Value | Description |
|-------|-------|-------------|
| `Volatile` | 0 | Changes frequently (user input, live feeds) |
| `Transient` | 1 | Changes occasionally (configuration, session data) |
| `Stable` | 2 | Changes rarely (external dependencies) |
| `Static` | 3 | Fixed for this session (bundled assets, constants) |

```rust
// Durability is specified at resolve_asset time
runtime.resolve_asset(ConfigFile(path), content, DurabilityLevel::Volatile);
runtime.resolve_asset(BundledAsset(name), data, DurabilityLevel::Static);
```

## QueryRuntime API

```rust
let runtime = QueryRuntime::new();

// Execute queries
let result = runtime.query(MyQuery::new(...))?;

// Invalidation
runtime.invalidate::<MyQuery>(&cache_key);
runtime.clear_cache();

// Asset management
runtime.register_asset_locator(locator);
runtime.resolve_asset(key, value, DurabilityLevel::Volatile);
runtime.invalidate_asset(&key);
runtime.remove_asset(&key);

// Pending assets
runtime.pending_assets();           // All pending
runtime.pending_assets_of::<K>();   // Filtered by type
runtime.has_pending_assets();
```

## Crates

| Crate | Description |
|-------|-------------|
| [`query-flow`](https://crates.io/crates/query-flow) | High-level query framework with automatic caching and dependency tracking |
| [`query-flow-macros`](https://crates.io/crates/query-flow-macros) | Procedural macros for defining queries |
| [`query-flow-inspector`](https://crates.io/crates/query-flow-inspector) | Debugging and inspection tools |
| [`whale`](https://crates.io/crates/whale) | Low-level lock-free dependency-tracking primitive |

## Whale

Whale is the low-level primitive that powers query-flow. It provides lock-free dependency tracking without opinions about what queries are or how to store their results.

### When to Use Whale Directly

Use `query-flow` if you want a batteries-included incremental computation framework. Use `whale` directly if you need:

- Full control over query representation and storage
- Custom invalidation strategies
- Integration with existing systems
- Maximum flexibility

### Whale Design

Whale is designed to be a minimal primitive for building high-level incremental computing systems. It does not provide:

- What actually the "query" is
- How to calculate a query ID
- Any data storage to store the result of a query
- Rich high-level APIs

### Whale Architecture

Whale is built around a lock-free dependency graph where nodes represent computations and edges represent their dependencies.

**Core Components:**

- **Runtime**: The central coordinator that manages the dependency graph. Lock-free and safe to clone across threads.
- **Node**: A vertex representing a computation with version, dependencies, dependents, and invalidation state.
- **Pointer**: A reference to a specific version of a computation (query ID + version).
- **RevisionPointer**: An extended pointer including invalidation state for precise state tracking.

**Lock-free Design:**

The system uses atomic operations and immutable data structures:

- Nodes are updated through atomic compare-and-swap operations
- Dependencies and dependents are stored in immutable collections
- Version numbers are managed through atomic counters

This allows multiple threads to concurrently query states, propagate invalidations, and modify the dependency graph.

**Consistency Guarantees:**

- **Version Monotonicity**: Version numbers only increase per query
- **Cyclic Safety**: Remains functional even with cycles in the dependency graph
- **Invalidation Guarantees**: All dependents are notified of changes

### Alternatives

- [salsa](https://github.com/salsa-rs/salsa): A well-known library for incremental computing with a different design philosophy.

## License

Licensed under either of

- Apache License, Version 2.0
- MIT license

at your option.
