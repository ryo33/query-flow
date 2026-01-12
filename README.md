# query-flow

[![GitHub](https://img.shields.io/badge/GitHub-ryo33/query--flow-222222)](https://github.com/ryo33/query-flow)
![MIT/Apache 2.0](https://img.shields.io/badge/license-MIT%2FApache--2.0-blue.svg)
[![Crates.io](https://img.shields.io/crates/v/query-flow)](https://crates.io/crates/query-flow)
[![docs.rs](https://img.shields.io/docsrs/query-flow)](https://docs.rs/query-flow)
![GitHub Repo stars](https://img.shields.io/github/stars/ryo33/query-flow?style=social)

An ergonomic, runtime-agnostic framework for incremental computation.

> [!WARNING]
> Currently in dogfooding phase with the [Eure](https://github.com/Hihaheho/eure/tree/main/crates/eure/src/query) project's CLI, LSP, and Web Playground.

## Features

- **Runtime-agnostic**: Sync query logic with suspense pattern — works with any event loop or async runtime
- **Automatic caching**: Query results are cached and invalidated based on dependencies
- **Type-safe**: Per-query-type caching with compile-time guarantees
- **Lock-free API**: Concurrent access from multiple threads via [whale](#whale)

## Quick Start

```rust
use query_flow::{query, Db, QueryError, QueryRuntime};

#[query]
fn add(db: &impl Db, a: i32, b: i32) -> Result<i32, QueryError> {
    Ok(a + b)
}

let runtime = QueryRuntime::new();
let result = runtime.query(Add::new(1, 2)).unwrap();
assert_eq!(*result, 3);
```

## Core Concepts

- **Query**: A derived computation that is cached and automatically invalidated when its dependencies change. Queries can depend on other queries or assets.
- **Asset**: An external input (files, network data, user input) that queries can depend on. Assets are resolved asynchronously and trigger the suspense pattern when not yet available.
- **Runtime**: The `QueryRuntime` manages query execution, caching, dependency tracking, and asset resolution.

## Defining Queries

### Using the `#[query]` Macro

The `#[query]` macro transforms a function into a query struct implementing the `Query` trait:

```rust
use query_flow::{query, Db, QueryError};

// Basic query - generates `Add` struct
#[query]
fn add(db: &impl Db, a: i32, b: i32) -> Result<i32, QueryError> {
    Ok(a + b)
}

// Query with dependencies
#[query]
fn double_sum(db: &impl Db, a: i32, b: i32) -> Result<i32, QueryError> {
    let sum = db.query(Add::new(a, b))?;
    Ok(*sum * 2)
}
```

### Macro Options

| Option | Example | Description |
|--------|---------|-------------|
| `keys(...)` | `#[query(keys(id))]` | Only specified fields used as cache key |
| `name = "..."` | `#[query(name = "FetchUserById")]` | Custom struct name |
| `output_eq = fn` | `#[query(output_eq = my_eq)]` | Custom equality for early cutoff |

### Manual Query Implementation

For full control, implement the `Query` trait directly:

```rust
use std::sync::Arc;
use query_flow::{Query, Db, QueryError, Key};

#[derive(Clone)]
struct Add { a: i32, b: i32 }

impl Query for Add {
    type CacheKey = (i32, i32);
    type Output = i32;

    fn cache_key(&self) -> Self::CacheKey {
        (self.a, self.b)
    }

    fn query(self, _db: &impl Db) -> Result<Arc<Self::Output>, QueryError> {
        Ok(Arc::new(self.a + self.b))
    }

    fn output_eq(old: &Self::Output, new: &Self::Output) -> bool {
        old == new
    }
}
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

// With selective key fields (only `path` used for Hash/Eq)
#[asset_key(asset = String, key(path))]
pub struct CountedAsset {
    path: String,
    call_count: Arc<AtomicU32>,  // Not part of key
}

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
fn process_config(db: &impl Db, path: PathBuf) -> Result<Config, QueryError> {
    // Get asset - suspends automatically if not ready
    let content = db.asset(ConfigFile(path.clone()))?;

    // Parse and return
    Ok(parse_config(&content))
}
```

### Asset Locators (Optional)

Locators are **optional**. Without a locator, assets always return `Pending` and must be resolved externally via `resolve_asset()` or `resolve_asset_error()`.

Register a locator when you need:
- **Immediate resolution**: Return `Ready` for assets available synchronously
- **Validation/hooks**: Reject invalid keys or log access patterns
- **Query-based DI**: Use `db.query()` to determine loading behavior dynamically

```rust
use query_flow::{asset_locator, Db, LocateResult, QueryError, DurabilityLevel};

#[asset_locator]
fn config_locator(db: &impl Db, key: &ConfigFile) -> Result<LocateResult<String>, QueryError> {
    // Validation: reject disallowed paths
    let config = db.query(GetConfig)?;
    if !config.allowed_paths.contains(&key.0) {
        return Err(anyhow::anyhow!("Path not allowed").into());
    }

    // Immediate resolution for bundled files
    if let Some(content) = BUNDLED_FILES.get(&key.0) {
        return Ok(LocateResult::Ready {
            value: content.clone(),
            durability: DurabilityLevel::Static,
        });
    }

    // Otherwise, defer to external loading
    Ok(LocateResult::Pending)
}

runtime.register_asset_locator(ConfigLocator);
```

The `#[asset_locator]` macro generates a struct (PascalCase of function name) implementing `AssetLocator`.

### Durability Levels

Durability is specified when resolving assets and helps optimize invalidation propagation:

| Level | Description |
|-------|-------------|
| `Volatile` | Changes frequently (user input, live feeds) |
| `Transient` | Changes occasionally (configuration, session data) |
| `Stable` | Changes rarely (external dependencies) |
| `Static` | Fixed for this session (bundled assets, constants) |

```rust
runtime.resolve_asset(ConfigFile(path), content, DurabilityLevel::Volatile);
runtime.resolve_asset(BundledAsset(name), data, DurabilityLevel::Static);
```

### Asset Invalidation

```rust
// File was modified externally
runtime.invalidate_asset(&ConfigFile(path));
// Dependent queries will now suspend until resolved

// Remove asset entirely
runtime.remove_asset(&ConfigFile(path));
```

### Suspense Pattern

The suspense pattern allows sync query code to handle async operations. `db.asset()` returns the asset value directly, suspending automatically if not ready.

#### Pattern 1: Suspend until ready (default)

Use `db.asset()` to get an asset. It automatically returns `Err(QueryError::Suspend)` if loading.

```rust
#[query]
fn process_config(db: &impl Db, path: ConfigFile) -> Result<Config, QueryError> {
    let content = db.asset(path)?;  // Returns Err(Suspend) if loading
    Ok(parse_config(&content))
}
```

When a query suspends, the runtime tracks which assets are pending. In your event loop, resolve assets when they become available:

```rust
// You can check what's pending:
for pending in runtime.pending_assets_of::<ConfigFile>() {
    start_loading(&pending.0);
}

// In your event loop, when file content is loaded:
runtime.resolve_asset(ConfigFile(path), content, DurabilityLevel::Volatile);

// Or if loading failed:
runtime.resolve_asset_error(ConfigFile(path), io_error, DurabilityLevel::Volatile);

// Then retry the query
let result = runtime.query(ProcessConfig::new(path))?;
```

#### Pattern 2: Handle loading state explicitly

Use `db.asset_state()` to get an `AssetLoadingState` for explicit loading state handling:

```rust
#[query]
fn eval_expr(db: &impl Db, name: String) -> Result<i64, QueryError> {
    // Return 0 while loading, use actual value when ready
    let value = db.asset_state(Variable(name))?
        .into_inner()
        .map(|v| *v)
        .unwrap_or(0);
    Ok(value)
}
```

## Error Handling

Queries return `Result<Arc<Output>, QueryError>`. The error variants are:

**System errors** (not cached):
- `Suspend` - An asset is not yet available. See [Suspense Pattern](#suspense-pattern).
- `Cycle` - A dependency cycle was detected in the query graph.
- `Cancelled` - Query explicitly returned cancellation (not cached, unlike `UserError`).
- `MissingDependency` - An asset locator indicated the asset is not found or not allowed.
- `DependenciesRemoved` - Dependencies were removed by another thread during execution.
- `InconsistentAssetResolution` - An asset was resolved during query execution, possibly causing inconsistent state.

**User errors** (cached like successful results):
- `UserError(Arc<anyhow::Error>)` - Domain errors from your query logic, automatically converted via `?` operator.

```rust
// User errors with ? operator - errors are automatically converted
#[query]
fn parse_int(db: &impl Db, input: String) -> Result<i32, QueryError> {
    let num: i32 = input.parse()?;  // ParseIntError -> QueryError::UserError
    Ok(num)
}

// System errors propagate automatically
#[query]
fn process(db: &impl Db, id: u64) -> Result<Output, QueryError> {
    let data = db.query(FetchData::new(id))?;  // Propagates Suspend, Cycle, UserError, etc.
    Ok(transform(*data))
}
```

### Handling Specific Error Types

Use `downcast_err()` to handle specific user error types while propagating others:

```rust
use query_flow::QueryResultExt;

let result = db.query(MyQuery::new()).downcast_err::<MyError>()?;
match result {
    Ok(value) => { /* success */ }
    Err(my_err) => {
        // my_err derefs to &MyError
        println!("Error code: {}", my_err.code);
    }
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

## Subscription Pattern

Use `runtime.poll()` to track query changes with revision numbers. This is useful for push-based notifications (e.g., LSP diagnostics).

```rust
struct Subscription<Q: Query> {
    query: Q,
    last_revision: RevisionCounter,
}

// Poll and return only when changed
fn poll_subscription<Q: Query>(
    db: &impl Db,
    sub: &mut Subscription<Q>,
) -> Result<Option<Arc<Q::Output>>, QueryError> {
    let polled = db.poll(sub.query.clone())?;
    if polled.revision != sub.last_revision {
        sub.last_revision = polled.revision;
        Ok(Some(polled.value?))
    } else {
        Ok(None)
    }
}
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
runtime.resolve_asset_error(key, error, DurabilityLevel::Volatile);
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
