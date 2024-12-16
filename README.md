# Whale

[![GitHub](https://img.shields.io/badge/GitHub-ryo33/whale-222222)](https://github.com/ryo33/whale)
![MIT/Apache 2.0](https://img.shields.io/badge/license-MIT%2FApache--2.0-blue.svg)
[![Crates.io](https://img.shields.io/crates/v/whale)](https://crates.io/crates/whale)
[![docs.rs](https://img.shields.io/docsrs/whale)](https://docs.rs/whale)
![GitHub Repo stars](https://img.shields.io/github/stars/ryo33/whale?style=social)

A lock-free, dependency-tracking primitive for incremental computation.

> [!WARNING]
> This is WIP, and any API is not working yet.

## Design and focus

Whale is designed to be a low-level primitive for building a high-level incremental computing systems.
So it does not provide,

- What actually the "query" is
- How to calculate a query ID
- Any data storage to store the result of a query
- Rich high-level APIs

If you need those, you can:

- Use [salsa](https://github.com/salsa-rs/salsa): A well-known library for incremental computing.
- Use [query-flow](https://github.com/ryo33/query-flow): My high-level implementation of incremental computing engine built on top of Whale.
- Build your own high-level APIs on top of Whale.

## Features

### Mixed Flow Support

The system seamlessly supports a mixture of:

- **Consumer-driven flow:** Where computations react to changes in dependencies (e.g., incremental computing).
- **Producer-driven flow:** Where updates in data trigger re-computation or adjustments (e.g., self-adjustment computing).

### Core Functionalities

The main API functionalities are:

- **Get a node**: `runtime.get(query_id: QueryId)`
  Returns the node of the query. And you can get the version, dependencies, dependents, and invalidation states from the returned node.

- **Iterate over all nodes**: `runtime.keys()`
  Returns all query IDs in the runtime.

- **Registering Dependencies**: `runtime.register(query_id: QueryId, dependencies: Vec<Pointer>)`
  Registers a new version of a query with its dependencies. This effectively manages pairs of query_id and version, and invalidates the dependents of the previous version. This returns both the new and old nodes, and also all invalidations that transitively invalidated by this registration.

- **Updating Dependencies**: `runtime.update_dependencies(query_id: QueryId, dependencies: Vec<Pointer>)`
  Almost same as `register`, but this does not invalidate the dependents of the previous version by this update.
  Typically, this is used when a query is invalidated and recalculated and it does produce the same result as the previous version. If dependencies are the same, prefer the `uninvalidate` instead.

- **Uninvalidating a node**: `runtime.uninvalidate(revision_pointer: RevisionPointer)`
  Mark a specific revision state of a node as not invalidated. This is typically used when a query is recalculated and it does produce the same result as the previous version. If dependencies are changed, use `update_dependencies` instead.

- **Removing an invalidator**: `runtime.remove_invalidator(pointer: Pointer, revision_pointer: RevisionPointer)`
  Removes an invalidation reason from a revision state. This method is used when a query has marked as invalidated by a depended query had invalidated it, and confirmed that the query actually does not need to be re-computed.

- **Removing a node**: `runtime.remove(query_id: QueryId)`
  Removes a node from the runtime. If the node is returned and has dependents, they will be marked as invalidated, and the full list is returned within the result.

- **Detecting a cycle**: `runtime.has_cycle(query_id: QueryId)`
  Detects a cycle in the dependency graph. Even while a graph has cycles, the whole system should work correctly and methods should not hang in infinite loops.

- **Freeing a unused node**: `runtime.remove_if_unused(query_id: QueryId)`
  Removes a node from the runtime if it is not depended by any other queries. This is useful for manual garbage collection when combined with `keys()` to iterate over all nodes.

## Architecture

Whale is built around a lock-free dependency graph where nodes represent computations and edges represent their dependencies. The core components work together to provide efficient dependency tracking:

### Core Components

- **Runtime**: The central coordinator that manages the dependency graph. It's lock-free and safe to clone, making it easy to share across threads.

- **Node**: A vertex in the dependency graph representing a computation. Each node maintains:
  - A unique query ID
  - A version number that changes when the computation result changes
  - Lists of dependencies and dependents
  - An invalidation state tracking when recomputation is needed

- **Pointer**: A reference to a specific version of a computation, consisting of:
  - A query ID to identify the computation
  - A version number to track changes

- **RevisionPointer**: An extended pointer that includes invalidation state, used to:
  - Track precise states of computations
  - Manage invalidation propagation
  - Handle dependency updates

### Lock-free Design

The system uses atomic operations and immutable data structures to achieve thread safety without locks:

- Nodes are updated through atomic compare-and-swap operations
- Dependencies are stored in immutable Arc-wrapped vectors
- Version numbers are managed through atomic counters

This design allows multiple threads to concurrently:

- Query and update computation states
- Propagate invalidations
- Modify the dependency graph

### Consistency

Whale maintains consistency through several key mechanisms:

- **Version Monotonicity**: For each query (not a Runtime-wide), its version number only increases, ensuring a clear timeline of changes.

- **Cyclic safety**: The system is consistent while there are cycles in the dependency graph.
  Also, it does not hang in infinite loops even if there are cycles in the dependency graph.

- **Invalidation Guarantees**: The system provides guarantees about invalidation:
  - All dependent computations are notified of changes, and at least one caller of operation will be notified of the invalidation.
  - Uninvalidating a node succeeds only if the node has not been invalidated since the given revision pointer

- **No Guarantees About**:
  - When get a node, it may be in an dirty state with other runnning operations
	- When get a node, some of dependencies and dependents may be removed already or version is increased one or more times. However the node must be marked as invalidated. So the query must be re-computed.
  - Order of invalidation propagation across different queries

## License

Licensed under either of

- Apache License, Version 2.0
- MIT license

at your option.
