# Whale

[![GitHub](https://img.shields.io/badge/GitHub-ryo33/whale-222222)](https://github.com/ryo33/whale)
![MIT/Apache 2.0](https://img.shields.io/badge/license-MIT%2FApache--2.0-blue.svg)
[![Crates.io](https://img.shields.io/crates/v/whale)](https://crates.io/crates/whale)
[![docs.rs](https://img.shields.io/docsrs/whale)](https://docs.rs/whale)
![GitHub Repo stars](https://img.shields.io/github/stars/ryo33/whale?style=social)

Lock-free, headless, dependency-tracking data structure for incremental computation.

> [!WARNING]
> This is WIP, and any API is not working yet.

## Features

### Mixed Flow Support

The system should seamlessly support a mixture of:
- **Consumer-driven flow:** Where computations react to changes in dependencies (e.g., incremental computing).
- **Producer-driven flow:** Where updates in data trigger re-computation or adjustments (e.g., self-adjustment computing).


3. **Core Functionalities:** The main API functionalities required are:
   - **Registering Dependencies:**
     - ctx.register_new_version(query_id, referenced_dependencies): Registers a new version of a query with its dependencies. This should effectively manage pairs of query_id and version, and invalidate any previous versions.
   - **Checking for Recomputation Needs:**
     - ctx.needs_recomputation(query_id): Returns true if any dependency of the specified query has changed.
   - **Finding Dependents:**
     - ctx.dependents(query_id): Returns a list of query IDs that reference the specified query_id.
   - **Suggesting Recomputations:**
     - ctx.next_computation_suggests(): Provides a list of query IDs whose direct dependencies have been invalidated, suggesting they need recomputation.

## Architecture
