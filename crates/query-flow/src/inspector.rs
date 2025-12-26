//! Inspector integration module.
//!
//! This module is kept for backward compatibility but is now mostly empty.
//! All inspector functionality is integrated directly into the runtime
//! using the `inspector` feature flag.
//!
//! When the `inspector` feature is enabled:
//! - `QueryRuntime` has a `sink` field for event collection
//! - Use `runtime.set_sink(Some(collector))` to enable tracing
//! - Events are emitted automatically during query execution
//!
//! # Example
//!
//! ```ignore
//! use query_flow_inspector::EventCollector;
//! use std::sync::Arc;
//!
//! let collector = Arc::new(EventCollector::new());
//! runtime.set_sink(Some(collector.clone()));
//! runtime.query(MyQuery::new());
//! let trace = collector.trace();
//! ```
