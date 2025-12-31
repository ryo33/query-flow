//! Error types for query execution.

use std::fmt;
use std::sync::Arc;

use crate::asset::PendingAsset;
use crate::key::FullCacheKey;

/// Query errors including both system-level and user errors.
///
/// User errors can be propagated using the `?` operator, which automatically
/// converts any `Into<anyhow::Error>` type into `QueryError::UserError`.
#[derive(Debug, Clone)]
pub enum QueryError {
    /// Query is waiting for async loading to complete.
    ///
    /// This is returned when a dependency is still loading via a background task.
    /// Use `runtime.query_async()` to wait for loading to complete, or handle
    /// explicitly in your query logic.
    ///
    /// The `asset` field contains information about the pending asset, which can
    /// be downcast to the original key type using `asset.key::<K>()`.
    Suspend {
        /// The pending asset that caused the suspension.
        asset: PendingAsset,
    },

    /// Dependency cycle detected.
    ///
    /// The query graph contains a cycle, which would cause infinite recursion.
    /// The `path` contains a debug representation of the cycle.
    Cycle {
        /// Debug representation of the queries forming the cycle.
        path: Vec<String>,
    },

    /// Query execution was cancelled.
    Cancelled,

    /// A required dependency is missing.
    MissingDependency {
        /// Description of the missing dependency.
        description: String,
    },

    /// Dependencies were removed during query execution.
    ///
    /// This can happen if another thread removes queries or assets
    /// while this query is being registered.
    DependenciesRemoved {
        /// Keys that were not found during registration.
        missing_keys: Vec<FullCacheKey>,
    },

    /// User-defined error.
    ///
    /// This variant allows user errors to be propagated through the query system
    /// using the `?` operator. Any type implementing `Into<anyhow::Error>` can be
    /// converted to this variant.
    ///
    /// Unlike system errors (Suspend, Cycle, etc.), UserError results are cached
    /// and participate in early cutoff optimization.
    UserError(Arc<anyhow::Error>),
}

impl fmt::Display for QueryError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            QueryError::Suspend { asset } => {
                write!(f, "query suspended: waiting for {}", asset.debug_repr())
            }
            QueryError::Cycle { path } => {
                write!(f, "dependency cycle detected: {}", path.join(" -> "))
            }
            QueryError::Cancelled => write!(f, "query cancelled"),
            QueryError::MissingDependency { description } => {
                write!(f, "missing dependency: {}", description)
            }
            QueryError::DependenciesRemoved { missing_keys } => {
                write!(
                    f,
                    "dependencies removed during execution: {:?}",
                    missing_keys
                )
            }
            QueryError::UserError(e) => write!(f, "user error: {}", e),
        }
    }
}

impl<T: Into<anyhow::Error>> From<T> for QueryError {
    fn from(err: T) -> Self {
        QueryError::UserError(Arc::new(err.into()))
    }
}
