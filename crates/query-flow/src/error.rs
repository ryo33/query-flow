//! Error types for query execution.

use std::fmt;

/// System-level query errors.
///
/// These are distinct from user domain errors, which should be wrapped
/// in `Query::Output` (e.g., `type Output = Result<T, MyError>`).
#[derive(Debug, Clone)]
pub enum QueryError {
    /// Query is waiting for async loading to complete.
    ///
    /// This is returned when a dependency is still loading via a background task.
    /// Use `runtime.query_async()` to wait for loading to complete, or handle
    /// explicitly in your query logic.
    Suspend,

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
}

impl fmt::Display for QueryError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            QueryError::Suspend => write!(f, "query suspended: waiting for async loading"),
            QueryError::Cycle { path } => {
                write!(f, "dependency cycle detected: {}", path.join(" -> "))
            }
            QueryError::Cancelled => write!(f, "query cancelled"),
            QueryError::MissingDependency { description } => {
                write!(f, "missing dependency: {}", description)
            }
        }
    }
}

impl std::error::Error for QueryError {}
