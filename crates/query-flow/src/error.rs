//! Error types for query execution.

use std::fmt;
use std::marker::PhantomData;
use std::ops::Deref;
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

impl QueryError {
    /// Returns a reference to the inner user error if this is a `UserError` variant.
    pub fn user_error(&self) -> Option<&Arc<anyhow::Error>> {
        match self {
            QueryError::UserError(e) => Some(e),
            _ => None,
        }
    }

    /// Attempts to downcast the user error to a specific type.
    ///
    /// Returns `Some(&E)` if this is a `UserError` containing an error of type `E`,
    /// otherwise returns `None`.
    pub fn downcast_ref<E: std::error::Error + Send + Sync + 'static>(&self) -> Option<&E> {
        self.user_error().and_then(|e| e.downcast_ref::<E>())
    }

    /// Returns `true` if this is a `UserError` containing an error of type `E`.
    pub fn is<E: std::error::Error + Send + Sync + 'static>(&self) -> bool {
        self.downcast_ref::<E>().is_some()
    }
}

/// A typed wrapper around a user error that provides `Deref` access to the inner error type.
///
/// This struct holds an `Arc<anyhow::Error>` internally and provides safe access to
/// the downcasted error reference. The `Arc` ensures the error remains valid for the
/// lifetime of this wrapper.
///
/// # Example
///
/// ```ignore
/// use query_flow::{QueryResultExt, TypedErr};
///
/// let result = db.query(MyQuery::new()).downcast_err::<MyError>()?;
/// match result {
///     Ok(value) => { /* success */ }
///     Err(typed_err) => {
///         // typed_err derefs to &MyError
///         println!("Error code: {}", typed_err.code);
///     }
/// }
/// ```
#[derive(Clone)]
pub struct TypedErr<E> {
    arc: Arc<anyhow::Error>,
    _marker: PhantomData<E>,
}

impl<E: std::error::Error + Send + Sync + 'static> TypedErr<E> {
    fn new(arc: Arc<anyhow::Error>) -> Option<Self> {
        // Verify the downcast is valid before constructing
        if arc.downcast_ref::<E>().is_some() {
            Some(Self {
                arc,
                _marker: PhantomData,
            })
        } else {
            None
        }
    }

    /// Returns a reference to the inner error.
    pub fn get(&self) -> &E {
        // Safe because we verified the type in `new`
        self.arc.downcast_ref::<E>().unwrap()
    }
}

impl<E: std::error::Error + Send + Sync + 'static> Deref for TypedErr<E> {
    type Target = E;

    fn deref(&self) -> &E {
        self.get()
    }
}

impl<E: std::error::Error + Send + Sync + 'static> fmt::Debug for TypedErr<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.get(), f)
    }
}

impl<E: std::error::Error + Send + Sync + 'static> fmt::Display for TypedErr<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self.get(), f)
    }
}

/// Extension trait for query results that provides ergonomic error downcasting.
///
/// This trait is implemented for `Result<Arc<T>, QueryError>` and allows you to
/// downcast user errors to a specific type while propagating system errors.
///
/// # Example
///
/// ```ignore
/// use query_flow::QueryResultExt;
///
/// // Downcast to MyError, propagating system errors and non-matching user errors
/// let result = db.query(MyQuery::new()).downcast_err::<MyError>()?;
///
/// match result {
///     Ok(value) => println!("Success: {:?}", value),
///     Err(my_err) => println!("MyError: {}", my_err.code),
/// }
/// ```
pub trait QueryResultExt<T> {
    /// Attempts to downcast a `UserError` to a specific error type.
    ///
    /// # Returns
    ///
    /// - `Ok(Ok(value))` - The query succeeded with `value`
    /// - `Ok(Err(typed_err))` - The query failed with a `UserError` of type `E`
    /// - `Err(query_error)` - The query failed with a system error, or a `UserError`
    ///   that is not of type `E`
    ///
    /// # Example
    ///
    /// ```ignore
    /// // Handle specific error type, propagate others
    /// let result = db.query(MyQuery::new()).downcast_err::<MyError>()?;
    /// let value = result.map_err(|e| {
    ///     eprintln!("MyError occurred: {}", e.message);
    ///     e
    /// })?;
    /// ```
    fn downcast_err<E: std::error::Error + Send + Sync + 'static>(
        self,
    ) -> Result<Result<Arc<T>, TypedErr<E>>, QueryError>;
}

impl<T> QueryResultExt<T> for Result<Arc<T>, QueryError> {
    fn downcast_err<E: std::error::Error + Send + Sync + 'static>(
        self,
    ) -> Result<Result<Arc<T>, TypedErr<E>>, QueryError> {
        match self {
            Ok(value) => Ok(Ok(value)),
            Err(QueryError::UserError(arc)) => match TypedErr::new(arc.clone()) {
                Some(typed) => Ok(Err(typed)),
                None => Err(QueryError::UserError(arc)),
            },
            Err(other) => Err(other),
        }
    }
}
