//! Loading state for async resource handling.

use crate::QueryError;

/// Represents the loading state of an async resource.
///
/// Use this as your `Query::Output` type when the query needs to load
/// data asynchronously (e.g., file I/O, network requests).
///
/// # Example
///
/// ```ignore
/// struct LoadFile { path: PathBuf }
///
/// impl Query for LoadFile {
///     type CacheKey = PathBuf;
///     type Output = LoadingState<String>;
///
///     fn query(&self, ctx: &mut QueryContext) -> Result<Self::Output, QueryError> {
///         // Check if already loaded
///         if let Some(content) = ctx.get_loaded(&self.path) {
///             return Ok(LoadingState::Ready(content));
///         }
///
///         // Spawn background loader
///         ctx.spawn_loader(self.cache_key(), async {
///             tokio::fs::read_to_string(&self.path).await.unwrap()
///         });
///
///         Err(QueryError::Suspend)
///     }
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub enum LoadingState<T> {
    /// Resource is still loading.
    #[default]
    Loading,
    /// Resource is ready with the given value.
    Ready(T),
}

impl<T> LoadingState<T> {
    /// Check if the resource is still loading.
    pub fn is_loading(&self) -> bool {
        matches!(self, LoadingState::Loading)
    }

    /// Check if the resource is ready.
    pub fn is_ready(&self) -> bool {
        matches!(self, LoadingState::Ready(_))
    }

    /// Get the value if ready, None if loading.
    pub fn get(&self) -> Option<&T> {
        match self {
            LoadingState::Loading => None,
            LoadingState::Ready(t) => Some(t),
        }
    }

    /// Get the value if ready, None if loading (consuming version).
    pub fn into_inner(self) -> Option<T> {
        match self {
            LoadingState::Loading => None,
            LoadingState::Ready(t) => Some(t),
        }
    }

    /// Convert to Result - Loading becomes Err(QueryError::Suspend).
    ///
    /// Use this with the `?` operator to propagate loading state upward.
    ///
    /// # Example
    ///
    /// ```ignore
    /// fn query(&self, ctx: &mut QueryContext) -> Result<MyOutput, QueryError> {
    ///     let data = ctx.query(LoadData { id: self.id })?.suspend()?;
    ///     // `data` is guaranteed to be ready here
    ///     Ok(process(data))
    /// }
    /// ```
    pub fn suspend(self) -> Result<T, QueryError> {
        match self {
            LoadingState::Loading => Err(QueryError::Suspend),
            LoadingState::Ready(t) => Ok(t),
        }
    }

    /// Reference version of suspend.
    pub fn suspend_ref(&self) -> Result<&T, QueryError> {
        match self {
            LoadingState::Loading => Err(QueryError::Suspend),
            LoadingState::Ready(t) => Ok(t),
        }
    }

    /// Map the inner value if ready.
    pub fn map<U, F: FnOnce(T) -> U>(self, f: F) -> LoadingState<U> {
        match self {
            LoadingState::Loading => LoadingState::Loading,
            LoadingState::Ready(t) => LoadingState::Ready(f(t)),
        }
    }

    /// Flat map the inner value if ready.
    pub fn and_then<U, F: FnOnce(T) -> LoadingState<U>>(self, f: F) -> LoadingState<U> {
        match self {
            LoadingState::Loading => LoadingState::Loading,
            LoadingState::Ready(t) => f(t),
        }
    }
}

impl<T> From<T> for LoadingState<T> {
    fn from(value: T) -> Self {
        LoadingState::Ready(value)
    }
}

impl<T> From<Option<T>> for LoadingState<T> {
    fn from(opt: Option<T>) -> Self {
        match opt {
            Some(t) => LoadingState::Ready(t),
            None => LoadingState::Loading,
        }
    }
}
