mod arc;
mod option;
mod tuple;
mod unit;

// Sized is required for From<Self>.
pub trait QueryOutput: Sized {
    /// The type of enum that is returned by the query.
    type Returned;
    /// The type to be stored in the storage.
    type Cached;

    /// Converts the output to stored type.
    fn into_cached(&self) -> Self::Cached;
    /// Returns a next action for a new output.
    fn action(&self, old: &Self::Cached) -> Action<Self>;
    /// Converts `Self` into `Self::Returned`.
    fn into_returned(self) -> Self::Returned;
    /// Converts `Self::Cached` into `Self::Returned`.
    fn cached_into_returned(cached: &Self::Cached) -> Self::Returned;
}

pub type OutputReturned<T: QueryOutput> = T::Returned;

pub enum Action<T: QueryOutput> {
    /// The output is the same as the old one.
    None,
    /// The output is different from the old one.
    Update(T::Cached),
}

impl<T: QueryOutput> From<&T> for Action<T> {
    fn from(value: &T) -> Self {
        Action::Update(value.into_cached())
    }
}

impl<T: QueryOutput> Action<T> {
    pub fn is_none(&self) -> bool {
        matches!(self, Action::None)
    }
    pub fn unwrap_or(self, default: &T) -> T::Cached {
        match self {
            Action::None => default.into_cached(),
            Action::Update(cached) => cached,
        }
    }
}
