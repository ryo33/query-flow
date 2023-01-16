use super::QueryOutput;

impl QueryOutput for () {
    type Returned = Self;

    type Cached = Self;

    fn into_cached(&self) -> Self::Cached {
        *self
    }

    fn action(&self, old: &Self::Cached) -> super::Action<Self> {
        super::Action::None
    }

    fn into_returned(self) -> Self::Returned {
        self
    }

    fn cached_into_returned<'a>(cached: &'a Self::Cached) -> Self::Returned {
        *cached
    }
}
