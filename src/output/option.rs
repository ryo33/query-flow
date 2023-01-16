use super::{Action, QueryOutput};

impl<T: QueryOutput> QueryOutput for Option<T> {
    type Returned = Option<T::Returned>;

    type Cached = Option<T::Cached>;

    fn into_cached(&self) -> Self::Cached {
        self.as_ref().map(|x| x.into_cached())
    }

    fn action(&self, old: &Self::Cached) -> Action<Self> {
        match (self, old) {
            (Some(new), Some(old)) => match new.action(old) {
                Action::None => Action::None,
                Action::Update(cached) => Action::Update(Some(cached)),
            },
            (None, None) => Action::None,
            (Some(new), None) => Action::Update(Some(new.into_cached())),
            (None, Some(_old)) => Action::Update(None),
        }
    }

    fn into_returned(self) -> Self::Returned {
        self.map(|x| x.into_returned())
    }

    fn cached_into_returned<'a>(cached: &'a Self::Cached) -> Self::Returned {
        cached.as_ref().map(|x| T::cached_into_returned(&x))
    }
}
