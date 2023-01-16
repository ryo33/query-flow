use super::{Action, QueryOutput};

impl<A: QueryOutput, B: QueryOutput> QueryOutput for (A, B) {
    type Returned = (A::Returned, B::Returned);

    type Cached = (A::Cached, B::Cached);

    fn into_cached(&self) -> Self::Cached {
        (self.0.into_cached(), self.1.into_cached())
    }

    fn action(&self, old: &Self::Cached) -> Action<Self> {
        let a = self.0.action(&old.0);
        let b = self.1.action(&old.1);
        if a.is_none() && b.is_none() {
            Action::None
        } else {
            Action::Update((a.unwrap_or(&self.0), b.unwrap_or(&self.1)))
        }
    }

    fn into_returned(self) -> Self::Returned {
        (self.0.into_returned(), self.1.into_returned())
    }

    fn cached_into_returned<'a>(cached: &'a Self::Cached) -> Self::Returned {
        (
            A::cached_into_returned(&cached.0),
            B::cached_into_returned(&cached.1),
        )
    }
}
