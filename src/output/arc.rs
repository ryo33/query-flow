use crate::rc::CfgRc;

use super::{Action, QueryOutput};

impl<T: PartialEq> QueryOutput for CfgRc<T> {
    type Returned = Self;
    type Cached = Self;

    fn into_cached(&self) -> Self::Cached {
        self.clone()
    }

    fn action(&self, old: &Self::Cached) -> Action<Self::Cached> {
        if self == old {
            Action::None
        } else {
            self.into()
        }
    }

    fn into_returned(self) -> Self::Returned {
        self
    }

    fn cached_into_returned(cached: &Self::Cached) -> Self::Returned {
        cached.clone()
    }
}
