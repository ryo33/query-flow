use std::{any::Any, fmt::Debug, hash::Hash};

use crate::{context::Ctx, error::AsyncQueryResult, input::Input, output::QueryOutput};

#[async_trait::async_trait]
pub trait AsyncQuery: Debug + Hash + Any + PartialEq + Eq + Sized + Send + Sync + 'static {
    type Output: QueryOutput;
    // TODO: Use Infallible as default when it's stabilized
    type Error: Debug + Send + Sync + 'static;

    async fn run(&self, ctx: &mut Ctx) -> AsyncQueryResult<Self>;

    fn ready(self) -> Ready<Self> {
        Ready(self)
    }
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub struct Ready<T: AsyncQuery>(pub(crate) T);

impl<O: QueryOutput, Q: AsyncQuery<Output = O>> Input for Ready<Q> {
    type Output = O;
}
