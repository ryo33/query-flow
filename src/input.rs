use std::{any::Any, convert::Infallible, fmt::Debug, hash::Hash};

use crate::{context::Ctx, error::QueryResult, output::QueryOutput, query::Query};

pub trait Input: Debug + Hash + Any + PartialEq + Eq + Send + Sync + 'static {
    type Output: QueryOutput;
}

impl<O, I> Query for I
where
    O: QueryOutput,
    I: Input<Output = O>,
{
    type Output = Option<O>;
    type Error = Infallible;

    fn run(&self, ctx: &mut Ctx) -> QueryResult<Self> {
        // The default value
        Ok(None)
    }

    fn on_input(&self) {
        // Do nothing
    }
}
