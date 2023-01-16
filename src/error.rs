use convertable::ConvertFrom;
use thiserror::Error;

use crate::{
    async_query::AsyncQuery, context::Ctx, id::QueryId, output::QueryOutput, query::Query,
};

#[derive(Error, Debug)]
pub enum QueryError {}

#[derive(Error, Debug)]
pub enum QueryFlowError<T> {
    #[error(transparent)]
    QueryError(#[from] QueryError),
    #[error(transparent)]
    UserError(T),
}

// TODO: Define a struct instead of this type and implement `Try` trait if `try_trait_v2` is stabilized.
pub(crate) type QueryFlowResult<T, E> = Result<T, QueryFlowError<E>>;

pub type QueryResult<T: Query> = QueryFlowResult<T::Output, T::Error>;
pub type AsyncQueryResult<T: AsyncQuery> = QueryFlowResult<T::Output, T::Error>;
pub type QueryResultReturned<T: Query> =
    QueryFlowResult<<T::Output as QueryOutput>::Returned, T::Error>;

#[derive(Error, Debug)]
pub struct WithSource<E, S> {
    error: E,
    #[source]
    source: S,
}

#[derive(Error, Debug)]
pub struct WithQueryId<E> {
    error: E,
    query_id: QueryId,
}

pub trait QueryFlowResultTrait<T, E>: ResultExt<T, QueryFlowError<E>> + Sized {
    fn with_query_id(self, ctx: &Ctx) -> QueryFlowResult<T, WithQueryId<E>>;
    fn map_user_err<E2>(self, f: impl FnOnce(E) -> E2) -> QueryFlowResult<T, E2>;
    fn err_into<E2>(self) -> QueryFlowResult<T, E2>
    where
        E: Into<E2>,
    {
        self.map_user_err(|error| error.into())
    }
}

impl<T, E> QueryFlowResultTrait<T, E> for QueryFlowResult<T, E> {
    fn with_query_id(self, ctx: &Ctx) -> QueryFlowResult<T, WithQueryId<E>> {
        self.map_user_err(|error| WithQueryId {
            error,
            query_id: ctx.query_id(),
        })
    }

    fn map_user_err<E2>(self, f: impl FnOnce(E) -> E2) -> QueryFlowResult<T, E2> {
        self.map_err(|error| match error {
            QueryFlowError::UserError(error) => QueryFlowError::UserError(f(error)),
            QueryFlowError::QueryError(error) => QueryFlowError::QueryError(error),
        })
    }
}

pub trait ResultExt<T, E> {
    fn into_qf<E2>(self) -> QueryFlowResult<T, E2>
    where
        E: Into<E2>;
}

impl<T, E> ResultExt<T, E> for Result<T, E> {
    fn into_qf<E2>(self) -> QueryFlowResult<T, E2>
    where
        E: Into<E2>,
    {
        self.map_err(|error| QueryFlowError::UserError(error.into()))
    }
}

impl<F: Into<I>, I> ConvertFrom<QueryFlowError<F>> for QueryFlowError<I> {
    fn convert_from(error: QueryFlowError<F>) -> Self {
        match error {
            QueryFlowError::QueryError(error) => QueryFlowError::QueryError(error),
            QueryFlowError::UserError(error) => QueryFlowError::UserError(error.into()),
        }
    }
}
