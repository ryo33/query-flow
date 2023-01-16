use crate::{
    context::Ctx,
    error::QueryError,
    id::QueryId,
    query::{Query, QueryReturned},
};

pub trait CacheStorage: Default {
    /// Try to lock the query for checking invalidation.
    fn lock_for_checking_invalidation(&self, query_id: QueryId) -> Result<(), QueryError>;
    /// Get the cached data and unlock the query
    fn get_and_unlock<T: Query>(&self, query_id: QueryId) -> Result<QueryReturned<T>, QueryError>;
    fn start_query(&self, ctx: &Ctx) -> Result<(), QueryError>;
    fn remove(&mut self, id: QueryId);
}

#[derive(Debug, Default)]
pub struct DefaultCacheStorage {}

impl CacheStorage for DefaultCacheStorage {
    fn lock_for_checking_invalidation(&self, id: QueryId) {
        todo!()
    }
    fn remove(&mut self, id: QueryId) {
        todo!()
    }
}
