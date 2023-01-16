pub mod cache_storage;
pub mod id_gen;
pub mod query_registry;
pub mod state;

use super::{
    cache_storage::CacheStorage, id_gen::IdGen, query_registry::QueryRegistry, state::StorageState,
    Storage,
};

pub trait Concurrent: Clone {}

impl<Q, C, I, S> Clone for Storage<Q, C, I, S>
where
    Q: QueryRegistry + Concurrent,
    C: CacheStorage + Concurrent,
    I: IdGen + Concurrent,
    S: StorageState + Concurrent,
{
    fn clone(&self) -> Self {
        Self {
            ctx_id_gen: self.ctx_id_gen.clone(),
            queries: self.queries.clone(),
            caches: self.caches.clone(),
            state: self.state.clone(),
        }
    }
}
