pub mod cache_storage;
#[cfg(feature = "concurrent-storage")]
pub mod concurrent;
pub mod id_gen;
pub mod notifier;
pub mod query_registry;
pub mod state;

use std::any::Any;

use crate::{
    cache::ReturnedCache,
    context::Ctx,
    error::QueryResultReturned,
    id::{CtxId, DefaultIdGen, QueryId},
    query::{DynQuery, Query},
    rc::CfgRc,
};

use self::{
    cache_storage::{CacheStorage, DefaultCacheStorage},
    concurrent::{
        cache_storage::ConcurrentCacheStorage, id_gen::ConcurrentIdGen,
        query_registry::ConcurrentQueryRegistry, state::ConcurrentStorageState,
    },
    id_gen::IdGen,
    query_registry::{DefaultQueryRegistry, QueryRegistry},
    state::{DefaultStorageState, StorageState},
};

#[derive(Debug, Default)]
pub struct Storage<Q, C, I, S>
where
    Q: QueryRegistry,
    C: CacheStorage,
    I: IdGen,
    S: StorageState,
{
    ctx_id_gen: I,
    queries: Q,
    caches: C,
    state: S,
}

pub type DefaultStorage =
    Storage<DefaultQueryRegistry, DefaultCacheStorage, DefaultIdGen, DefaultStorageState>;

#[cfg(feature = "concurrent-storage")]
pub type ConcurrentStorage = Storage<
    ConcurrentQueryRegistry,
    ConcurrentCacheStorage,
    ConcurrentIdGen,
    ConcurrentStorageState,
>;

impl<Q, C, I, S> Storage<Q, C, I, S>
where
    Q: QueryRegistry,
    C: CacheStorage,
    I: IdGen,
    S: StorageState,
{
    pub fn query<T: Query>(&mut self, query: T) -> QueryResultReturned<T> {
        let query = CfgRc::new(query);
        let query_id = self.queries.register(query.clone());
        let mut ctx = Ctx::new(self, query_id);
        ctx.query(query)
    }
}

pub(crate) trait DynStorage {
    fn register_query(&mut self, query: CfgRc<dyn DynQuery>) -> QueryId;
    fn get_cache_to_return(&self, id: QueryId) -> Option<ReturnedCache<Box<dyn Any>>>;
    fn next_ctx_id(&mut self) -> CtxId;
    fn remove_ctx_id(&mut self, id: CtxId);
}

impl<Q, C, I, S> DynStorage for Storage<Q, C, I, S>
where
    Q: QueryRegistry,
    C: CacheStorage,
    I: IdGen,
    S: StorageState,
{
    fn register_query(&mut self, query: CfgRc<dyn DynQuery>) -> QueryId {
        // self.queries.register(query)
        todo!()
    }

    fn get_cache_to_return(&self, id: QueryId) -> Option<ReturnedCache<Box<dyn Any>>> {
        // self.caches.get_to_return(id)
        todo!()
    }

    fn next_ctx_id(&mut self) -> CtxId {
        CtxId(self.ctx_id_gen.next())
    }

    fn remove_ctx_id(&mut self, id: CtxId) {
        self.ctx_id_gen.remove(id.0)
    }
}
