use std::sync::Arc;

use crate::{
    async_query::AsyncQuery,
    cache::InvalidationReason,
    dependency::Dependencies,
    error::{QueryFlowResult, QueryResultReturned},
    id::{CtxId, QueryId},
    output::QueryOutput,
    query::{Query, QueryMany},
    rc::CfgRc,
    storage::DynStorage,
};

pub struct Ctx<'a> {
    query_id: QueryId,
    root_id: CtxId,
    storage: &'a mut dyn DynStorage,
    deps: Vec<CfgRc<Dependencies>>,
}

impl Ctx<'_> {
    pub(crate) fn new<'a>(storage: &'a mut dyn DynStorage, query_id: QueryId) -> Ctx<'a> {
        Ctx {
            query_id,
            root_id: storage.next_ctx_id(),
            storage,
            deps: Default::default(),
        }
    }

    pub(crate) fn new_child(&mut self, query_id: QueryId) -> Ctx<'_> {
        Ctx {
            query_id: self.query_id,
            root_id: self.root_id.clone(),
            storage: self.storage,
            deps: Default::default(),
        }
    }

    pub fn query_id(&self) -> QueryId {
        self.query_id
    }

    fn into_sequence(self) -> CfgRc<Dependencies> {
        Dependencies::new_sequence(self.deps)
    }

    fn into_many(self) -> CfgRc<Dependencies> {
        Dependencies::new_many(self.deps)
    }

    pub fn query<T: Query>(&mut self, query: Arc<T>) -> QueryResultReturned<T> {
        let output = if let Some(cache) = self.storage.get_cache_to_return(self.query_id) {
            self.deps.push(cache.deps.clone());
            T::Output::cached_into_returned(
                cache
                    .ret
                    .downcast_ref::<<<T as Query>::Output as QueryOutput>::Cached>()
                    .unwrap(),
            )
        };
        Ok(output)
    }

    pub fn query_because<T: Query>(
        &mut self,
        query: Arc<T>,
        because: InvalidationReason,
    ) -> QueryResultReturned<T> {
        let mut ctx = self.new_child(self.query_id);
        let output = query.run(&mut ctx)?;
        let deps = ctx.into_sequence();
        self.deps.push(deps);
        Ok(output.into_returned())
    }

    pub fn query_many<T: QueryMany>(&mut self, query: T) -> QueryFlowResult<T::Output, T::Error> {
        let mut ctx = self.new_child(self.query_id);
        let ret = query.run(&mut ctx);
        let deps = ctx.into_many();
        self.deps.push(deps);
        ret
    }

    // This must not be `async` because we need to lock the storage before the first polling
    pub fn async_query<O, Q>(&mut self, query: Q) -> O
    where
        O: QueryOutput,
        Q: AsyncQuery<Output = O>,
    {
        todo!()
    }
}
