use std::{any::TypeId, collections::BTreeMap, sync::Arc};

use crate::{
    id::{IdMap, QueryId},
    query::{DynQuery, Query},
    rc::CfgRc,
};

pub trait QueryRegistry: Default {
    fn register<Q: Query>(&mut self, query: CfgRc<Q>) -> QueryId;
    fn get<Q: Query>(&self, id: QueryId) -> Option<CfgRc<Q>> {
        self.dyn_get(id)
            .map(|q| CfgRc::downcast(q.as_rc_any()).unwrap())
    }
    fn dyn_get(&self, id: QueryId) -> Option<CfgRc<dyn DynQuery>>;
    fn remove(&mut self, id: QueryId);
}

#[derive(Default)]
pub struct DefaultQueryRegistry {
    queries: BTreeMap<TypeId, IdMap<CfgRc<dyn DynQuery>>>,
}

impl QueryRegistry for DefaultQueryRegistry {
    fn register<Q: Query>(&mut self, query: CfgRc<Q>) -> QueryId {
        let queries = self
            .queries
            .entry(TypeId::of::<Q>())
            .or_insert_with(Default::default);
        let index = queries.insert(query);
        QueryId::new::<Q>(index)
    }
    fn dyn_get(&self, id: QueryId) -> Option<CfgRc<dyn DynQuery>> {
        self.queries
            .get(&id.type_id)
            .and_then(|queries| queries.get(id.index))
            .cloned()
    }
    fn remove(&mut self, id: QueryId) {
        if let Some(removed) = self
            .queries
            .get_mut(&id.type_id)
            .and_then(|queries| queries.remove(id.index))
        {
            debug_assert_eq!(Arc::strong_count(&removed), 1);
        }
    }
}
