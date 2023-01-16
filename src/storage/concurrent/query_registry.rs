use std::sync::Arc;

use parking_lot::RwLock;

use crate::{
    id::QueryId,
    query::{DynQuery, Query},
    rc::CfgRc,
    storage::query_registry::{DefaultQueryRegistry, QueryRegistry},
};

#[derive(Clone, Default)]
pub struct ConcurrentQueryRegistry {
    // TODO: Use Arc<RwLock<BTreeMap<TypeId, IdMap<CfgRc<dyn DynQuery>>>>> instead for more efficient
    inner: Arc<RwLock<DefaultQueryRegistry>>,
}

impl QueryRegistry for ConcurrentQueryRegistry {
    fn register<Q: Query>(&mut self, query: CfgRc<Q>) -> QueryId {
        self.inner.write().register(query)
    }
    fn dyn_get(&self, id: QueryId) -> Option<CfgRc<dyn DynQuery>> {
        self.inner.read().dyn_get(id)
    }
    fn remove(&mut self, id: QueryId) {
        self.inner.write().remove(id)
    }
}

#[cfg(test)]
mod tests {
    use crate::input::Input;

    use super::*;

    #[derive(PartialEq, Eq, Hash, Debug)]
    struct TestInput(u8);
    impl Input for TestInput {
        type Output = ();
    }

    fn rc(n: u8) -> CfgRc<TestInput> {
        CfgRc::new(TestInput(n))
    }

    #[test]
    fn test_register_new() {
        let mut registry = ConcurrentQueryRegistry::default();
        assert_eq!(registry.register(rc(0)), QueryId::new::<TestInput>(0));
        assert_eq!(registry.register(rc(1)), QueryId::new::<TestInput>(1));
    }

    #[test]
    fn test_register_same() {
        let mut registry = ConcurrentQueryRegistry::default();
        assert_eq!(registry.register(rc(0)), QueryId::new::<TestInput>(0));
        assert_eq!(registry.register(rc(0)), QueryId::new::<TestInput>(0));
    }

    #[test]
    fn test_get_some() {
        let mut registry = ConcurrentQueryRegistry::default();
        let id = registry.register(rc(0));
        assert_eq!(registry.get(id), Some(rc(0)));
    }

    #[test]
    fn test_get_none() {
        let registry = ConcurrentQueryRegistry::default();
        assert_eq!(
            registry.get::<TestInput>(QueryId::new::<TestInput>(0)),
            None
        );
    }

    #[test]
    fn test_get_none_registered() {
        let mut registry = ConcurrentQueryRegistry::default();
        let _ = registry.register(rc(0));
        assert_eq!(
            registry.get::<TestInput>(QueryId::new::<TestInput>(1)),
            None
        );
    }

    #[test]
    fn test_remove_some() {
        let mut registry = ConcurrentQueryRegistry::default();
        let id = registry.register(rc(0));
        registry.remove(id);
        assert_eq!(registry.get::<TestInput>(id), None);
    }

    #[test]
    fn test_remove_none() {
        let mut registry = ConcurrentQueryRegistry::default();
        registry.remove(QueryId::new::<TestInput>(0));
    }

    #[test]
    fn test_remove_none_registered() {
        let mut registry = ConcurrentQueryRegistry::default();
        let _ = registry.register(rc(0));
        registry.remove(QueryId::new::<TestInput>(1));
    }

    #[test]
    #[should_panic]
    fn assert_arc_is_not_used() {
        let mut registry = ConcurrentQueryRegistry::default();
        let id = registry.register(rc(0));
        let _query = registry.get::<TestInput>(id).unwrap();
        registry.remove(id);
    }
}
