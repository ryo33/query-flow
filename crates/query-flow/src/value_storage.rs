use crate::query::Query;

pub trait ValueStorage<Q: Query> {
    fn get(&self, key: &Q::CacheKey) -> Option<&Q::Output>;
    fn set(&mut self, key: Q::CacheKey, value: Q::Output);
}
