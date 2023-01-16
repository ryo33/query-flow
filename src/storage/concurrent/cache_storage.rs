use std::sync::Arc;

use parking_lot::RwLock;

use crate::{
    id::QueryId,
    storage::cache_storage::{CacheStorage, DefaultCacheStorage},
};

use super::Concurrent;

#[derive(Debug, Default, Clone)]
pub struct ConcurrentCacheStorage {
    inner: Arc<RwLock<DefaultCacheStorage>>,
}

impl CacheStorage for ConcurrentCacheStorage {
    fn remove(&mut self, id: QueryId) {
        todo!()
    }
}

impl Concurrent for ConcurrentCacheStorage {}
