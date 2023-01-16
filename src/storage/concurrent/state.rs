use std::sync::Arc;

use parking_lot::RwLock;

use crate::{
    event::Event,
    storage::state::{DefaultStorageState, StorageState},
};

pub struct ConcurrentStorageState {
    inner: Arc<RwLock<DefaultStorageState>>,
}

impl StorageState for ConcurrentStorageState {
    fn push_events(&mut self, events: Vec<Event>) {
        self.inner.write().push_events(events)
    }
}
