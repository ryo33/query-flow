use std::sync::Arc;

use parking_lot::Mutex;

use crate::{id::DefaultIdGen, storage::id_gen::IdGen};

#[derive(Debug, Default, Clone)]
pub struct ConcurrentIdGen {
    inner: Arc<Mutex<DefaultIdGen>>,
}

impl IdGen for ConcurrentIdGen {
    fn next(&mut self) -> usize {
        self.inner.lock().next()
    }

    fn remove(&mut self, id: usize) {
        self.inner.lock().remove(id)
    }

    fn shrink_to_fit(&mut self) {
        self.inner.lock().shrink_to_fit()
    }
}
