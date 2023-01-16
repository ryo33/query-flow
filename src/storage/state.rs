use crate::event::Event;

pub trait StorageState {
    fn push_events(&mut self, events: Vec<Event>);
}

pub struct DefaultStorageState {
    // TODO
}

impl StorageState for DefaultStorageState {
    fn push_events(&mut self, events: Vec<Event>) {
        todo!()
    }
}
