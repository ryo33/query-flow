use std::{any::TypeId, collections::HashMap, hash::Hash, num::Wrapping};

use slab::Slab;

use crate::query::Query;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct QueryId {
    pub(crate) type_id: TypeId,
    pub(crate) index: usize,
}

impl QueryId {
    pub(crate) fn new<T: Query + 'static>(index: usize) -> Self {
        Self {
            type_id: TypeId::of::<T>(),
            index,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Version(pub(crate) Wrapping<usize>);

impl Version {
    pub fn new(version: usize) -> Self {
        Self(Wrapping(version))
    }

    pub fn other(&self) -> Self {
        Self(self.0 + Wrapping(1))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CtxId(pub(crate) usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CacheId {
    pub(crate) query_id: QueryId,
    pub(crate) version: Version,
}

#[derive(Debug)]
pub struct IdMap<T> {
    contents: Slab<T>,
    ids: HashMap<T, usize>,
}

impl<T> Default for IdMap<T> {
    fn default() -> Self {
        Self {
            contents: Default::default(),
            ids: Default::default(),
        }
    }
}

impl<T: Hash + Eq + Clone> IdMap<T> {
    pub fn insert(&mut self, value: T) -> usize {
        if let Some(id) = self.ids.get(&value) {
            *id
        } else {
            let id = self.contents.insert(value.clone());
            self.ids.insert(value, id);
            id
        }
    }

    pub fn get(&self, id: usize) -> Option<&T> {
        self.contents.get(id)
    }

    pub fn remove(&mut self, id: usize) -> Option<T> {
        if self.contents.contains(id) {
            let value = self.contents.remove(id);
            self.ids.remove(&value);
            Some(value)
        } else {
            None
        }
    }

    pub fn shrink_to_fit(&mut self) {
        self.contents.shrink_to_fit();
    }
}

#[derive(Debug, Default)]
pub struct DefaultIdGen {
    ids: Slab<()>,
}

impl DefaultIdGen {
    pub fn next(&mut self) -> usize {
        self.ids.insert(())
    }

    pub fn remove(&mut self, id: usize) {
        self.ids.remove(id)
    }

    pub fn shrink_to_fit(&mut self) {
        self.ids.shrink_to_fit();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn insert_new() {
        let mut map = IdMap::default();
        let id = map.insert(1);
        assert_eq!(map.get(id), Some(&1));
    }

    #[test]
    fn insert_existing() {
        let mut map = IdMap::default();
        let id = map.insert(1);
        let id2 = map.insert(1);
        assert_eq!(id, id2);
        assert_eq!(map.get(id), Some(&1));
    }

    #[test]
    fn remove() {
        let mut map = IdMap::default();
        let id = map.insert(1);
        assert_eq!(map.remove(id), Some(1));
        assert_eq!(map.get(id), None);
        assert!(map.contents.is_empty());
        assert!(map.ids.is_empty());
    }

    #[test]
    fn id_gen_next() {
        let mut gen = DefaultIdGen::default();
        assert_eq!(gen.next(), 0);
        assert_eq!(gen.next(), 1);
    }

    #[test]
    fn id_gen_remove() {
        let mut gen = DefaultIdGen::default();
        let id = gen.next();
        gen.remove(id);
        assert_eq!(gen.next(), id);
    }
}
