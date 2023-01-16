use crate::{dependency::Dependencies, id::CacheId, rc::CfgRc};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum Event {
    UpdateCache {
        cache_id: CacheId,
        deps: CfgRc<Dependencies>,
    },
}
