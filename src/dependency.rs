use std::collections::BTreeSet;

use crate::{id::CacheId, rc::CfgRc};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum Dependencies {
    Sequence(Vec<CfgRc<Dependencies>>),
    Cache {
        id: CacheId,
        deps: CfgRc<Dependencies>,
    },
    Many(BTreeSet<CfgRc<Dependencies>>),
}

impl Dependencies {
    pub fn direct_dependencies(&self) -> DirectDependencies {
        match self {
            Dependencies::Sequence(deps) => {
                let mut direct_deps = BTreeSet::new();
                for dep in deps {
                    direct_deps.extend(dep.direct_dependencies().0);
                }
                DirectDependencies(direct_deps)
            }
            Dependencies::Cache { id, .. } => DirectDependencies([*id].into_iter().collect()),
            Dependencies::Many(deps) => {
                let mut direct_deps = BTreeSet::new();
                for dep in deps {
                    direct_deps.extend(dep.direct_dependencies().0);
                }
                DirectDependencies(direct_deps)
            }
        }
    }

    pub fn new_sequence(deps: impl IntoIterator<Item = CfgRc<Dependencies>>) -> CfgRc<Self> {
        Dependencies::Sequence(deps.into_iter().collect()).into()
    }

    pub fn new_cache(id: CacheId, deps: CfgRc<Dependencies>) -> CfgRc<Self> {
        Dependencies::Cache { id, deps: deps }.into()
    }

    pub fn new_many(deps: impl IntoIterator<Item = CfgRc<Dependencies>>) -> CfgRc<Self> {
        Dependencies::Many(deps.into_iter().collect()).into()
    }
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub struct DirectDependencies(pub(crate) BTreeSet<CacheId>);

impl FromIterator<CacheId> for DirectDependencies {
    fn from_iter<T: IntoIterator<Item = CacheId>>(iter: T) -> Self {
        DirectDependencies(iter.into_iter().collect())
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        id::{QueryId, Version},
        query::Query,
    };

    use super::*;

    impl Query for () {
        type Output = ();
        type Error = ();

        fn run(&self, ctx: &mut crate::context::Ctx) -> crate::error::QueryResult<Self> {
            unimplemented!()
        }
    }

    #[test]
    fn direct_dependencies_cache() {
        let deps = Dependencies::new_cache(
            CacheId {
                query_id: QueryId::new::<()>(0),
                version: Version::new(0),
            },
            Dependencies::new_sequence(vec![
                Dependencies::new_cache(
                    CacheId {
                        query_id: QueryId::new::<()>(1),
                        version: Version::new(0),
                    },
                    Dependencies::new_sequence(vec![]),
                ),
                Dependencies::new_cache(
                    CacheId {
                        query_id: QueryId::new::<()>(2),
                        version: Version::new(0),
                    },
                    Dependencies::new_sequence(vec![]),
                ),
            ]),
        );
        assert_eq!(
            deps.direct_dependencies(),
            [CacheId {
                query_id: QueryId::new::<()>(0),
                version: Version::new(0),
            }]
            .into_iter()
            .collect()
        );
    }

    #[test]
    fn direct_dependencies_sequence() {
        let deps = Dependencies::new_sequence(vec![
            Dependencies::new_cache(
                CacheId {
                    query_id: QueryId::new::<()>(0),
                    version: Version::new(0),
                },
                Dependencies::new_sequence(vec![]),
            ),
            Dependencies::new_cache(
                CacheId {
                    query_id: QueryId::new::<()>(1),
                    version: Version::new(0),
                },
                Dependencies::new_sequence(vec![]),
            ),
        ]);
        assert_eq!(
            deps.direct_dependencies(),
            [
                CacheId {
                    query_id: QueryId::new::<()>(0),
                    version: Version::new(0),
                },
                CacheId {
                    query_id: QueryId::new::<()>(1),
                    version: Version::new(0),
                }
            ]
            .into_iter()
            .collect()
        );
    }

    #[test]
    fn direct_dependencies_many() {
        let deps = Dependencies::new_many([
            Dependencies::new_cache(
                CacheId {
                    query_id: QueryId::new::<()>(0),
                    version: Version::new(0),
                },
                Dependencies::new_sequence(vec![]),
            ),
            Dependencies::new_cache(
                CacheId {
                    query_id: QueryId::new::<()>(1),
                    version: Version::new(0),
                },
                Dependencies::new_sequence(vec![]),
            ),
        ]);
        assert_eq!(
            deps.direct_dependencies(),
            [
                CacheId {
                    query_id: QueryId::new::<()>(0),
                    version: Version::new(0),
                },
                CacheId {
                    query_id: QueryId::new::<()>(1),
                    version: Version::new(0),
                }
            ]
            .into_iter()
            .collect()
        );
    }

    #[test]
    fn direct_dependencies_recursive() {
        let deps = Dependencies::new_sequence(vec![
            Dependencies::new_sequence([Dependencies::new_sequence([Dependencies::new_cache(
                CacheId {
                    query_id: QueryId::new::<()>(0),
                    version: Version::new(0),
                },
                Dependencies::new_sequence(vec![]),
            )])]),
            Dependencies::new_many([
                Dependencies::new_sequence([Dependencies::new_cache(
                    CacheId {
                        query_id: QueryId::new::<()>(1),
                        version: Version::new(0),
                    },
                    Dependencies::new_sequence(vec![]),
                )]),
                Dependencies::new_many([Dependencies::new_cache(
                    CacheId {
                        query_id: QueryId::new::<()>(2),
                        version: Version::new(0),
                    },
                    Dependencies::new_sequence(vec![]),
                )]),
            ]),
        ]);
        assert_eq!(
            deps.direct_dependencies(),
            [
                CacheId {
                    query_id: QueryId::new::<()>(0),
                    version: Version::new(0),
                },
                CacheId {
                    query_id: QueryId::new::<()>(1),
                    version: Version::new(0),
                },
                CacheId {
                    query_id: QueryId::new::<()>(2),
                    version: Version::new(0),
                }
            ]
            .into_iter()
            .collect()
        );
    }
}
