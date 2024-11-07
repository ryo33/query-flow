pub mod context;
pub mod result;

use context::QueryContext;

use crate::{error::Error, key::Key};

pub trait Query {
    type CacheKey: Key;
    type Output;

    /// Get the cache key for the query.
    fn cache_key(&self) -> Self::CacheKey;

    /// Query the output of the query.
    fn query(&self, ctx: &mut QueryContext) -> Result<Self::Output, Error>;

    /// Whether the query should never be cached.
    ///
    /// If true, this query will always be re-calculated. Even if not cached, downstream queries can be cached.
    fn never_cache(&self) -> bool {
        false
    }
}
