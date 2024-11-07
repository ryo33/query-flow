use std::sync::Arc;

use crate::{error::Error, version::Version};

use super::Query;

pub type QueryResult<Q> = Result<QueryOutput<Q>, Error>;

pub struct QueryOutput<Q: Query> {
    value: Arc<Q::Output>,
    version: Version,
}

impl<Q: Query> QueryOutput<Q> {
    pub fn version(&self) -> Version {
        self.version
    }
}

impl<Q: Query> std::ops::Deref for QueryOutput<Q> {
    type Target = Q::Output;

    fn deref(&self) -> &Self::Target {
        &self.value
    }
}
