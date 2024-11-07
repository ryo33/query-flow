use crate::error::Error;

use super::{result::QueryOutput, Query};

pub struct QueryContext {}

impl QueryContext {
    pub fn query<Q: Query>(&self, query: Q) -> Result<QueryOutput<Q>, Error> {
        todo!()
    }
}
