use std::{any::Any, fmt::Debug, hash::Hash};

use crate::output::QueryOutput;

pub trait Input: Debug + Hash + Any + PartialEq + Eq + Send + Sync + 'static {
    type Output: QueryOutput;
}
