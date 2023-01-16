mod tuple;

use std::{any::Any, fmt::Debug, hash::Hash};

use crate::{
    context::Ctx,
    error::{QueryFlowResult, QueryResult},
    output::{OutputReturned, QueryOutput},
    rc::CfgRc,
};

pub trait Query: Debug + Hash + Any + PartialEq + Eq + Send + Sync + 'static {
    /// The output type of the query.
    type Output: QueryOutput;
    // TODO: Use Infallible as default when it's stabilized
    type Error: Debug + Send + Sync + 'static;

    fn run(&self, ctx: &mut Ctx) -> QueryResult<Self>;

    /// This method is called when an input is given to the query.
    fn on_input(&self) {
        panic!("input not allowed for this query");
    }
}

pub type QueryReturned<T: Query> = OutputReturned<T::Output>;

pub trait QueryMany: Sized {
    type Output;
    type Error: Debug + Send + Sync + 'static;

    fn run(&self, ctx: &mut Ctx) -> QueryFlowResult<Self::Output, Self::Error>;
}

pub trait DynQuery: Any + Send + Sync + 'static {
    #[doc(hidden)]
    fn dyn_hash(&self, state: &mut dyn std::hash::Hasher);
    #[doc(hidden)]
    fn dyn_eq(&self, other: &dyn DynQuery) -> bool;
    #[doc(hidden)]
    fn dyn_fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result;
    #[doc(hidden)]
    fn as_any(&self) -> &dyn Any;
    #[doc(hidden)]
    fn as_rc_any(self: CfgRc<Self>) -> CfgRc<dyn Any + Send + Sync + 'static>;
}

impl<O, Q> DynQuery for Q
where
    O: QueryOutput,
    Q: Query<Output = O>,
{
    fn dyn_hash(&self, mut state: &mut dyn std::hash::Hasher) {
        self.hash(&mut state);
    }

    fn dyn_eq(&self, other: &dyn DynQuery) -> bool {
        if let Some(other) = other.as_any().downcast_ref::<Self>() {
            self == other
        } else {
            false
        }
    }

    fn as_any(&self) -> &dyn Any {
        self
    }

    fn as_rc_any(self: CfgRc<Self>) -> CfgRc<dyn Any + Send + Sync + 'static> {
        self
    }

    fn dyn_fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.fmt(f)
    }
}

impl PartialEq for dyn DynQuery {
    fn eq(&self, other: &Self) -> bool {
        self.dyn_eq(other)
    }
}

impl PartialEq<&Self> for dyn DynQuery {
    fn eq(&self, other: &&Self) -> bool {
        self.dyn_eq(*other)
    }
}

impl Eq for dyn DynQuery {}

impl Hash for dyn DynQuery {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.dyn_hash(state);
    }
}

impl Debug for dyn DynQuery {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.dyn_fmt(f)
    }
}

#[cfg(test)]
mod tests {
    use std::{collections::hash_map::DefaultHasher, convert::Infallible, hash::Hasher};

    use super::*;

    #[test]
    fn test_hash_same_value() {
        #[derive(PartialEq, Eq, Hash, Debug)]
        pub struct A(usize);
        impl Query for A {
            type Output = ();
            type Error = Infallible;
            fn run(&self, _ctx: &mut Ctx) -> QueryResult<Self> {
                unimplemented!()
            }
        }

        let a: Box<dyn DynQuery> = Box::new(A(1));
        let b: Box<dyn DynQuery> = Box::new(A(1));

        let mut hasher_a = DefaultHasher::new();
        let mut hasher_b = DefaultHasher::new();

        Hash::hash(&a, &mut hasher_a);
        Hash::hash(&b, &mut hasher_b);

        assert_eq!(hasher_a.finish(), hasher_b.finish());
    }

    #[test]
    fn test_hash_not_same_value() {
        #[derive(PartialEq, Eq, Hash, Debug)]
        pub struct A(usize);
        impl Query for A {
            type Output = ();
            type Error = Infallible;
            fn run(&self, _ctx: &mut Ctx) -> QueryResult<Self> {
                unimplemented!()
            }
        }

        let a: Box<dyn DynQuery> = Box::new(A(1));
        let b: Box<dyn DynQuery> = Box::new(A(2));

        let mut hasher_a = DefaultHasher::new();
        let mut hasher_b = DefaultHasher::new();

        Hash::hash(&a, &mut hasher_a);
        Hash::hash(&b, &mut hasher_b);

        assert_ne!(hasher_a.finish(), hasher_b.finish());
    }

    #[test]
    fn test_eq_same_value() {
        #[derive(PartialEq, Eq, Hash, Debug)]
        pub struct A(usize);
        impl Query for A {
            type Output = ();
            type Error = Infallible;
            fn run(&self, _ctx: &mut Ctx) -> QueryResult<Self> {
                unimplemented!()
            }
        }

        let a: Box<dyn DynQuery> = Box::new(A(1));
        let b: Box<dyn DynQuery> = Box::new(A(1));

        assert_eq!(&a, &b);
    }

    #[test]
    fn test_eq_different_value() {
        #[derive(PartialEq, Eq, Hash, Debug)]
        pub struct A(usize);
        impl Query for A {
            type Output = ();
            type Error = Infallible;
            fn run(&self, _ctx: &mut Ctx) -> QueryResult<Self> {
                unimplemented!()
            }
        }

        let a: Box<dyn DynQuery> = Box::new(A(1));
        let b: Box<dyn DynQuery> = Box::new(A(2));

        assert_ne!(&a, &b);
    }

    #[test]
    fn test_eq_different_type() {
        #[derive(PartialEq, Eq, Hash, Debug)]
        pub struct A(usize);
        impl Query for A {
            type Output = ();
            type Error = Infallible;
            fn run(&self, _ctx: &mut Ctx) -> QueryResult<Self> {
                unimplemented!()
            }
        }

        #[derive(PartialEq, Eq, Hash, Debug)]
        pub struct B(usize);
        impl Query for B {
            type Output = ();
            type Error = Infallible;
            fn run(&self, _ctx: &mut Ctx) -> QueryResult<Self> {
                unimplemented!()
            }
        }

        let a: Box<dyn DynQuery> = Box::new(A(1));
        let b: Box<dyn DynQuery> = Box::new(B(1));

        assert_ne!(&a, &b);
    }
}
