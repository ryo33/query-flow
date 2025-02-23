use crate::{Invalidation, Pointer, RevisionPointer};

/// A trait for collecting and give strategy for invalidation propagation.
pub trait InvalidationCollector<I> {
    /// Collect invalidations.
    fn notify(
        &mut self,
        target: &Pointer<I>,
        invalidation: &Invalidation<I>,
    ) -> InvalidationPropagation;
}

/// InvalidationPropagation is a strategy for invalidation propagation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum InvalidationPropagation {
    /// Propagate invalidations to dependents.
    Propagate,
    /// Do not propagate invalidations.
    #[default]
    DoNotPropagate,
}

/// A noop implementation of InvalidationCollector.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct NoopInvalidationCollector;

impl<I> InvalidationCollector<I> for NoopInvalidationCollector {
    fn notify(&mut self, _: &Pointer<I>, _: &Invalidation<I>) -> InvalidationPropagation {
        InvalidationPropagation::DoNotPropagate
    }
}

/// A collector that propagates invalidations to dependents.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct PropagateInvalidationCollector;

impl<I> InvalidationCollector<I> for PropagateInvalidationCollector {
    fn notify(&mut self, _: &Pointer<I>, _: &Invalidation<I>) -> InvalidationPropagation {
        InvalidationPropagation::Propagate
    }
}

/// A collector that collects all invalidations into a Vec.
pub struct VecInvalidationCollector<I> {
    invalidations: Vec<Invalidation<I>>,
}

impl<I> InvalidationCollector<I> for VecInvalidationCollector<I>
where
    I: Clone,
{
    fn notify(
        &mut self,
        _: &Pointer<I>,
        invalidation: &Invalidation<I>,
    ) -> InvalidationPropagation {
        self.invalidations.push(invalidation.clone());
        InvalidationPropagation::Propagate
    }
}

/// A trait for collecting and give strategy for uninvalidation propagation.
pub trait UninvalidationCollector<I> {
    /// Notify about an uninvalidation and decide whether to propagate it.
    fn notify(
        &mut self,
        target: &Pointer<I>,
        source: &RevisionPointer<I>,
    ) -> InvalidationPropagation;
}

/// A noop implementation of UninvalidationCollector.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct NoopUninvalidationCollector;

impl<I> UninvalidationCollector<I> for NoopUninvalidationCollector {
    fn notify(&mut self, _: &Pointer<I>, _: &RevisionPointer<I>) -> InvalidationPropagation {
        InvalidationPropagation::DoNotPropagate
    }
}

/// A collector that propagates all uninvalidations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct PropagateUninvalidationCollector;

impl<I> UninvalidationCollector<I> for PropagateUninvalidationCollector {
    fn notify(&mut self, _: &Pointer<I>, _: &RevisionPointer<I>) -> InvalidationPropagation {
        InvalidationPropagation::Propagate
    }
}

/// A collector that collects all uninvalidations into a Vec.
pub struct VecUninvalidationCollector<I> {
    uninvalidations: Vec<(Pointer<I>, RevisionPointer<I>)>,
}

impl<I> UninvalidationCollector<I> for VecUninvalidationCollector<I>
where
    I: Clone,
{
    fn notify(
        &mut self,
        target: &Pointer<I>,
        source: &RevisionPointer<I>,
    ) -> InvalidationPropagation {
        self.uninvalidations.push((target.clone(), source.clone()));
        InvalidationPropagation::Propagate
    }
}
