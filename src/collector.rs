use crate::{Invalidation, Pointer, RevisionPointer};

/// A trait for collecting and give strategy for invalidation propagation.
pub trait InvalidationCollector {
    /// Collect invalidations.
    fn notify(&mut self, target: Pointer, invalidation: Invalidation) -> InvalidationPropagation;
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

impl InvalidationCollector for NoopInvalidationCollector {
    fn notify(&mut self, _: Pointer, _: Invalidation) -> InvalidationPropagation {
        InvalidationPropagation::DoNotPropagate
    }
}

/// A collector that propagates invalidations to dependents.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct PropagateInvalidationCollector;

impl InvalidationCollector for PropagateInvalidationCollector {
    fn notify(&mut self, _: Pointer, _: Invalidation) -> InvalidationPropagation {
        InvalidationPropagation::Propagate
    }
}

/// A collector that collects all invalidations into a Vec.
pub struct VecInvalidationCollector {
    invalidations: Vec<Invalidation>,
}

impl InvalidationCollector for VecInvalidationCollector {
    fn notify(&mut self, _: Pointer, invalidation: Invalidation) -> InvalidationPropagation {
        self.invalidations.push(invalidation);
        InvalidationPropagation::Propagate
    }
}

/// A trait for collecting and give strategy for uninvalidation propagation.
pub trait UninvalidationCollector {
    /// Notify about an uninvalidation and decide whether to propagate it.
    fn notify(&mut self, target: Pointer, source: RevisionPointer) -> InvalidationPropagation;
}

/// A noop implementation of UninvalidationCollector.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct NoopUninvalidationCollector;

impl UninvalidationCollector for NoopUninvalidationCollector {
    fn notify(&mut self, _: Pointer, _: RevisionPointer) -> InvalidationPropagation {
        InvalidationPropagation::DoNotPropagate
    }
}

/// A collector that propagates all uninvalidations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct PropagateUninvalidationCollector;

impl UninvalidationCollector for PropagateUninvalidationCollector {
    fn notify(&mut self, _: Pointer, _: RevisionPointer) -> InvalidationPropagation {
        InvalidationPropagation::Propagate
    }
}

/// A collector that collects all uninvalidations into a Vec.
pub struct VecUninvalidationCollector {
    uninvalidations: Vec<(Pointer, RevisionPointer)>,
}

impl UninvalidationCollector for VecUninvalidationCollector {
    fn notify(&mut self, target: Pointer, source: RevisionPointer) -> InvalidationPropagation {
        self.uninvalidations.push((target, source));
        InvalidationPropagation::Propagate
    }
}
