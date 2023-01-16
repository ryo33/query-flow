use crate::id::DefaultIdGen;

pub trait IdGen: Default {
    fn next(&mut self) -> usize;
    fn remove(&mut self, id: usize);
    fn shrink_to_fit(&mut self);
}

impl IdGen for DefaultIdGen {
    fn next(&mut self) -> usize {
        self.next()
    }

    fn remove(&mut self, id: usize) {
        self.remove(id)
    }

    fn shrink_to_fit(&mut self) {
        self.shrink_to_fit()
    }
}
