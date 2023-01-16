use crate::context::Ctx;

use super::Query;

impl Query for () {
    type Output = ();

    fn run(&self, _ctx: &mut Ctx) -> Self::Output {
        ()
    }
}
