use apollo_kernel::nbe::{conv, quote};
use apollo_kernel::{Ctx, Multiplicity, TermArena, Value, check};

use crate::proof::{Equation, path_type};

pub fn kernel_accepts(arena: &mut TermArena, ctx: &mut Ctx, eq: &Equation) -> bool {
    let goal = path_type(arena, &eq.ty, &eq.lhs, &eq.rhs);
    quote(arena, ctx.depth(), &eq.proof)
        .is_ok_and(|term| check(arena, ctx, Multiplicity::Zero, term, &goal).is_ok())
}

#[must_use]
pub fn same(arena: &TermArena, ctx: &Ctx, lhs: &Value, rhs: &Value) -> bool {
    conv(arena, ctx.depth(), lhs, rhs) == Ok(true)
}
