use std::sync::Arc;

use apollo_kernel::nbe::eval;
use apollo_kernel::{Closure, CofTerm, EvalError, Index, TermArena, TermId, Value};

#[derive(Debug, Clone)]
pub struct Equation {
    pub ty: Value,
    pub lhs: Value,
    pub rhs: Value,
    pub proof: Value,
}

pub fn path_type(arena: &mut TermArena, ty: &Value, lhs: &Value, rhs: &Value) -> Value {
    Value::Path {
        family: Closure::new(vec![ty.clone()], arena.var(Index(1))),
        left: Arc::new(lhs.clone()),
        right: Arc::new(rhs.clone()),
    }
}

struct Frame {
    env: Vec<Value>,
}

impl Frame {
    const fn new(env: Vec<Value>) -> Self {
        Self { env }
    }

    fn var(&self, arena: &mut TermArena, slot: usize, binders: u32) -> TermId {
        let len = u32::try_from(self.env.len()).unwrap_or(u32::MAX);
        let slot = u32::try_from(slot).unwrap_or(u32::MAX);
        arena.var(Index(len - 1 - slot + binders))
    }

    fn eval(&self, arena: &TermArena, term: TermId) -> Result<Value, EvalError> {
        eval(arena, &self.env, term)
    }
}

pub fn refl(arena: &mut TermArena, ty: Value, x: Value) -> Result<Equation, EvalError> {
    let frame = Frame::new(vec![x.clone()]);
    let body = frame.var(arena, 0, 1);
    let plam = arena.plam(body);
    Ok(Equation {
        ty,
        lhs: x.clone(),
        rhs: x,
        proof: frame.eval(arena, plam)?,
    })
}

pub fn sym(arena: &mut TermArena, eq: &Equation) -> Result<Equation, EvalError> {
    let frame = Frame::new(vec![
        eq.ty.clone(),
        eq.lhs.clone(),
        eq.rhs.clone(),
        eq.proof.clone(),
    ]);
    let ty = frame.var(arena, 0, 1);
    let cap = frame.var(arena, 1, 1);
    let start = frame.var(arena, 1, 2);
    let end = frame.var(arena, 2, 2);
    let path = frame.var(arena, 3, 2);
    let dim = arena.var(Index(0));
    let d0 = arena.dim_zero();
    let d1 = arena.dim_one();
    let along = arena.papp(path, start, end, dim);
    let branches = vec![(CofTerm::Eq(dim, d0), along), (CofTerm::Eq(dim, d1), start)];
    let hcom = arena.hcom(ty, d0, d1, branches, cap);
    let plam = arena.plam(hcom);
    Ok(Equation {
        ty: eq.ty.clone(),
        lhs: eq.rhs.clone(),
        rhs: eq.lhs.clone(),
        proof: frame.eval(arena, plam)?,
    })
}

pub fn trans(
    arena: &mut TermArena,
    first: &Equation,
    second: &Equation,
) -> Result<Equation, EvalError> {
    let frame = Frame::new(vec![
        first.ty.clone(),
        first.lhs.clone(),
        first.rhs.clone(),
        second.rhs.clone(),
        first.proof.clone(),
        second.proof.clone(),
    ]);
    let ty = frame.var(arena, 0, 1);
    let start_cap = frame.var(arena, 1, 1);
    let middle_cap = frame.var(arena, 2, 1);
    let first_cap = frame.var(arena, 4, 1);
    let start = frame.var(arena, 1, 2);
    let middle = frame.var(arena, 2, 2);
    let end = frame.var(arena, 3, 2);
    let second_path = frame.var(arena, 5, 2);
    let dim = arena.var(Index(0));
    let d0 = arena.dim_zero();
    let d1 = arena.dim_one();
    let cap = arena.papp(first_cap, start_cap, middle_cap, dim);
    let along = arena.papp(second_path, middle, end, dim);
    let branches = vec![(CofTerm::Eq(dim, d0), start), (CofTerm::Eq(dim, d1), along)];
    let hcom = arena.hcom(ty, d0, d1, branches, cap);
    let plam = arena.plam(hcom);
    Ok(Equation {
        ty: first.ty.clone(),
        lhs: first.lhs.clone(),
        rhs: second.rhs.clone(),
        proof: frame.eval(arena, plam)?,
    })
}

pub fn cong<F>(
    arena: &mut TermArena,
    ty: Value,
    fixed: &[Value],
    args: &[Equation],
    rebuild: F,
) -> Result<Equation, EvalError>
where
    F: Fn(&mut TermArena, &[TermId], &[TermId]) -> TermId,
{
    let mut env = fixed.to_vec();
    for arg in args {
        env.push(arg.lhs.clone());
        env.push(arg.rhs.clone());
        env.push(arg.proof.clone());
    }
    let frame = Frame::new(env);
    let base = fixed.len();
    let slots = |arena: &mut TermArena, binders: u32| -> Vec<TermId> {
        (0..base).map(|k| frame.var(arena, k, binders)).collect()
    };
    let side = |arena: &mut TermArena, offset: usize| -> Vec<TermId> {
        (0..args.len())
            .map(|k| frame.var(arena, base + 3 * k + offset, 0))
            .collect()
    };

    let fixed0 = slots(arena, 0);
    let lefts = side(arena, 0);
    let lhs_term = rebuild(arena, &fixed0, &lefts);
    let rights = side(arena, 1);
    let rhs_term = rebuild(arena, &fixed0, &rights);

    let fixed1 = slots(arena, 1);
    let i = arena.var(Index(0));
    let mut pointwise = Vec::with_capacity(args.len());
    for k in 0..args.len() {
        let start = frame.var(arena, base + 3 * k, 1);
        let end = frame.var(arena, base + 3 * k + 1, 1);
        let path = frame.var(arena, base + 3 * k + 2, 1);
        pointwise.push(arena.papp(path, start, end, i));
    }
    let body = rebuild(arena, &fixed1, &pointwise);
    let plam = arena.plam(body);
    Ok(Equation {
        ty,
        lhs: frame.eval(arena, lhs_term)?,
        rhs: frame.eval(arena, rhs_term)?,
        proof: frame.eval(arena, plam)?,
    })
}

#[cfg(test)]
mod tests {
    use apollo_kernel::nbe::{apply, eval};
    use apollo_kernel::{Ctx, DeBruijnLevel, Index, Level, Multiplicity, TermArena, Value};

    use super::{Equation, cong, path_type, refl, sym, trans};
    use crate::testing::{kernel_accepts, same};

    fn env_of(ctx: &Ctx) -> Vec<Value> {
        (0..ctx.depth())
            .map(|l| Value::var(DeBruijnLevel(l)))
            .collect()
    }

    struct Fixture {
        arena: TermArena,
        ctx: Ctx,
        ty: Value,
        first: Value,
        middle: Value,
        last: Value,
        unary: Value,
        binary: Value,
        early: Equation,
        late: Equation,
    }

    fn fixture() -> Fixture {
        let mut arena = TermArena::new();
        let mut ctx = Ctx::new();
        let ty = ctx.push(Value::Universe(Level::zero()));
        let first = ctx.push(ty.clone());
        let middle = ctx.push(ty.clone());
        let last = ctx.push(ty.clone());
        let dom = arena.var(Index(3));
        let cod_one = arena.var(Index(4));
        let cod_two = arena.var(Index(5));
        let unary_ty = arena.pi(Multiplicity::Many, dom, cod_one);
        let inner = arena.pi(Multiplicity::Many, cod_one, cod_two);
        let binary_ty = arena.pi(Multiplicity::Many, dom, inner);
        let unary_val = eval(&arena, &env_of(&ctx), unary_ty).unwrap_or(Value::Unit);
        let binary_val = eval(&arena, &env_of(&ctx), binary_ty).unwrap_or(Value::Unit);
        let unary = ctx.push(unary_val);
        let binary = ctx.push(binary_val);
        let early_ty = path_type(&mut arena, &ty, &first, &middle);
        let late_ty = path_type(&mut arena, &ty, &middle, &last);
        let early = Equation {
            ty: ty.clone(),
            lhs: first.clone(),
            rhs: middle.clone(),
            proof: ctx.push(early_ty),
        };
        let late = Equation {
            ty: ty.clone(),
            lhs: middle.clone(),
            rhs: last.clone(),
            proof: ctx.push(late_ty),
        };
        Fixture {
            arena,
            ctx,
            ty,
            first,
            middle,
            last,
            unary,
            binary,
            early,
            late,
        }
    }

    #[test]
    fn builds_kernel_checked_refl_sym_and_trans() {
        let Fixture {
            mut arena,
            mut ctx,
            ty,
            first,
            middle,
            last,
            early,
            late,
            ..
        } = fixture();

        let r = refl(&mut arena, ty.clone(), first.clone());
        assert!(r.as_ref().is_ok_and(
            |e| same(&arena, &ctx, &e.lhs, &first) && same(&arena, &ctx, &e.rhs, &first)
        ));
        assert!(r.is_ok_and(|e| kernel_accepts(&mut arena, &mut ctx, &e)));

        let s = sym(&mut arena, &early);
        assert!(s.as_ref().is_ok_and(|e| same(&arena, &ctx, &e.lhs, &middle)
            && same(&arena, &ctx, &e.rhs, &first)
            && same(&arena, &ctx, &e.ty, &ty)));
        assert!(s.is_ok_and(|e| kernel_accepts(&mut arena, &mut ctx, &e)));

        let t = trans(&mut arena, &early, &late);
        assert!(t.as_ref().is_ok_and(|e| same(&arena, &ctx, &e.lhs, &first)
            && same(&arena, &ctx, &e.rhs, &last)
            && same(&arena, &ctx, &e.ty, &ty)));
        assert!(t.is_ok_and(|e| kernel_accepts(&mut arena, &mut ctx, &e)));

        if let (Ok(back_late), Ok(back_early)) = (sym(&mut arena, &late), sym(&mut arena, &early)) {
            let back = trans(&mut arena, &back_late, &back_early);
            assert!(back.as_ref().is_ok_and(
                |e| same(&arena, &ctx, &e.lhs, &last) && same(&arena, &ctx, &e.rhs, &first)
            ));
            assert!(back.is_ok_and(|e| kernel_accepts(&mut arena, &mut ctx, &e)));
        }

        let wrong = Equation {
            ty,
            lhs: first.clone(),
            rhs: first,
            proof: early.proof.clone(),
        };
        assert!(!kernel_accepts(&mut arena, &mut ctx, &wrong));
        let bad_trans = trans(&mut arena, &late, &early);
        assert!(bad_trans.is_ok_and(|e| !kernel_accepts(&mut arena, &mut ctx, &e)));
    }

    #[test]
    fn builds_kernel_checked_unary_and_binary_congruence() {
        let Fixture {
            mut arena,
            mut ctx,
            ty,
            first,
            middle,
            last,
            unary,
            binary,
            early,
            late,
        } = fixture();

        let mapped = cong(
            &mut arena,
            ty.clone(),
            std::slice::from_ref(&unary),
            std::slice::from_ref(&early),
            |a, fixed, args| a.app(fixed[0], args[0]),
        );
        let at_first = apply(&arena, &unary, first.clone());
        let at_middle = apply(&arena, &unary, middle.clone());
        assert!(at_first.is_ok() && at_middle.is_ok());
        if let (Ok(eq), Ok(lhs), Ok(rhs)) = (&mapped, &at_first, &at_middle) {
            assert!(same(&arena, &ctx, &eq.lhs, lhs));
            assert!(same(&arena, &ctx, &eq.rhs, rhs));
        }
        assert!(mapped.is_ok_and(|e| kernel_accepts(&mut arena, &mut ctx, &e)));

        let both = cong(
            &mut arena,
            ty,
            std::slice::from_ref(&binary),
            &[early, late],
            |a, fixed, args| {
                let partial = a.app(fixed[0], args[0]);
                a.app(partial, args[1])
            },
        );
        let lhs = apply(&arena, &binary, first).and_then(|h| apply(&arena, &h, middle.clone()));
        let rhs = apply(&arena, &binary, middle).and_then(|h| apply(&arena, &h, last));
        assert!(lhs.is_ok() && rhs.is_ok());
        if let (Ok(eq), Ok(lhs), Ok(rhs)) = (&both, &lhs, &rhs) {
            assert!(same(&arena, &ctx, &eq.lhs, lhs));
            assert!(same(&arena, &ctx, &eq.rhs, rhs));
            assert!(!same(&arena, &ctx, &eq.lhs, rhs));
        }
        assert!(both.is_ok_and(|e| kernel_accepts(&mut arena, &mut ctx, &e)));
    }
}
