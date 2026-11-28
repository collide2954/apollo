use std::sync::Arc;

use apollo_kernel::nbe::{apply, eval, quote};
use apollo_kernel::{DeBruijnLevel, EvalError, Index, Multiplicity, TermArena, TermId, Value};

use crate::add_term;
use crate::proof::{Equation, cong, path_type, refl, sym, trans};

pub fn add_val(arena: &mut TermArena, lhs: &Value, rhs: &Value) -> Result<Value, EvalError> {
    let l = arena.var(Index(1));
    let r = arena.var(Index(0));
    let sum = add_term(arena, l, r);
    eval(arena, &[lhs.clone(), rhs.clone()], sum)
}

#[must_use]
pub fn succ_val(value: &Value) -> Value {
    Value::Succ(Arc::new(value.clone()))
}

pub fn cong_succ(arena: &mut TermArena, eq: &Equation) -> Result<Equation, EvalError> {
    cong(
        arena,
        Value::Nat,
        &[],
        std::slice::from_ref(eq),
        |a, _, args| a.succ(args[0]),
    )
}

pub fn cong_add(
    arena: &mut TermArena,
    lhs: &Equation,
    rhs: &Equation,
) -> Result<Equation, EvalError> {
    cong(
        arena,
        Value::Nat,
        &[],
        &[lhs.clone(), rhs.clone()],
        |a, _, args| add_term(a, args[0], args[1]),
    )
}

type Sides = (Value, Value);
type Statement = fn(&mut TermArena, &Value, &[Value]) -> Result<Sides, EvalError>;
type Base<'a> = &'a dyn Fn(&mut TermArena, &[Value]) -> Result<Equation, EvalError>;
type Step<'a> =
    &'a dyn Fn(&mut TermArena, &Value, &Equation, &[Value]) -> Result<Equation, EvalError>;

fn zero_r_sides(arena: &mut TermArena, x: &Value, _: &[Value]) -> Result<Sides, EvalError> {
    Ok((add_val(arena, x, &Value::Zero)?, x.clone()))
}

fn succ_r_sides(arena: &mut TermArena, x: &Value, rest: &[Value]) -> Result<Sides, EvalError> {
    let lhs = add_val(arena, x, &succ_val(&rest[0]))?;
    let rhs = succ_val(&add_val(arena, x, &rest[0])?);
    Ok((lhs, rhs))
}

fn assoc_sides(arena: &mut TermArena, x: &Value, rest: &[Value]) -> Result<Sides, EvalError> {
    let xy = add_val(arena, x, &rest[0])?;
    let yz = add_val(arena, &rest[0], &rest[1])?;
    Ok((add_val(arena, &xy, &rest[1])?, add_val(arena, x, &yz)?))
}

fn comm_sides(arena: &mut TermArena, x: &Value, rest: &[Value]) -> Result<Sides, EvalError> {
    Ok((add_val(arena, x, &rest[0])?, add_val(arena, &rest[0], x)?))
}

fn induction(
    arena: &mut TermArena,
    arity: u32,
    statement: Statement,
    base: Base<'_>,
    step: Step<'_>,
) -> Result<TermId, EvalError> {
    let vars: Vec<Value> = (0..arity).map(|l| Value::var(DeBruijnLevel(l))).collect();
    let rest = &vars[1..];
    let k = Value::var(DeBruijnLevel(arity));
    let (ml, mr) = statement(arena, &k, rest)?;
    let motive_val = path_type(arena, &Value::Nat, &ml, &mr);
    let motive = quote(arena, arity + 1, &motive_val)?;
    let base_eq = base(arena, rest)?;
    let base_term = quote(arena, arity, &base_eq.proof)?;
    let ih = Equation {
        ty: Value::Nat,
        lhs: ml,
        rhs: mr,
        proof: Value::var(DeBruijnLevel(arity + 1)),
    };
    let step_eq = step(arena, &k, &ih, rest)?;
    let step_term = quote(arena, arity + 2, &step_eq.proof)?;
    let scrut = arena.var(Index(arity - 1));
    let mut body = arena.nat_elim(motive, base_term, step_term, scrut);

    let (tl, tr) = statement(arena, &vars[0], rest)?;
    let ty_val = path_type(arena, &Value::Nat, &tl, &tr);
    let mut ty = quote(arena, arity, &ty_val)?;
    let nat = arena.nat();
    for _ in 0..arity {
        body = arena.lam(Multiplicity::Zero, body);
        ty = arena.pi(Multiplicity::Zero, nat, ty);
    }
    Ok(arena.ann(body, ty))
}

fn instance(
    arena: &mut TermArena,
    lemma: TermId,
    statement: Statement,
    args: &[Value],
) -> Result<Equation, EvalError> {
    let mut proof = eval(arena, &[], lemma)?;
    for arg in args {
        proof = apply(arena, &proof, arg.clone())?;
    }
    let (lhs, rhs) = statement(arena, &args[0], &args[1..])?;
    Ok(Equation {
        ty: Value::Nat,
        lhs,
        rhs,
        proof,
    })
}

#[derive(Debug, Clone, Copy)]
pub struct NatLemmas {
    zero_r: TermId,
    succ_r: TermId,
    assoc: TermId,
    comm: TermId,
}

impl NatLemmas {
    pub fn build(arena: &mut TermArena) -> Result<Self, EvalError> {
        let zero_r = induction(
            arena,
            1,
            zero_r_sides,
            &|a, _| refl(a, Value::Nat, Value::Zero),
            &|a, _, ih, _| cong_succ(a, ih),
        )?;
        let succ_r = induction(
            arena,
            2,
            succ_r_sides,
            &|a, rest| refl(a, Value::Nat, succ_val(&rest[0])),
            &|a, _, ih, _| cong_succ(a, ih),
        )?;
        let assoc = induction(
            arena,
            3,
            assoc_sides,
            &|a, rest| {
                let yz = add_val(a, &rest[0], &rest[1])?;
                refl(a, Value::Nat, yz)
            },
            &|a, _, ih, _| cong_succ(a, ih),
        )?;
        let comm = induction(
            arena,
            2,
            comm_sides,
            &|a, rest| {
                let eq = instance(a, zero_r, zero_r_sides, &rest[..1])?;
                sym(a, &eq)
            },
            &|a, k, ih, rest| {
                let lifted = cong_succ(a, ih)?;
                let shift = instance(a, succ_r, succ_r_sides, &[rest[0].clone(), k.clone()])?;
                let back = sym(a, &shift)?;
                trans(a, &lifted, &back)
            },
        )?;
        Ok(Self {
            zero_r,
            succ_r,
            assoc,
            comm,
        })
    }

    pub fn zero_r(&self, arena: &mut TermArena, x: &Value) -> Result<Equation, EvalError> {
        instance(arena, self.zero_r, zero_r_sides, std::slice::from_ref(x))
    }

    pub fn succ_r(
        &self,
        arena: &mut TermArena,
        x: &Value,
        y: &Value,
    ) -> Result<Equation, EvalError> {
        instance(arena, self.succ_r, succ_r_sides, &[x.clone(), y.clone()])
    }

    pub fn assoc(
        &self,
        arena: &mut TermArena,
        x: &Value,
        y: &Value,
        z: &Value,
    ) -> Result<Equation, EvalError> {
        instance(
            arena,
            self.assoc,
            assoc_sides,
            &[x.clone(), y.clone(), z.clone()],
        )
    }

    pub fn comm(&self, arena: &mut TermArena, x: &Value, y: &Value) -> Result<Equation, EvalError> {
        instance(arena, self.comm, comm_sides, &[x.clone(), y.clone()])
    }

    pub fn left_comm(
        &self,
        arena: &mut TermArena,
        x: &Value,
        y: &Value,
        z: &Value,
    ) -> Result<Equation, EvalError> {
        let assoc_xy = self.assoc(arena, x, y, z)?;
        let regroup = sym(arena, &assoc_xy)?;
        let swap = self.comm(arena, x, y)?;
        let keep = refl(arena, Value::Nat, z.clone())?;
        let swapped = cong_add(arena, &swap, &keep)?;
        let assoc_yx = self.assoc(arena, y, x, z)?;
        let first = trans(arena, &regroup, &swapped)?;
        trans(arena, &first, &assoc_yx)
    }
}

#[cfg(test)]
mod tests {
    use apollo_kernel::{Ctx, TermArena, Value, infer_closed};

    use super::{NatLemmas, add_val, succ_val};
    use crate::proof::Equation;
    use crate::testing::{kernel_accepts, same};

    fn nat_ctx(count: u32) -> (Ctx, Vec<Value>) {
        let mut ctx = Ctx::new();
        let vars = (0..count).map(|_| ctx.push(Value::Nat)).collect();
        (ctx, vars)
    }

    fn holds(
        arena: &mut TermArena,
        ctx: &mut Ctx,
        eq: &Equation,
        lhs: &Value,
        rhs: &Value,
    ) -> bool {
        same(arena, ctx, &eq.lhs, lhs)
            && same(arena, ctx, &eq.rhs, rhs)
            && kernel_accepts(arena, ctx, eq)
    }

    #[test]
    fn builds_closed_kernel_checked_addition_lemmas() {
        let mut arena = TermArena::new();
        let lemmas = NatLemmas::build(&mut arena);
        assert!(
            lemmas.is_ok(),
            "lemma construction failed: {:?}",
            lemmas.err()
        );
        let Ok(lemmas) = lemmas else {
            return;
        };
        for lemma in [lemmas.zero_r, lemmas.succ_r, lemmas.assoc, lemmas.comm] {
            let ty = infer_closed(&arena, lemma);
            assert!(ty.is_ok(), "kernel rejected lemma: {:?}", ty.err());
        }
        assert_ne!(lemmas.zero_r, lemmas.succ_r);
        assert_ne!(lemmas.assoc, lemmas.comm);
    }

    #[test]
    fn instantiates_lemmas_at_open_terms_with_exact_sides() {
        let mut arena = TermArena::new();
        let Ok(lemmas) = NatLemmas::build(&mut arena) else {
            return;
        };
        let (mut ctx, vars) = nat_ctx(3);
        let (x, y, z) = (&vars[0], &vars[1], &vars[2]);
        let sum = |arena: &mut TermArena, a: &Value, b: &Value| {
            add_val(arena, a, b).unwrap_or(Value::Unit)
        };

        let eq = lemmas.zero_r(&mut arena, x);
        let lhs = sum(&mut arena, x, &Value::Zero);
        assert!(eq.is_ok_and(|e| holds(&mut arena, &mut ctx, &e, &lhs, x)));

        let eq = lemmas.succ_r(&mut arena, x, y);
        let lhs = sum(&mut arena, x, &succ_val(y));
        let rhs = succ_val(&sum(&mut arena, x, y));
        assert!(eq.is_ok_and(|e| holds(&mut arena, &mut ctx, &e, &lhs, &rhs)));

        let eq = lemmas.assoc(&mut arena, x, y, z);
        let xy = sum(&mut arena, x, y);
        let yz = sum(&mut arena, y, z);
        let lhs = sum(&mut arena, &xy, z);
        let rhs = sum(&mut arena, x, &yz);
        assert!(eq.is_ok_and(|e| holds(&mut arena, &mut ctx, &e, &lhs, &rhs)));

        let eq = lemmas.comm(&mut arena, x, y);
        let yx = sum(&mut arena, y, x);
        assert!(eq.is_ok_and(|e| holds(&mut arena, &mut ctx, &e, &xy, &yx)));

        let eq = lemmas.left_comm(&mut arena, x, y, z);
        let xz = sum(&mut arena, x, z);
        let lhs = sum(&mut arena, x, &yz);
        let rhs = sum(&mut arena, y, &xz);
        assert!(eq.is_ok_and(|e| holds(&mut arena, &mut ctx, &e, &lhs, &rhs)));

        let shifted = lemmas.comm(&mut arena, &succ_val(x), &Value::Zero);
        let lhs = sum(&mut arena, &succ_val(x), &Value::Zero);
        let rhs = succ_val(x);
        assert!(
            shifted.is_ok_and(|e| holds(&mut arena, &mut ctx, &e, &lhs, &rhs)
                && !same(&arena, &ctx, &e.lhs, &rhs))
        );
    }
}
