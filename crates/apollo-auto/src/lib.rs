pub mod egraph;
pub mod lemmas;
pub mod linear;
pub mod proof;
pub mod render;
#[cfg(test)]
pub mod testing;

use std::fmt;

use apollo_kernel::nbe::{conv, quote};
use apollo_kernel::{
    Ctx, DeBruijnLevel, Dim, EvalError, Index, Multiplicity, TermArena, TermId, TypeError, Value,
    check, infer,
};

use crate::egraph::{EGraph, Reason};
use crate::lemmas::NatLemmas;
use crate::linear::{Atom, Normalizer};
use crate::proof::Equation;

#[must_use]
pub const fn version() -> &'static str {
    env!("CARGO_PKG_VERSION")
}

#[must_use]
pub fn add_term(arena: &mut TermArena, lhs: TermId, rhs: TermId) -> TermId {
    let motive = arena.nat();
    let ih = arena.var(Index(0));
    let step = arena.succ(ih);
    arena.nat_elim(motive, rhs, step, lhs)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AutoError {
    NotPathGoal,
    Eval(EvalError),
    Type(TypeError),
    Unproved {
        lhs: TermId,
        rhs: TermId,
        lhs_normal: TermId,
        rhs_normal: TermId,
    },
}

impl From<EvalError> for AutoError {
    fn from(value: EvalError) -> Self {
        Self::Eval(value)
    }
}

impl From<TypeError> for AutoError {
    fn from(value: TypeError) -> Self {
        Self::Type(value)
    }
}

impl fmt::Display for AutoError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NotPathGoal => f.write_str("auto requires a non-dependent Path goal"),
            Self::Eval(err) => write!(f, "auto evaluation error: {err}"),
            Self::Type(err) => write!(f, "kernel rejected auto proof: {err}"),
            Self::Unproved { .. } => f.write_str("auto could not prove the goal"),
        }
    }
}

impl std::error::Error for AutoError {}

fn path_sides(arena: &TermArena, ctx: &Ctx, ty: &Value) -> Option<(Value, Value, Value)> {
    let Value::Path {
        family,
        left,
        right,
    } = ty
    else {
        return None;
    };
    let mut probe = ctx.clone();
    let dim = probe.push_dim();
    let at_zero = family.apply(arena, Value::Dim(Dim::Zero)).ok()?;
    let at_var = family.apply(arena, dim).ok()?;
    conv(arena, probe.depth(), &at_zero, &at_var)
        .ok()
        .filter(|&same| same)
        .map(|_| (at_zero, (**left).clone(), (**right).clone()))
}

fn hypotheses(arena: &TermArena, ctx: &Ctx) -> Vec<Equation> {
    let mut hyps = Vec::new();
    for (level, ty) in (0_u32..).zip(ctx.types()) {
        if let Some((ty, lhs, rhs)) = path_sides(arena, ctx, ty) {
            hyps.push(Equation {
                ty,
                lhs,
                rhs,
                proof: Value::var(DeBruijnLevel(level)),
            });
        }
    }
    hyps
}

fn infer_value(arena: &mut TermArena, ctx: &mut Ctx, value: &Value) -> Result<Value, AutoError> {
    let term = quote(arena, ctx.depth(), value)?;
    let (ty, _) = infer(arena, ctx, Multiplicity::Zero, term)?;
    Ok(ty)
}

struct Prover<'a> {
    ctx: &'a mut Ctx,
    graph: EGraph,
    lemmas: NatLemmas,
}

impl Prover<'_> {
    fn node(&mut self, arena: &mut TermArena, value: &Value) -> Result<usize, AutoError> {
        let ctx = &mut *self.ctx;
        self.graph
            .add(arena, value, &mut |a, v| infer_value(a, ctx, v))
    }

    fn representative(
        &mut self,
        arena: &mut TermArena,
        value: &Value,
    ) -> Result<(Atom, Equation), AutoError> {
        let node = self.node(arena, value)?;
        let depth = self.ctx.depth();
        let mut keyed = Vec::new();
        for member in self.graph.members(node) {
            keyed.push((quote(arena, depth, self.graph.value(member))?, member));
        }
        let fallback = (quote(arena, depth, value)?, node);
        let (key, rep) = keyed
            .into_iter()
            .min_by_key(|(k, _)| k.raw())
            .unwrap_or(fallback);
        let eq = self.graph.explain(arena, node, rep)?;
        Ok((
            Atom {
                key,
                value: self.graph.value(rep).clone(),
            },
            eq,
        ))
    }

    fn normal_form(&mut self, arena: &mut TermArena, value: &Value) -> Result<Equation, AutoError> {
        let lemmas = self.lemmas;
        let normalizer = Normalizer {
            lemmas: &lemmas,
            depth: self.ctx.depth(),
        };
        let (_, eq) = normalizer.normalize(arena, value, &mut |a, v| self.representative(a, v))?;
        Ok(eq)
    }

    fn assume(&mut self, arena: &mut TermArena, eq: Equation) -> Result<(), AutoError> {
        let a = self.node(arena, &eq.lhs)?;
        let b = self.node(arena, &eq.rhs)?;
        self.graph.merge(a, b, Reason::Given(Box::new(eq)));
        Ok(())
    }
}

pub fn prove(arena: &mut TermArena, ctx: &mut Ctx, goal: &Value) -> Result<TermId, AutoError> {
    let depth = ctx.depth();
    let (ty, lhs, rhs) = path_sides(arena, ctx, goal).ok_or(AutoError::NotPathGoal)?;
    let hyps = hypotheses(arena, ctx);
    let lemmas = NatLemmas::build(arena)?;
    let mut prover = Prover {
        ctx,
        graph: EGraph::new(depth),
        lemmas,
    };
    let l = prover.node(arena, &lhs)?;
    let r = prover.node(arena, &rhs)?;
    let is_nat = matches!(ty, Value::Nat);
    let mut nat_terms = Vec::new();
    if is_nat {
        nat_terms.push(lhs.clone());
        nat_terms.push(rhs.clone());
    }
    for hyp in &hyps {
        if matches!(hyp.ty, Value::Nat) {
            nat_terms.push(hyp.lhs.clone());
            nat_terms.push(hyp.rhs.clone());
        }
        prover.assume(arena, hyp.clone())?;
    }
    prover.graph.close();

    let mut normals = (lhs.clone(), rhs.clone());
    if prover.graph.find(l) != prover.graph.find(r) {
        nat_terms.extend(prover.graph.arithmetic());
        let mut eqs = Vec::with_capacity(nat_terms.len());
        for term in &nat_terms {
            eqs.push(prover.normal_form(arena, term)?);
        }
        if is_nat {
            normals = (eqs[0].rhs.clone(), eqs[1].rhs.clone());
        }
        for eq in eqs {
            prover.assume(arena, eq)?;
        }
        prover.graph.close();
    }

    if prover.graph.find(l) == prover.graph.find(r) {
        let eq = prover.graph.explain(arena, l, r)?;
        let term = quote(arena, depth, &eq.proof)?;
        let _ = check(arena, prover.ctx, Multiplicity::Zero, term, goal)?;
        return Ok(term);
    }
    Err(AutoError::Unproved {
        lhs: quote(arena, depth, &lhs)?,
        rhs: quote(arena, depth, &rhs)?,
        lhs_normal: quote(arena, depth, &normals.0)?,
        rhs_normal: quote(arena, depth, &normals.1)?,
    })
}

#[cfg(test)]
mod tests {
    use apollo_kernel::{Ctx, EvalError, Index, Term, TermArena, TermId, TypeError, Value};

    use super::{AutoError, add_term, prove, version};
    use crate::lemmas::{add_val, succ_val};
    use crate::proof::path_type;

    fn nat_goal(arena: &mut TermArena, lhs: &Value, rhs: &Value) -> Value {
        path_type(arena, &Value::Nat, lhs, rhs)
    }

    fn sum(arena: &mut TermArena, lhs: &Value, rhs: &Value) -> Value {
        add_val(arena, lhs, rhs).unwrap_or(Value::Unit)
    }

    #[test]
    fn proves_sums_modulo_hypothesis_classes_with_interleaved_atoms() {
        let mut arena = TermArena::new();
        let keys: Vec<TermId> = [3, 2, 1].iter().map(|&i| arena.var(Index(i))).collect();
        assert!(keys.windows(2).all(|w| w[0].raw() < w[1].raw()));
        let mut ctx = Ctx::new();
        let first = ctx.push(Value::Nat);
        let second = ctx.push(Value::Nat);
        let third = ctx.push(Value::Nat);
        let hyp = nat_goal(&mut arena, &first, &third);
        let _ = ctx.push(hyp);

        let lhs = sum(&mut arena, &first, &second);
        let rhs = sum(&mut arena, &second, &third);
        let goal = nat_goal(&mut arena, &lhs, &rhs);
        let proved = prove(&mut arena, &mut ctx, &goal);
        assert!(proved.is_ok(), "auto failed: {:?}", proved.err());

        let rhs_succ = succ_val(&rhs);
        let lhs_succ = sum(&mut arena, &first, &succ_val(&second));
        let shifted = nat_goal(&mut arena, &lhs_succ, &rhs_succ);
        assert!(prove(&mut arena, &mut ctx, &shifted).is_ok());

        let unrelated = nat_goal(&mut arena, &first, &second);
        assert!(matches!(
            prove(&mut arena, &mut ctx, &unrelated),
            Err(AutoError::Unproved { lhs, rhs, .. }) if lhs == keys[0] && rhs == keys[1]
        ));
        assert_eq!(
            prove(&mut arena, &mut ctx, &Value::Nat),
            Err(AutoError::NotPathGoal)
        );
    }

    #[test]
    fn converts_and_describes_auto_errors() {
        let eval =
            EvalError::InvalidTermId(TermArena::new().universe(apollo_kernel::Level::zero()));
        assert!(matches!(AutoError::from(eval.clone()), AutoError::Eval(e) if e == eval));
        assert_eq!(
            AutoError::from(TypeError::TypeMismatch),
            AutoError::Type(TypeError::TypeMismatch)
        );
        let mut arena = TermArena::new();
        let id = arena.zero();
        for (err, needle) in [
            (AutoError::NotPathGoal, "non-dependent Path goal"),
            (AutoError::Eval(eval), "auto evaluation error"),
            (
                AutoError::Type(TypeError::TypeMismatch),
                "kernel rejected auto proof",
            ),
            (
                AutoError::Unproved {
                    lhs: id,
                    rhs: id,
                    lhs_normal: id,
                    rhs_normal: id,
                },
                "could not prove",
            ),
        ] {
            assert!(err.to_string().contains(needle), "{err}");
        }
    }

    #[test]
    fn reports_package_version() {
        assert_eq!(version(), env!("CARGO_PKG_VERSION"));
    }

    #[test]
    fn builds_canonical_addition_as_recursion_on_left_operand() {
        let mut arena = TermArena::new();
        let a = arena.var(Index(1));
        let b = arena.var(Index(0));
        let sum = add_term(&mut arena, a, b);
        let nat = arena.nat();
        let ih = arena.var(Index(0));
        let step = arena.succ(ih);
        assert_eq!(
            arena.get(sum),
            Some(&Term::NatElim {
                motive: nat,
                base: b,
                step,
                scrut: a,
            })
        );
    }
}
