use std::fmt;
use std::sync::Arc;

use crate::cubical::{Cof, Dim, Face};
use crate::level::Level;
use crate::multiplicity::{Multiplicity, UsageError, UsageVec};
use crate::nbe::{Closure, Env, EvalError, Value, conv, eval, eval_cof, proj_fst, subtype};
use crate::term::{CofTerm, DeBruijnLevel, Index, Term, TermArena, TermId};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeError {
    Eval(EvalError),
    Usage(UsageError),
    InvalidTermId(TermId),
    UnboundIndex {
        index: Index,
        depth: u32,
    },
    ExpectedUniverse,
    ExpectedFunction,
    ExpectedPair,
    ExpectedPath,
    CannotInferLambda,
    CannotInferPair,
    CannotInferPathLambda,
    PathBoundaryMismatch,
    HComBoundaryMismatch,
    MultiplicityMismatch {
        expected: Multiplicity,
        actual: Multiplicity,
    },
    BinderUsageViolation {
        used: Multiplicity,
        expected: Multiplicity,
    },
    ErasedProjection,
    TypeMismatch,
}

impl From<EvalError> for TypeError {
    fn from(value: EvalError) -> Self {
        Self::Eval(value)
    }
}

impl From<UsageError> for TypeError {
    fn from(value: UsageError) -> Self {
        Self::Usage(value)
    }
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Eval(err) => write!(f, "evaluation error: {err}"),
            Self::Usage(err) => write!(f, "usage error: {err}"),
            Self::InvalidTermId(id) => write!(f, "invalid term id {}", id.raw()),
            Self::UnboundIndex { index, depth } => {
                write!(f, "unbound variable {index} at depth {depth}")
            }
            Self::ExpectedUniverse => f.write_str("expected a universe type"),
            Self::ExpectedFunction => f.write_str("expected a function type"),
            Self::ExpectedPair => f.write_str("expected a dependent pair type"),
            Self::ExpectedPath => f.write_str("expected a cubical path type"),
            Self::CannotInferLambda => f.write_str("cannot infer type of unannotated lambda"),
            Self::CannotInferPair => f.write_str("cannot infer type of unannotated pair"),
            Self::CannotInferPathLambda => {
                f.write_str("cannot infer type of unannotated path lambda")
            }
            Self::PathBoundaryMismatch => f.write_str("path boundary mismatch"),
            Self::HComBoundaryMismatch => f.write_str("composition boundary mismatch"),
            Self::MultiplicityMismatch { expected, actual } => {
                write!(
                    f,
                    "multiplicity mismatch: expected {expected}, got {actual}"
                )
            }
            Self::BinderUsageViolation { used, expected } => {
                write!(
                    f,
                    "binder used with multiplicity {used}, expected {expected}"
                )
            }
            Self::ErasedProjection => {
                f.write_str("cannot project erased pair component at runtime")
            }
            Self::TypeMismatch => f.write_str("type mismatch"),
        }
    }
}

impl std::error::Error for TypeError {}

#[derive(Debug, Clone, Default)]
pub struct Ctx {
    types: Vec<Value>,
    env: Env,
}

impl Ctx {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    #[must_use]
    pub fn depth(&self) -> u32 {
        u32::try_from(self.types.len()).unwrap_or(u32::MAX)
    }

    pub fn push(&mut self, ty: Value) -> Value {
        let var = Value::var(DeBruijnLevel(self.depth()));
        self.types.push(ty);
        self.env.push(var.clone());
        var
    }

    pub fn push_dim(&mut self) -> Value {
        let dim = Value::dim_var(self.depth());
        self.types.push(Value::Interval);
        self.env.push(dim.clone());
        dim
    }

    pub fn pop(&mut self) {
        let _ = self.types.pop();
        let _ = self.env.pop();
    }
}

const fn child_mode(outer_mode: Multiplicity, binder_mult: Multiplicity) -> Multiplicity {
    if outer_mode.is_erased() || binder_mult.is_erased() {
        Multiplicity::Zero
    } else {
        Multiplicity::One
    }
}

pub fn check_is_type(arena: &TermArena, ctx: &mut Ctx, term: TermId) -> Result<Level, TypeError> {
    let (ty, _) = infer(arena, ctx, Multiplicity::Zero, term)?;
    match ty {
        Value::Universe(level) => Ok(level),
        _ => Err(TypeError::ExpectedUniverse),
    }
}

fn infer_binder_universe(
    arena: &TermArena,
    ctx: &mut Ctx,
    domain: TermId,
    codomain: TermId,
) -> Result<(Value, UsageVec), TypeError> {
    let depth = ctx.types.len();
    let l1 = check_is_type(arena, ctx, domain)?;
    let dom_val = eval(arena, &ctx.env, domain)?;
    let _ = ctx.push(dom_val);
    let l2_res = check_is_type(arena, ctx, codomain);
    ctx.pop();
    let l2 = l2_res?;
    Ok((Value::Universe(l1.max(&l2)), UsageVec::zero(depth)))
}

fn infer_app(
    arena: &TermArena,
    ctx: &mut Ctx,
    mode: Multiplicity,
    func: TermId,
    arg: TermId,
) -> Result<(Value, UsageVec), TypeError> {
    let (func_ty, u_func) = infer(arena, ctx, mode, func)?;
    let Value::Pi {
        mult,
        domain,
        codomain,
    } = func_ty
    else {
        return Err(TypeError::ExpectedFunction);
    };
    let arg_mode = child_mode(mode, mult);
    let u_arg = check(arena, ctx, arg_mode, arg, &domain)?;
    let arg_val = eval(arena, &ctx.env, arg)?;
    let res_ty = codomain.apply(arena, arg_val)?;
    let total = u_func.add(&u_arg.scale(mult))?;
    Ok((res_ty, total))
}

fn infer_path(
    arena: &TermArena,
    ctx: &mut Ctx,
    family: TermId,
    left: TermId,
    right: TermId,
) -> Result<(Value, UsageVec), TypeError> {
    let depth = ctx.types.len();
    let _ = ctx.push_dim();
    let level_res = check_is_type(arena, ctx, family);
    ctx.pop();
    let level = level_res?;
    let fam_closure = Closure::new(ctx.env.clone(), family);
    let left_ty = fam_closure.apply(arena, Value::Dim(Dim::Zero))?;
    let right_ty = fam_closure.apply(arena, Value::Dim(Dim::One))?;
    let _ = check(arena, ctx, Multiplicity::Zero, left, &left_ty)?;
    let _ = check(arena, ctx, Multiplicity::Zero, right, &right_ty)?;
    Ok((Value::Universe(level), UsageVec::zero(depth)))
}

fn infer_papp(
    arena: &TermArena,
    ctx: &mut Ctx,
    mode: Multiplicity,
    path: TermId,
    left: TermId,
    right: TermId,
    dim: TermId,
) -> Result<(Value, UsageVec), TypeError> {
    let (path_ty, u_path) = infer(arena, ctx, mode, path)?;
    let Value::Path {
        family,
        left: ty_left,
        right: ty_right,
    } = path_ty
    else {
        return Err(TypeError::ExpectedPath);
    };
    let _ = check(arena, ctx, Multiplicity::Zero, dim, &Value::Interval)?;
    let left_val = eval(arena, &ctx.env, left)?;
    let right_val = eval(arena, &ctx.env, right)?;
    if !conv(arena, ctx.depth(), &left_val, &ty_left)?
        || !conv(arena, ctx.depth(), &right_val, &ty_right)?
    {
        return Err(TypeError::PathBoundaryMismatch);
    }
    let dim_val = eval(arena, &ctx.env, dim)?;
    let res_ty = family.apply(arena, dim_val)?;
    Ok((res_ty, u_path))
}

fn infer_coe(
    arena: &TermArena,
    ctx: &mut Ctx,
    mode: Multiplicity,
    line: TermId,
    src: TermId,
    dst: TermId,
    term: TermId,
) -> Result<(Value, UsageVec), TypeError> {
    let _ = ctx.push_dim();
    let line_res = check_is_type(arena, ctx, line);
    ctx.pop();
    let _ = line_res?;
    let _ = check(arena, ctx, Multiplicity::Zero, src, &Value::Interval)?;
    let _ = check(arena, ctx, Multiplicity::Zero, dst, &Value::Interval)?;
    let src_val = eval(arena, &ctx.env, src)?;
    let dst_val = eval(arena, &ctx.env, dst)?;
    let line_closure = Closure::new(ctx.env.clone(), line);
    let src_ty = line_closure.apply(arena, src_val)?;
    let dst_ty = line_closure.apply(arena, dst_val)?;
    let usage = check(arena, ctx, mode, term, &src_ty)?;
    Ok((dst_ty, usage))
}

fn check_cof(arena: &TermArena, ctx: &mut Ctx, cof: &CofTerm) -> Result<(), TypeError> {
    match cof {
        CofTerm::Top | CofTerm::Bot => Ok(()),
        CofTerm::Eq(lhs, rhs) => {
            let _ = check(arena, ctx, Multiplicity::Zero, *lhs, &Value::Interval)?;
            let _ = check(arena, ctx, Multiplicity::Zero, *rhs, &Value::Interval)?;
            Ok(())
        }
        CofTerm::And(lhs, rhs) | CofTerm::Or(lhs, rhs) => {
            check_cof(arena, ctx, lhs)?;
            check_cof(arena, ctx, rhs)
        }
    }
}

fn restrict_env(env: &[Value], face: &Face) -> Env {
    env.iter()
        .map(|val| match val {
            Value::Dim(dim) => Value::Dim(face.canonical_dim(*dim)),
            other => other.clone(),
        })
        .collect()
}

struct HComSpec<'a> {
    ty: TermId,
    src: TermId,
    dst: TermId,
    branches: &'a [(CofTerm, TermId)],
    cap: TermId,
}

fn infer_hcom(
    arena: &TermArena,
    ctx: &mut Ctx,
    mode: Multiplicity,
    spec: &HComSpec<'_>,
) -> Result<(Value, UsageVec), TypeError> {
    let _ = check_is_type(arena, ctx, spec.ty)?;
    let _ = check(arena, ctx, Multiplicity::Zero, spec.src, &Value::Interval)?;
    let _ = check(arena, ctx, Multiplicity::Zero, spec.dst, &Value::Interval)?;
    let ty_val = eval(arena, &ctx.env, spec.ty)?;
    let usage = check(arena, ctx, mode, spec.cap, &ty_val)?;
    let depth = ctx.depth();

    let mut checked_branches = Vec::with_capacity(spec.branches.len());
    for (cof_term, tube) in spec.branches {
        check_cof(arena, ctx, cof_term)?;
        let cof = eval_cof(arena, &ctx.env, cof_term)?;
        let _ = ctx.push_dim();
        let tube_res = check(arena, ctx, Multiplicity::Zero, *tube, &ty_val);
        ctx.pop();
        let _ = tube_res?;

        for face in cof.faces() {
            let f_env = restrict_env(&ctx.env, &face);
            let f_src = eval(arena, &f_env, spec.src)?;
            let tube_at_src = Closure::new(f_env.clone(), *tube).apply(arena, f_src)?;
            let cap_on_face = eval(arena, &f_env, spec.cap)?;
            if !conv(arena, depth, &tube_at_src, &cap_on_face)? {
                return Err(TypeError::HComBoundaryMismatch);
            }
        }
        checked_branches.push((cof, *tube));
    }

    let mut rem = checked_branches.as_slice();
    while let Some(((cof_a, tube_a), rest)) = rem.split_first() {
        for (cof_b, tube_b) in rest {
            let overlap = Cof::and(cof_a.clone(), cof_b.clone());
            for face in overlap.faces() {
                let f_env = restrict_env(&ctx.env, &face);
                let dim_j = Value::dim_var(depth);
                let va = Closure::new(f_env.clone(), *tube_a).apply(arena, dim_j.clone())?;
                let vb = Closure::new(f_env, *tube_b).apply(arena, dim_j)?;
                if !conv(arena, depth + 1, &va, &vb)? {
                    return Err(TypeError::HComBoundaryMismatch);
                }
            }
        }
        rem = rest;
    }

    Ok((ty_val, usage))
}

fn check_motive(
    arena: &TermArena,
    ctx: &mut Ctx,
    dom: Value,
    motive: TermId,
) -> Result<Closure, TypeError> {
    let _ = ctx.push(dom);
    let res = check_is_type(arena, ctx, motive);
    ctx.pop();
    let _ = res?;
    Ok(Closure::new(ctx.env.clone(), motive))
}

fn infer_unit_elim(
    arena: &TermArena,
    ctx: &mut Ctx,
    mode: Multiplicity,
    motive: TermId,
    on_unit: TermId,
    scrut: TermId,
) -> Result<(Value, UsageVec), TypeError> {
    let motive_cl = check_motive(arena, ctx, Value::Unit, motive)?;
    let u_scrut = check(arena, ctx, mode, scrut, &Value::Unit)?;
    let unit_ty = motive_cl.apply(arena, Value::Tt)?;
    let u_unit = check(arena, ctx, mode, on_unit, &unit_ty)?;
    let scrut_val = eval(arena, &ctx.env, scrut)?;
    let res_ty = motive_cl.apply(arena, scrut_val)?;
    Ok((res_ty, u_scrut.add(&u_unit)?))
}

fn infer_void_elim(
    arena: &TermArena,
    ctx: &mut Ctx,
    mode: Multiplicity,
    motive: TermId,
    scrut: TermId,
) -> Result<(Value, UsageVec), TypeError> {
    let motive_cl = check_motive(arena, ctx, Value::Void, motive)?;
    let u_scrut = check(arena, ctx, mode, scrut, &Value::Void)?;
    let scrut_val = eval(arena, &ctx.env, scrut)?;
    let res_ty = motive_cl.apply(arena, scrut_val)?;
    Ok((res_ty, u_scrut))
}

fn infer_bool_elim(
    arena: &TermArena,
    ctx: &mut Ctx,
    mode: Multiplicity,
    motive: TermId,
    on_true: TermId,
    on_false: TermId,
    scrut: TermId,
) -> Result<(Value, UsageVec), TypeError> {
    let motive_cl = check_motive(arena, ctx, Value::Bool, motive)?;
    let u_scrut = check(arena, ctx, mode, scrut, &Value::Bool)?;
    let true_ty = motive_cl.apply(arena, Value::True)?;
    let u_true = check(arena, ctx, mode, on_true, &true_ty)?;
    let false_ty = motive_cl.apply(arena, Value::False)?;
    let u_false = check(arena, ctx, mode, on_false, &false_ty)?;
    let u_branches = u_true.join(&u_false)?;
    let scrut_val = eval(arena, &ctx.env, scrut)?;
    let res_ty = motive_cl.apply(arena, scrut_val)?;
    Ok((res_ty, u_scrut.add(&u_branches)?))
}

fn infer_nat_elim(
    arena: &TermArena,
    ctx: &mut Ctx,
    mode: Multiplicity,
    motive: TermId,
    base: TermId,
    step: TermId,
    scrut: TermId,
) -> Result<(Value, UsageVec), TypeError> {
    let motive_cl = check_motive(arena, ctx, Value::Nat, motive)?;
    let u_scrut = check(arena, ctx, mode, scrut, &Value::Nat)?;
    let base_ty = motive_cl.apply(arena, Value::Zero)?;
    let u_base = check(arena, ctx, mode, base, &base_ty)?;

    let k_var = ctx.push(Value::Nat);
    let ih_ty = motive_cl.apply(arena, k_var.clone())?;
    let succ_ty = motive_cl.apply(arena, Value::Succ(Arc::new(k_var)))?;
    let _ = ctx.push(ih_ty);
    let step_res = check(arena, ctx, mode, step, &succ_ty);
    ctx.pop();
    ctx.pop();
    let mut u_step = step_res?;
    let _ = u_step.pop_last();
    let _ = u_step.pop_last();

    let total = u_scrut
        .add(&u_base)?
        .add(&u_step.scale(Multiplicity::Many))?;
    let scrut_val = eval(arena, &ctx.env, scrut)?;
    let res_ty = motive_cl.apply(arena, scrut_val)?;
    Ok((res_ty, total))
}

pub fn infer(
    arena: &TermArena,
    ctx: &mut Ctx,
    mode: Multiplicity,
    id: TermId,
) -> Result<(Value, UsageVec), TypeError> {
    let term = arena.get(id).ok_or(TypeError::InvalidTermId(id))?;
    let depth = ctx.types.len();

    match term {
        Term::Universe(level) => Ok((Value::Universe(level.succ()), UsageVec::zero(depth))),
        Term::Var(index) => {
            let idx = index.0 as usize;
            if idx >= depth {
                return Err(TypeError::UnboundIndex {
                    index: *index,
                    depth: ctx.depth(),
                });
            }
            let level = depth - 1 - idx;
            let ty = ctx.types[level].clone();
            let usage = UsageVec::single(depth, level, mode)?;
            Ok((ty, usage))
        }
        Term::Pi {
            domain, codomain, ..
        } => infer_binder_universe(arena, ctx, *domain, *codomain),
        Term::Sigma { first, second, .. } => infer_binder_universe(arena, ctx, *first, *second),
        Term::App { func, arg } => infer_app(arena, ctx, mode, *func, *arg),
        Term::Fst(pair) => {
            let (pair_ty, u_pair) = infer(arena, ctx, mode, *pair)?;
            let Value::Sigma { mult, first, .. } = pair_ty else {
                return Err(TypeError::ExpectedPair);
            };
            if !mode.is_erased() && mult.is_erased() {
                return Err(TypeError::ErasedProjection);
            }
            Ok(((*first).clone(), u_pair))
        }
        Term::Snd(pair) => {
            let (pair_ty, u_pair) = infer(arena, ctx, mode, *pair)?;
            let Value::Sigma { second, .. } = pair_ty else {
                return Err(TypeError::ExpectedPair);
            };
            let pair_val = eval(arena, &ctx.env, *pair)?;
            let fst_val = proj_fst(&pair_val);
            let snd_ty = second.apply(arena, fst_val)?;
            Ok((snd_ty, u_pair))
        }
        Term::Ann { term, ty } => {
            let _ = check_is_type(arena, ctx, *ty)?;
            let ty_val = eval(arena, &ctx.env, *ty)?;
            let usage = check(arena, ctx, mode, *term, &ty_val)?;
            Ok((ty_val, usage))
        }
        Term::Interval => Err(TypeError::ExpectedUniverse),
        Term::DimZero | Term::DimOne => Ok((Value::Interval, UsageVec::zero(depth))),
        Term::Path {
            family,
            left,
            right,
        } => infer_path(arena, ctx, *family, *left, *right),
        Term::PApp {
            path,
            left,
            right,
            dim,
        } => infer_papp(arena, ctx, mode, *path, *left, *right, *dim),
        Term::Coe {
            line,
            src,
            dst,
            term,
        } => infer_coe(arena, ctx, mode, *line, *src, *dst, *term),
        Term::HCom {
            ty,
            src,
            dst,
            branches,
            cap,
        } => infer_hcom(
            arena,
            ctx,
            mode,
            &HComSpec {
                ty: *ty,
                src: *src,
                dst: *dst,
                branches,
                cap: *cap,
            },
        ),
        Term::Lam { .. } => Err(TypeError::CannotInferLambda),
        Term::Pair { .. } => Err(TypeError::CannotInferPair),
        Term::PLam(_) => Err(TypeError::CannotInferPathLambda),
        other => infer_inductive(arena, ctx, mode, depth, other),
    }
}

fn infer_inductive(
    arena: &TermArena,
    ctx: &mut Ctx,
    mode: Multiplicity,
    depth: usize,
    term: &Term,
) -> Result<(Value, UsageVec), TypeError> {
    match term {
        Term::Unit | Term::Void | Term::Bool | Term::Nat => {
            Ok((Value::Universe(Level::zero()), UsageVec::zero(depth)))
        }
        Term::Tt => Ok((Value::Unit, UsageVec::zero(depth))),
        Term::UnitElim {
            motive,
            on_unit,
            scrut,
        } => infer_unit_elim(arena, ctx, mode, *motive, *on_unit, *scrut),
        Term::VoidElim { motive, scrut } => infer_void_elim(arena, ctx, mode, *motive, *scrut),
        Term::True | Term::False => Ok((Value::Bool, UsageVec::zero(depth))),
        Term::BoolElim {
            motive,
            on_true,
            on_false,
            scrut,
        } => infer_bool_elim(arena, ctx, mode, *motive, *on_true, *on_false, *scrut),
        Term::Zero => Ok((Value::Nat, UsageVec::zero(depth))),
        Term::Succ(pred) => {
            let u_pred = check(arena, ctx, mode, *pred, &Value::Nat)?;
            Ok((Value::Nat, u_pred))
        }
        Term::NatElim {
            motive,
            base,
            step,
            scrut,
        } => infer_nat_elim(arena, ctx, mode, *motive, *base, *step, *scrut),
        _ => Err(TypeError::TypeMismatch),
    }
}

pub fn check(
    arena: &TermArena,
    ctx: &mut Ctx,
    mode: Multiplicity,
    id: TermId,
    expected: &Value,
) -> Result<UsageVec, TypeError> {
    let term = arena.get(id).ok_or(TypeError::InvalidTermId(id))?;

    match (term, expected) {
        (
            Term::Lam { mult, body },
            Value::Pi {
                mult: pi_mult,
                domain,
                codomain,
            },
        ) => {
            if mult != pi_mult {
                return Err(TypeError::MultiplicityMismatch {
                    expected: *pi_mult,
                    actual: *mult,
                });
            }
            let var = ctx.push((**domain).clone());
            let body_res = codomain
                .apply(arena, var)
                .map_err(TypeError::Eval)
                .and_then(|cod_ty| check(arena, ctx, mode, *body, &cod_ty));
            ctx.pop();
            let mut usage = body_res?;
            let used = usage.pop_last().unwrap_or(Multiplicity::Zero);
            let allowed = mode * *mult;
            if !used.fits_in(allowed) {
                return Err(TypeError::BinderUsageViolation {
                    used,
                    expected: allowed,
                });
            }
            Ok(usage)
        }
        (
            Term::Pair { first, second },
            Value::Sigma {
                mult,
                first: first_ty,
                second: second_ty,
            },
        ) => {
            let first_mode = child_mode(mode, *mult);
            let u1 = check(arena, ctx, first_mode, *first, first_ty)?;
            let first_val = eval(arena, &ctx.env, *first)?;
            let snd_ty = second_ty.apply(arena, first_val)?;
            let u2 = check(arena, ctx, mode, *second, &snd_ty)?;
            Ok(u1.scale(*mult).add(&u2)?)
        }
        (
            Term::PLam(body),
            Value::Path {
                family,
                left,
                right,
            },
        ) => {
            let dim_var = ctx.push_dim();
            let body_res = family
                .apply(arena, dim_var)
                .map_err(TypeError::Eval)
                .and_then(|fam_ty| check(arena, ctx, Multiplicity::Zero, *body, &fam_ty));
            ctx.pop();
            let _ = body_res?;
            let body_closure = Closure::new(ctx.env.clone(), *body);
            let at_zero = body_closure.apply(arena, Value::Dim(Dim::Zero))?;
            let at_one = body_closure.apply(arena, Value::Dim(Dim::One))?;
            if !conv(arena, ctx.depth(), &at_zero, left)?
                || !conv(arena, ctx.depth(), &at_one, right)?
            {
                return Err(TypeError::PathBoundaryMismatch);
            }
            Ok(UsageVec::zero(ctx.types.len()))
        }
        _ => {
            let check_mode = if matches!(expected, Value::Path { .. }) {
                Multiplicity::Zero
            } else {
                mode
            };
            let (actual, usage) = infer(arena, ctx, check_mode, id)?;
            if subtype(arena, ctx.depth(), &actual, expected)? {
                Ok(usage)
            } else {
                Err(TypeError::TypeMismatch)
            }
        }
    }
}

pub fn infer_closed(arena: &TermArena, term: TermId) -> Result<Value, TypeError> {
    let mut ctx = Ctx::new();
    let (ty, _) = infer(arena, &mut ctx, Multiplicity::One, term)?;
    Ok(ty)
}

pub fn check_closed(arena: &TermArena, term: TermId, ty: TermId) -> Result<(), TypeError> {
    let mut ctx = Ctx::new();
    let _ = check_is_type(arena, &mut ctx, ty)?;
    let ty_val = eval(arena, &ctx.env, ty)?;
    let _ = check(arena, &mut ctx, Multiplicity::One, term, &ty_val)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::{Ctx, TypeError, check_closed, check_is_type, infer, infer_closed};
    use crate::level::Level;
    use crate::multiplicity::{Multiplicity, UsageError};
    use crate::nbe::{EvalError, Value, conv};
    use crate::term::{Index, TermArena};

    #[test]
    fn checks_polymorphic_linear_identity_and_application() {
        let mut arena = TermArena::new();
        let u0 = arena.universe(Level::zero());
        let u1 = arena.universe(Level::constant(1));
        let v0 = arena.var(Index(0));
        let v1 = arena.var(Index(1));

        let inner_pi = arena.pi(Multiplicity::One, v0, v1);
        let id_ty = arena.pi(Multiplicity::Zero, u1, inner_pi);
        let inner_lam = arena.lam(Multiplicity::One, v0);
        let id_expr = arena.lam(Multiplicity::Zero, inner_lam);

        assert_eq!(check_closed(&arena, id_expr, id_ty), Ok(()));

        let id_ann = arena.ann(id_expr, id_ty);
        let app_u0 = arena.app(id_ann, u0);
        let inferred = infer_closed(&arena, app_u0);
        assert!(inferred.is_ok());

        let expected_ty = arena.pi(Multiplicity::One, u0, u0);
        assert_eq!(check_closed(&arena, u0, u1), Ok(()));
        let u2 = arena.universe(Level::constant(2));
        assert_eq!(check_closed(&arena, u0, u2), Ok(()));
        assert!(inferred.is_ok());
        if let Ok(actual) = inferred {
            let mut ctx = Ctx::new();
            let _ = check_is_type(&arena, &mut ctx, expected_ty);
            let expected = crate::nbe::eval(&arena, &[], expected_ty);
            assert!(expected.is_ok());
            if let Ok(exp) = expected {
                assert_eq!(conv(&arena, 0, &actual, &exp), Ok(true));
            }
        }
    }

    #[test]
    fn enforces_linear_no_drop_no_duplicate_and_erased_isolation() {
        let mut arena = TermArena::new();
        let u0 = arena.universe(Level::zero());
        let v0 = arena.var(Index(0));
        let v1 = arena.var(Index(1));

        let v2 = arena.var(Index(2));
        let pair_self = arena.pair(v0, v0);
        let dup_body = arena.lam(Multiplicity::One, pair_self);
        let dup_tm = arena.lam(Multiplicity::Zero, dup_body);
        let pair_ty = arena.sigma(Multiplicity::One, v1, v2);
        let lin_dup_inner = arena.pi(Multiplicity::One, v0, pair_ty);
        let lin_dup_ty = arena.pi(Multiplicity::Zero, u0, lin_dup_inner);

        assert_eq!(
            check_closed(&arena, dup_tm, lin_dup_ty),
            Err(TypeError::BinderUsageViolation {
                used: Multiplicity::Many,
                expected: Multiplicity::One,
            })
        );

        let many_dup_body = arena.lam(Multiplicity::Many, pair_self);
        let many_dup_expr = arena.lam(Multiplicity::Zero, many_dup_body);
        let many_dup_inner = arena.pi(Multiplicity::Many, v0, pair_ty);
        let many_dup_ty = arena.pi(Multiplicity::Zero, u0, many_dup_inner);
        assert_eq!(check_closed(&arena, many_dup_expr, many_dup_ty), Ok(()));

        let drop_inner_lam = arena.lam(Multiplicity::One, v0);
        let drop_mid_lam = arena.lam(Multiplicity::One, drop_inner_lam);
        let drop_expr = arena.lam(Multiplicity::Zero, drop_mid_lam);
        let drop_v2 = arena.var(Index(2));
        let drop_pi2 = arena.pi(Multiplicity::One, v1, drop_v2);
        let drop_pi1 = arena.pi(Multiplicity::One, v0, drop_pi2);
        let drop_ty = arena.pi(Multiplicity::Zero, u0, drop_pi1);
        assert_eq!(
            check_closed(&arena, drop_expr, drop_ty),
            Err(TypeError::BinderUsageViolation {
                used: Multiplicity::Zero,
                expected: Multiplicity::One,
            })
        );

        let erased_inner = arena.lam(Multiplicity::Zero, v0);
        let erased_use = arena.lam(Multiplicity::Zero, erased_inner);
        let erased_pi = arena.pi(Multiplicity::Zero, v0, v1);
        let erased_ty = arena.pi(Multiplicity::Zero, u0, erased_pi);
        assert_eq!(
            check_closed(&arena, erased_use, erased_ty),
            Err(TypeError::BinderUsageViolation {
                used: Multiplicity::One,
                expected: Multiplicity::Zero,
            })
        );
    }

    #[test]
    fn handles_dependent_sigma_and_erased_projection_rules() {
        let mut arena = TermArena::new();
        let u0 = arena.universe(Level::zero());
        let u1 = arena.universe(Level::constant(1));
        let v0 = arena.var(Index(0));
        let v1 = arena.var(Index(1));

        let endo = arena.pi(Multiplicity::One, v0, v1);
        let pkg_ty = arena.sigma(Multiplicity::Zero, u1, endo);
        let id_fn = arena.lam(Multiplicity::One, v0);
        let pkg = arena.pair(u0, id_fn);
        assert_eq!(check_closed(&arena, pkg, pkg_ty), Ok(()));

        let pkg_ann = arena.ann(pkg, pkg_ty);
        let bad_fst = arena.fst(pkg_ann);
        assert_eq!(
            infer_closed(&arena, bad_fst).err(),
            Some(TypeError::ErasedProjection)
        );

        let mut ctx = Ctx::new();
        let erased_fst = infer(&arena, &mut ctx, Multiplicity::Zero, bad_fst);
        assert!(erased_fst.is_ok());

        let ok_snd = arena.snd(pkg_ann);
        let snd_ty = infer_closed(&arena, ok_snd);
        assert!(snd_ty.is_ok());

        let rt_pkg_ty = arena.sigma(Multiplicity::One, u1, u1);
        let rt_pkg = arena.pair(u0, u0);
        let rt_ann = arena.ann(rt_pkg, rt_pkg_ty);
        let rt_fst = arena.fst(rt_ann);
        let inferred_fst = infer_closed(&arena, rt_fst);
        assert!(inferred_fst.is_ok());
        if let Ok(actual) = inferred_fst {
            assert_eq!(
                conv(&arena, 0, &actual, &Value::Universe(Level::constant(1))),
                Ok(true)
            );
        }
    }

    #[test]
    fn allows_internal_linear_lambda_in_many_argument_and_blocks_linear_capture() {
        let mut arena = TermArena::new();
        let u0 = arena.universe(Level::zero());
        let v0 = arena.var(Index(0));
        let v1 = arena.var(Index(1));
        let v2 = arena.var(Index(2));

        let lin_id_ty = arena.pi(Multiplicity::One, v0, v1);
        let take_many_fn_ty = arena.pi(Multiplicity::Many, lin_id_ty, v1);
        let outer_ty = arena.pi(Multiplicity::Zero, u0, take_many_fn_ty);

        let lin_id = arena.lam(Multiplicity::One, v0);
        let call_f = arena.app(v0, lin_id);
        let pass_inner = arena.lam(Multiplicity::One, call_f);
        let pass_id = arena.lam(Multiplicity::Zero, pass_inner);
        let hof_inner = arena.pi(Multiplicity::One, take_many_fn_ty, v1);
        let hof_ty = arena.pi(Multiplicity::Zero, u0, hof_inner);
        assert_eq!(check_closed(&arena, pass_id, hof_ty), Ok(()));
        assert!(infer_closed(&arena, outer_ty).is_ok());

        let bad_capture_body = arena.app(v1, v0);
        let bad_l1 = arena.lam(Multiplicity::One, bad_capture_body);
        let bad_l2 = arena.lam(Multiplicity::One, bad_l1);
        let bad_capture = arena.lam(Multiplicity::Zero, bad_l2);
        let many_fn = arena.pi(Multiplicity::Many, v0, v1);
        let inner_arg = arena.pi(Multiplicity::One, v1, v2);
        let mid_pi = arena.pi(Multiplicity::One, many_fn, inner_arg);
        let bad_capture_ty = arena.pi(Multiplicity::Zero, u0, mid_pi);
        assert_eq!(
            check_closed(&arena, bad_capture, bad_capture_ty),
            Err(TypeError::BinderUsageViolation {
                used: Multiplicity::Many,
                expected: Multiplicity::One,
            })
        );
    }

    #[test]
    fn reports_all_type_error_variants_and_displays() {
        let mut arena = TermArena::new();
        let u0 = arena.universe(Level::zero());
        let u1 = arena.universe(Level::constant(1));
        let v0 = arena.var(Index(0));

        let lam = arena.lam(Multiplicity::One, v0);
        let pair = arena.pair(u0, u0);
        let bad_app = arena.app(u0, u0);
        let bad_fst = arena.fst(u0);
        let bad_snd = arena.snd(u0);
        let lam_many = arena.lam(Multiplicity::Many, v0);
        let pi_one = arena.pi(Multiplicity::One, u0, u0);
        let fn_val = arena.ann(lam, pi_one);

        let errors = [
            infer_closed(&arena, lam).err(),
            infer_closed(&arena, pair).err(),
            infer_closed(&arena, bad_app).err(),
            infer_closed(&arena, bad_fst).err(),
            infer_closed(&arena, bad_snd).err(),
            infer_closed(&arena, v0).err(),
            check_closed(&arena, u1, u0).err(),
            check_closed(&arena, lam_many, pi_one).err(),
            check_closed(&arena, u0, fn_val).err(),
            Some(TypeError::Eval(EvalError::InvalidTermId(u0))),
            Some(TypeError::Usage(UsageError::LengthMismatch {
                expected: 1,
                actual: 2,
            })),
            Some(TypeError::InvalidTermId(u0)),
            Some(TypeError::ErasedProjection),
            Some(TypeError::BinderUsageViolation {
                used: Multiplicity::Many,
                expected: Multiplicity::One,
            }),
        ];

        for maybe_err in errors {
            assert!(maybe_err.is_some());
            if let Some(err) = maybe_err {
                assert_ne!(err.to_string(), "");
            }
        }
    }

    #[test]
    fn distinguishes_outer_type_binders_and_allows_erased_type_level_projection() {
        let mut arena = TermArena::new();
        let u0 = arena.universe(Level::zero());
        let v0 = arena.var(Index(0));
        let v1 = arena.var(Index(1));
        let v2 = arena.var(Index(2));
        let v3 = arena.var(Index(3));

        let pi_y = arena.pi(Multiplicity::Zero, v1, v3);
        let pi_x = arena.pi(Multiplicity::One, v1, pi_y);
        let pi_b = arena.pi(Multiplicity::Zero, u0, pi_x);
        let const_ty = arena.pi(Multiplicity::Zero, u0, pi_b);

        let valid_step1 = arena.lam(Multiplicity::Zero, v1);
        let valid_step2 = arena.lam(Multiplicity::One, valid_step1);
        let valid_step3 = arena.lam(Multiplicity::Zero, valid_step2);
        let ret_x = arena.lam(Multiplicity::Zero, valid_step3);
        assert_eq!(check_closed(&arena, ret_x, const_ty), Ok(()));

        let wrong_step1 = arena.lam(Multiplicity::Zero, v0);
        let wrong_step2 = arena.lam(Multiplicity::One, wrong_step1);
        let wrong_step3 = arena.lam(Multiplicity::Zero, wrong_step2);
        let ret_y = arena.lam(Multiplicity::Zero, wrong_step3);
        assert_eq!(
            check_closed(&arena, ret_y, const_ty),
            Err(TypeError::TypeMismatch)
        );

        let f_ty = arena.pi(Multiplicity::One, u0, u0);
        let p_ty = arena.sigma(Multiplicity::Zero, u0, u0);
        let p_fst = arena.fst(v0);
        let f_of_fst = arena.app(v1, p_fst);
        let p_fst_shifted = arena.fst(v1);
        let f_of_fst_shifted = arena.app(v2, p_fst_shifted);
        let inner_id_pi = arena.pi(Multiplicity::One, f_of_fst, f_of_fst_shifted);
        let take_p_pi = arena.pi(Multiplicity::Zero, p_ty, inner_id_pi);
        let full_ty = arena.pi(Multiplicity::Zero, f_ty, take_p_pi);

        let id_body = arena.lam(Multiplicity::One, v0);
        let take_p = arena.lam(Multiplicity::Zero, id_body);
        let take_f = arena.lam(Multiplicity::Zero, take_p);
        assert_eq!(check_closed(&arena, take_f, full_ty), Ok(()));
    }

    fn wrap_zero_lams(
        arena: &mut TermArena,
        count: usize,
        mut body: crate::term::TermId,
    ) -> crate::term::TermId {
        for _ in 0..count {
            body = arena.lam(Multiplicity::Zero, body);
        }
        body
    }

    #[test]
    fn proves_refl_and_linear_pair_with_refl() {
        let mut arena = TermArena::new();
        let u0 = arena.universe(Level::zero());
        let v0 = arena.var(Index(0));
        let v1 = arena.var(Index(1));
        let v2 = arena.var(Index(2));
        let v3 = arena.var(Index(3));

        let refl_path = arena.path(v2, v0, v0);
        let refl_inner = arena.pi(Multiplicity::Zero, v0, refl_path);
        let refl_ty = arena.pi(Multiplicity::Zero, u0, refl_inner);
        let refl_plam = arena.plam(v1);
        let refl_expr = wrap_zero_lams(&mut arena, 2, refl_plam);
        assert_eq!(check_closed(&arena, refl_expr, refl_ty), Ok(()));

        let linear_with_refl_path = arena.path(v3, v1, v0);
        let linear_with_refl_sig = arena.sigma(Multiplicity::One, v1, linear_with_refl_path);
        let linear_with_refl_pi = arena.pi(Multiplicity::One, v0, linear_with_refl_sig);
        let linear_with_refl_ty = arena.pi(Multiplicity::Zero, u0, linear_with_refl_pi);
        let linear_pair = arena.pair(v0, refl_plam);
        let linear_lam_x = arena.lam(Multiplicity::One, linear_pair);
        let linear_with_refl = arena.lam(Multiplicity::Zero, linear_lam_x);
        assert_eq!(
            check_closed(&arena, linear_with_refl, linear_with_refl_ty),
            Ok(())
        );
    }

    #[test]
    fn proves_ap_and_function_extensionality() {
        let mut arena = TermArena::new();
        let u0 = arena.universe(Level::zero());
        let v0 = arena.var(Index(0));
        let v1 = arena.var(Index(1));
        let v2 = arena.var(Index(2));
        let v3 = arena.var(Index(3));
        let v4 = arena.var(Index(4));
        let v5 = arena.var(Index(5));

        let fn_ab = arena.pi(Multiplicity::One, v1, v1);
        let p_xy = arena.path(v5, v1, v0);
        let fx = arena.app(v3, v2);
        let fy = arena.app(v3, v1);
        let ap_ret = arena.path(v5, fx, fy);
        let ap_ty = [p_xy, v3, v2, fn_ab, u0, u0]
            .into_iter()
            .fold(ap_ret, |cod, dom| arena.pi(Multiplicity::Zero, dom, cod));

        let p_at_i = arena.papp(v1, v3, v2, v0);
        let f_of_pi = arena.app(v4, p_at_i);
        let ap_plam = arena.plam(f_of_pi);
        let ap_expr = wrap_zero_lams(&mut arena, 6, ap_plam);
        assert_eq!(check_closed(&arena, ap_expr, ap_ty), Ok(()));

        let fn_ab_at_f = arena.pi(Multiplicity::One, v2, v2);
        let f_app_x = arena.app(v2, v0);
        let g_app_x = arena.app(v1, v0);
        let h_path = arena.path(v4, f_app_x, g_app_x);
        let h_ty = arena.pi(Multiplicity::Zero, v3, h_path);
        let fn_ab_under_i = arena.pi(Multiplicity::One, v5, v5);
        let funext_ret = arena.path(fn_ab_under_i, v2, v1);
        let funext_ty = [h_ty, fn_ab_at_f, fn_ab, u0, u0]
            .into_iter()
            .fold(funext_ret, |cod, dom| {
                arena.pi(Multiplicity::Zero, dom, cod)
            });

        let h_of_x = arena.app(v2, v0);
        let f_of_x_inner = arena.app(v4, v0);
        let g_of_x_inner = arena.app(v3, v0);
        let h_x_at_i = arena.papp(h_of_x, f_of_x_inner, g_of_x_inner, v1);
        let fe_inner_lam = arena.lam(Multiplicity::One, h_x_at_i);
        let fe_plam = arena.plam(fe_inner_lam);
        let funext_expr = wrap_zero_lams(&mut arena, 5, fe_plam);
        assert_eq!(check_closed(&arena, funext_expr, funext_ty), Ok(()));
    }

    #[test]
    fn rejects_path_boundary_mismatches_and_path_errors() {
        let mut arena = TermArena::new();
        let u0 = arena.universe(Level::zero());
        let d0 = arena.dim_zero();
        let d1 = arena.dim_one();
        let v0 = arena.var(Index(0));
        let v1 = arena.var(Index(1));
        let v2 = arena.var(Index(2));
        let v3 = arena.var(Index(3));

        let bad_ty_path = arena.path(v3, v1, v0);
        let bad_ty = [v1, v0, u0].into_iter().fold(bad_ty_path, |cod, dom| {
            arena.pi(Multiplicity::Zero, dom, cod)
        });

        let bad_left_plam = arena.plam(v1);
        let bad_left = wrap_zero_lams(&mut arena, 3, bad_left_plam);
        assert_eq!(
            check_closed(&arena, bad_left, bad_ty),
            Err(TypeError::PathBoundaryMismatch)
        );

        let bad_right_plam = arena.plam(v2);
        let bad_right = wrap_zero_lams(&mut arena, 3, bad_right_plam);
        assert_eq!(
            check_closed(&arena, bad_right, bad_ty),
            Err(TypeError::PathBoundaryMismatch)
        );

        let wrong_papp_ty = [bad_ty_path, v1, v0, u0]
            .into_iter()
            .fold(v3, |cod, dom| arena.pi(Multiplicity::Zero, dom, cod));
        let wrong_left_papp = arena.papp(v0, v1, v1, d0);
        let wrong_left_fn = wrap_zero_lams(&mut arena, 4, wrong_left_papp);
        assert_eq!(
            check_closed(&arena, wrong_left_fn, wrong_papp_ty),
            Err(TypeError::PathBoundaryMismatch)
        );
        let wrong_right_papp = arena.papp(v0, v2, v2, d0);
        let wrong_right_fn = wrap_zero_lams(&mut arena, 4, wrong_right_papp);
        assert_eq!(
            check_closed(&arena, wrong_right_fn, wrong_papp_ty),
            Err(TypeError::PathBoundaryMismatch)
        );

        let bad_papp = arena.papp(u0, u0, u0, d0);
        assert_eq!(
            infer_closed(&arena, bad_papp).err(),
            Some(TypeError::ExpectedPath)
        );
        assert_eq!(
            infer_closed(&arena, bad_left_plam).err(),
            Some(TypeError::CannotInferPathLambda)
        );
        let interval = arena.interval();
        assert_eq!(
            infer_closed(&arena, interval).err(),
            Some(TypeError::ExpectedUniverse)
        );
        assert!(infer_closed(&arena, d0).is_ok());
        assert!(infer_closed(&arena, d1).is_ok());

        for err in [
            TypeError::ExpectedPath,
            TypeError::CannotInferPathLambda,
            TypeError::PathBoundaryMismatch,
        ] {
            assert_ne!(err.to_string(), "");
        }
    }

    #[test]
    fn proves_transport_subst_and_transport_refl_via_coercion() {
        let mut arena = TermArena::new();
        let u0 = arena.universe(Level::zero());
        let u1 = arena.universe(Level::constant(1));
        let d0 = arena.dim_zero();
        let d1 = arena.dim_one();
        let v0 = arena.var(Index(0));
        let v1 = arena.var(Index(1));
        let v2 = arena.var(Index(2));
        let v3 = arena.var(Index(3));
        let v4 = arena.var(Index(4));
        let v5 = arena.var(Index(5));

        let path_ab = arena.path(u0, v1, v0);
        let transport_inner = arena.pi(Multiplicity::One, v2, v2);
        let transport_ty = [path_ab, u0, u0]
            .into_iter()
            .fold(transport_inner, |cod, dom| {
                arena.pi(Multiplicity::Zero, dom, cod)
            });

        let p_at_i = arena.papp(v2, v4, v3, v0);
        let transport_body = arena.coe(p_at_i, d0, d1, v0);
        let transport_lam_x = arena.lam(Multiplicity::One, transport_body);
        let transport_expr = wrap_zero_lams(&mut arena, 3, transport_lam_x);
        assert_eq!(check_closed(&arena, transport_expr, transport_ty), Ok(()));

        let p_fam = arena.pi(Multiplicity::Zero, v0, u0);
        let p_xy = arena.path(v4, v1, v0);
        let src_pred_ty = arena.app(v3, v2);
        let dst_pred_ty = arena.app(v4, v2);
        let subst_inner = arena.pi(Multiplicity::One, src_pred_ty, dst_pred_ty);
        let subst_ty = [p_xy, v2, v1, p_fam, u0]
            .into_iter()
            .fold(subst_inner, |cod, dom| {
                arena.pi(Multiplicity::Zero, dom, cod)
            });

        let p_at_i_sub = arena.papp(v2, v4, v3, v0);
        let pred_at_i = arena.app(v5, p_at_i_sub);
        let subst_body = arena.coe(pred_at_i, d0, d1, v0);
        let subst_lam_px = arena.lam(Multiplicity::One, subst_body);
        let subst_expr = wrap_zero_lams(&mut arena, 5, subst_lam_px);
        assert_eq!(check_closed(&arena, subst_expr, subst_ty), Ok(()));

        let coe_const = arena.coe(v2, d0, d1, v0);
        let refl_path_ty = arena.path(v2, coe_const, v0);
        let transport_refl_ty = [v0, u0].into_iter().fold(refl_path_ty, |cod, dom| {
            arena.pi(Multiplicity::Zero, dom, cod)
        });
        let coe_from_i = arena.coe(v3, v0, d1, v1);
        let refl_plam = arena.plam(coe_from_i);
        let transport_refl_expr = wrap_zero_lams(&mut arena, 2, refl_plam);
        assert_eq!(
            check_closed(&arena, transport_refl_expr, transport_refl_ty),
            Ok(())
        );

        let wrong_coe = arena.coe(u0, d0, d1, u1);
        assert_eq!(
            infer_closed(&arena, wrong_coe).err(),
            Some(TypeError::TypeMismatch)
        );
    }

    #[test]
    fn proves_path_symmetry_and_transitivity_via_hcom() {
        let mut arena = TermArena::new();
        let u0 = arena.universe(Level::zero());
        let d0 = arena.dim_zero();
        let d1 = arena.dim_one();
        let v0 = arena.var(Index(0));
        let v1 = arena.var(Index(1));
        let v2 = arena.var(Index(2));
        let v3 = arena.var(Index(3));
        let v4 = arena.var(Index(4));
        let v5 = arena.var(Index(5));
        let v6 = arena.var(Index(6));

        let p_xy = arena.path(v3, v1, v0);
        let sym_ret = arena.path(v4, v1, v2);
        let sym_ty = [p_xy, v1, v0, u0]
            .into_iter()
            .fold(sym_ret, |cod, dom| arena.pi(Multiplicity::Zero, dom, cod));

        let sym_tube_0 = arena.papp(v2, v4, v3, v0);
        let sym_hcom = arena.hcom(
            v4,
            d0,
            d1,
            vec![
                (crate::term::CofTerm::Eq(v0, d0), sym_tube_0),
                (crate::term::CofTerm::Eq(v0, d1), v4),
            ],
            v3,
        );
        let sym_plam = arena.plam(sym_hcom);
        let sym_expr = wrap_zero_lams(&mut arena, 4, sym_plam);
        assert_eq!(check_closed(&arena, sym_expr, sym_ty), Ok(()));

        let p_xy_tr = arena.path(v4, v2, v1);
        let q_yz_tr = arena.path(v5, v2, v1);
        let trans_ret = arena.path(v6, v4, v2);
        let trans_ty = [q_yz_tr, p_xy_tr, v2, v1, v0, u0]
            .into_iter()
            .fold(trans_ret, |cod, dom| arena.pi(Multiplicity::Zero, dom, cod));

        let cap_pi = arena.papp(v2, v5, v4, v0);
        let tube_qj = arena.papp(v2, v5, v4, v0);
        let trans_hcom = arena.hcom(
            v6,
            d0,
            d1,
            vec![
                (crate::term::CofTerm::Eq(v0, d0), v6),
                (crate::term::CofTerm::Eq(v0, d1), tube_qj),
            ],
            cap_pi,
        );
        let trans_plam = arena.plam(trans_hcom);
        let trans_expr = wrap_zero_lams(&mut arena, 6, trans_plam);
        assert_eq!(check_closed(&arena, trans_expr, trans_ty), Ok(()));
    }

    #[test]
    fn rejects_inconsistent_hcom_cap_and_branch_overlap() {
        let mut arena = TermArena::new();
        let u0 = arena.universe(Level::zero());
        let d0 = arena.dim_zero();
        let d1 = arena.dim_one();
        let v0 = arena.var(Index(0));
        let v1 = arena.var(Index(1));
        let v2 = arena.var(Index(2));
        let v3 = arena.var(Index(3));
        let v4 = arena.var(Index(4));

        let p_xy = arena.path(v3, v1, v0);
        let sym_ret = arena.path(v4, v1, v2);
        let sym_ty = [p_xy, v1, v0, u0]
            .into_iter()
            .fold(sym_ret, |cod, dom| arena.pi(Multiplicity::Zero, dom, cod));

        let bad_cap_hcom = arena.hcom(v4, d0, d1, vec![(crate::term::CofTerm::Eq(v0, d0), v3)], v3);
        let bad_cap_plam = arena.plam(bad_cap_hcom);
        let bad_cap_expr = wrap_zero_lams(&mut arena, 4, bad_cap_plam);
        assert_eq!(
            check_closed(&arena, bad_cap_expr, sym_ty),
            Err(TypeError::HComBoundaryMismatch)
        );

        let overlap_cof = crate::term::CofTerm::Or(
            Box::new(crate::term::CofTerm::Eq(v0, d0)),
            Box::new(crate::term::CofTerm::Eq(v0, d1)),
        );
        let p_at_j = arena.papp(v2, v4, v3, v0);
        let bad_overlap_hcom = arena.hcom(
            v4,
            d0,
            d1,
            vec![
                (crate::term::CofTerm::Eq(v0, d0), p_at_j),
                (overlap_cof, v4),
            ],
            v3,
        );
        let bad_overlap_plam = arena.plam(bad_overlap_hcom);
        let bad_overlap_expr = wrap_zero_lams(&mut arena, 4, bad_overlap_plam);
        assert_eq!(
            check_closed(&arena, bad_overlap_expr, sym_ty),
            Err(TypeError::HComBoundaryMismatch)
        );

        let u1 = arena.universe(Level::constant(1));
        let bad_cof_hcom = arena.hcom(u1, d0, d1, vec![(crate::term::CofTerm::Eq(u0, d0), u0)], u0);
        assert_eq!(
            infer_closed(&arena, bad_cof_hcom).err(),
            Some(TypeError::TypeMismatch)
        );
        assert_ne!(TypeError::HComBoundaryMismatch.to_string(), "");
    }

    #[test]
    fn rejects_nested_hcom_overlap_at_different_depths() {
        let mut arena = TermArena::new();
        let u0 = arena.universe(Level::zero());
        let d0 = arena.dim_zero();
        let d1 = arena.dim_one();
        let v0 = arena.var(Index(0));
        let v1 = arena.var(Index(1));
        let v2 = arena.var(Index(2));
        let v3 = arena.var(Index(3));
        let v4 = arena.var(Index(4));

        let path_xx = arena.path(v3, v1, v1);
        let outer_cap = arena.plam(v1);
        let cap_refl = arena.plam(v2);
        let outer_path = arena.path(path_xx, outer_cap, outer_cap);
        let outer_ty = [v0, u0].into_iter().fold(outer_path, |cod, dom| {
            arena.pi(Multiplicity::Zero, dom, cod)
        });
        let inner_body = arena.hcom(
            v4,
            d0,
            v1,
            vec![
                (crate::term::CofTerm::Eq(v0, d0), v4),
                (crate::term::CofTerm::Eq(v0, d1), v4),
                (crate::term::CofTerm::Eq(v0, d0), v4),
            ],
            v3,
        );
        let tube_inner = arena.plam(inner_body);
        let mid_body = arena.hcom(
            v4,
            d0,
            v1,
            vec![
                (crate::term::CofTerm::Eq(v0, d0), v4),
                (crate::term::CofTerm::Eq(v0, d1), v4),
                (crate::term::CofTerm::Eq(v1, d0), v4),
            ],
            v3,
        );
        let tube_mid = arena.plam(mid_body);
        let outer_body = arena.hcom(
            v4,
            d0,
            v1,
            vec![
                (crate::term::CofTerm::Eq(v0, d0), v4),
                (crate::term::CofTerm::Eq(v0, d1), v4),
                (crate::term::CofTerm::Eq(v2, d0), v4),
            ],
            v3,
        );
        let tube_outer = arena.plam(outer_body);
        let overlap_mid = arena.hcom(
            path_xx,
            d0,
            d1,
            vec![
                (crate::term::CofTerm::Top, tube_inner),
                (crate::term::CofTerm::Top, tube_mid),
            ],
            cap_refl,
        );
        let overlap_mid_plam = arena.plam(overlap_mid);
        let overlap_mid_expr = wrap_zero_lams(&mut arena, 2, overlap_mid_plam);
        assert_eq!(
            check_closed(&arena, overlap_mid_expr, outer_ty),
            Err(TypeError::HComBoundaryMismatch)
        );
        let overlap_outer = arena.hcom(
            path_xx,
            d0,
            d1,
            vec![
                (crate::term::CofTerm::Top, tube_inner),
                (crate::term::CofTerm::Top, tube_outer),
            ],
            cap_refl,
        );
        let overlap_outer_plam = arena.plam(overlap_outer);
        let overlap_outer_expr = wrap_zero_lams(&mut arena, 2, overlap_outer_plam);
        assert_eq!(
            check_closed(&arena, overlap_outer_expr, outer_ty),
            Err(TypeError::HComBoundaryMismatch)
        );
    }

    #[test]
    fn checks_unit_void_and_bool_proofs_with_qtt_branches() {
        let mut arena = TermArena::new();
        let u0 = arena.universe(Level::zero());
        let unit = arena.unit();
        let tt = arena.tt();
        let void = arena.void();
        let bool_ty = arena.bool_ty();
        let b_true = arena.bool_true();
        let b_false = arena.bool_false();
        let v0 = arena.var(Index(0));
        let v1 = arena.var(Index(1));
        let v2 = arena.var(Index(2));
        let v3 = arena.var(Index(3));
        let v4 = arena.var(Index(4));

        let absurd_inner = arena.pi(Multiplicity::One, void, v1);
        let absurd_ty = arena.pi(Multiplicity::Zero, u0, absurd_inner);
        let absurd_elim = arena.void_elim(v2, v0);
        let absurd_lam = arena.lam(Multiplicity::One, absurd_elim);
        let absurd_body = arena.lam(Multiplicity::Zero, absurd_lam);
        assert_eq!(check_closed(&arena, absurd_body, absurd_ty), Ok(()));

        let unit_id_ty = arena.pi(Multiplicity::One, unit, unit);
        let unit_elim = arena.unit_elim(unit, tt, v0);
        let unit_id = arena.lam(Multiplicity::One, unit_elim);
        assert_eq!(check_closed(&arena, unit_id, unit_id_ty), Ok(()));

        let not_ty = arena.pi(Multiplicity::One, bool_ty, bool_ty);
        let not_elim = arena.bool_elim(bool_ty, b_false, b_true, v0);
        let not_body = arena.lam(Multiplicity::One, not_elim);
        assert_eq!(check_closed(&arena, not_body, not_ty), Ok(()));

        let erased_bool_ty = arena.pi(Multiplicity::Zero, bool_ty, bool_ty);
        let erased_bool_body = arena.lam(Multiplicity::Zero, not_elim);
        assert_eq!(
            check_closed(&arena, erased_bool_body, erased_bool_ty),
            Err(TypeError::BinderUsageViolation {
                used: Multiplicity::One,
                expected: Multiplicity::Zero,
            })
        );

        let not_ann = arena.ann(not_body, not_ty);
        let not_b = arena.app(not_ann, v0);
        let not_not_b = arena.app(not_ann, not_b);
        let not_not_path = arena.path(bool_ty, not_not_b, v0);
        let not_not_ty = arena.pi(Multiplicity::Zero, bool_ty, not_not_path);
        let refl_true = arena.plam(b_true);
        let refl_false = arena.plam(b_false);
        let not_not_elim = arena.bool_elim(not_not_path, refl_true, refl_false, v0);
        let not_not_body = arena.lam(Multiplicity::Zero, not_not_elim);
        assert_eq!(check_closed(&arena, not_not_body, not_not_ty), Ok(()));

        let choose_c = arena.pi(Multiplicity::One, bool_ty, v2);
        let choose_b = arena.pi(Multiplicity::One, v0, choose_c);
        let choose_ty = arena.pi(Multiplicity::Zero, u0, choose_b);
        let ok_elim = arena.bool_elim(v3, v1, v1, v0);
        let ok_l2 = arena.lam(Multiplicity::One, ok_elim);
        let ok_l1 = arena.lam(Multiplicity::One, ok_l2);
        let ok_branch = arena.lam(Multiplicity::Zero, ok_l1);
        assert_eq!(check_closed(&arena, ok_branch, choose_ty), Ok(()));

        let bad_d = arena.pi(Multiplicity::One, bool_ty, v3);
        let bad_c = arena.pi(Multiplicity::Many, v1, bad_d);
        let bad_b = arena.pi(Multiplicity::One, v0, bad_c);
        let bad_branch_ty = arena.pi(Multiplicity::Zero, u0, bad_b);
        let bad_elim = arena.bool_elim(v4, v2, v1, v0);
        let bad_l3 = arena.lam(Multiplicity::One, bad_elim);
        let bad_l2 = arena.lam(Multiplicity::Many, bad_l3);
        let bad_l1 = arena.lam(Multiplicity::One, bad_l2);
        let bad_branch = arena.lam(Multiplicity::Zero, bad_l1);
        assert_eq!(
            check_closed(&arena, bad_branch, bad_branch_ty),
            Err(TypeError::BinderUsageViolation {
                used: Multiplicity::Many,
                expected: Multiplicity::One,
            })
        );
    }

    #[test]
    fn checks_nat_arithmetic_and_cubical_induction_proofs() {
        let mut arena = TermArena::new();
        let nat = arena.nat();
        let zero = arena.zero();
        let v0 = arena.var(Index(0));
        let v1 = arena.var(Index(1));
        let v2 = arena.var(Index(2));

        let add_inner_ty = arena.pi(Multiplicity::One, nat, nat);
        let add_ty = arena.pi(Multiplicity::One, nat, add_inner_ty);
        let succ_v0 = arena.succ(v0);
        let add_elim = arena.nat_elim(nat, v0, succ_v0, v1);
        let add_inner_lam = arena.lam(Multiplicity::One, add_elim);
        let add_body = arena.lam(Multiplicity::One, add_inner_lam);
        assert_eq!(check_closed(&arena, add_body, add_ty), Ok(()));

        let add_ann = arena.ann(add_body, add_ty);
        let add_applied_n = arena.app(add_ann, v0);
        let add_n_zero = arena.app(add_applied_n, zero);
        let add_zero_path = arena.path(nat, add_n_zero, v0);
        let add_zero_ty = arena.pi(Multiplicity::Zero, nat, add_zero_path);
        let add_applied_k = arena.app(add_ann, v2);
        let step_lhs = arena.app(add_applied_k, zero);
        let ih_at_i = arena.papp(v1, step_lhs, v2, v0);
        let succ_ih = arena.succ(ih_at_i);
        let step_proof = arena.plam(succ_ih);
        let base_proof = arena.plam(zero);
        let add_zero_elim = arena.nat_elim(add_zero_path, base_proof, step_proof, v0);
        let add_zero_body = arena.lam(Multiplicity::Zero, add_zero_elim);
        assert_eq!(check_closed(&arena, add_zero_body, add_zero_ty), Ok(()));

        let mul_step_a = arena.app(add_ann, v0);
        let mul_step = arena.app(mul_step_a, v2);
        let mul_elim = arena.nat_elim(nat, zero, mul_step, v1);

        let mul_bad_inner = arena.pi(Multiplicity::One, nat, nat);
        let mul_bad_ty = arena.pi(Multiplicity::One, nat, mul_bad_inner);
        let mul_bad_l1 = arena.lam(Multiplicity::One, mul_elim);
        let mul_bad = arena.lam(Multiplicity::One, mul_bad_l1);
        assert_eq!(
            check_closed(&arena, mul_bad, mul_bad_ty),
            Err(TypeError::BinderUsageViolation {
                used: Multiplicity::Many,
                expected: Multiplicity::One,
            })
        );

        let mul_ok_inner = arena.pi(Multiplicity::Many, nat, nat);
        let mul_ok_ty = arena.pi(Multiplicity::One, nat, mul_ok_inner);
        let mul_ok_l1 = arena.lam(Multiplicity::Many, mul_elim);
        let mul_ok = arena.lam(Multiplicity::One, mul_ok_l1);
        assert_eq!(check_closed(&arena, mul_ok, mul_ok_ty), Ok(()));
    }
}
