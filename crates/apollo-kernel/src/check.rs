use std::fmt;

use crate::level::Level;
use crate::multiplicity::{Multiplicity, UsageError, UsageVec};
use crate::nbe::{Env, EvalError, Value, eval, proj_fst, subtype};
use crate::term::{DeBruijnLevel, Index, Term, TermArena, TermId};

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
    CannotInferLambda,
    CannotInferPair,
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
            Self::CannotInferLambda => f.write_str("cannot infer type of unannotated lambda"),
            Self::CannotInferPair => f.write_str("cannot infer type of unannotated pair"),
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
        } => {
            let l1 = check_is_type(arena, ctx, *domain)?;
            let dom_val = eval(arena, &ctx.env, *domain)?;
            let _ = ctx.push(dom_val);
            let l2_res = check_is_type(arena, ctx, *codomain);
            ctx.pop();
            let l2 = l2_res?;
            Ok((Value::Universe(l1.max(&l2)), UsageVec::zero(depth)))
        }
        Term::Sigma { first, second, .. } => {
            let l1 = check_is_type(arena, ctx, *first)?;
            let first_val = eval(arena, &ctx.env, *first)?;
            let _ = ctx.push(first_val);
            let l2_res = check_is_type(arena, ctx, *second);
            ctx.pop();
            let l2 = l2_res?;
            Ok((Value::Universe(l1.max(&l2)), UsageVec::zero(depth)))
        }
        Term::App { func, arg } => {
            let (func_ty, u_func) = infer(arena, ctx, mode, *func)?;
            let Value::Pi {
                mult,
                domain,
                codomain,
            } = func_ty
            else {
                return Err(TypeError::ExpectedFunction);
            };
            let arg_mode = child_mode(mode, mult);
            let u_arg = check(arena, ctx, arg_mode, *arg, &domain)?;
            let arg_val = eval(arena, &ctx.env, *arg)?;
            let res_ty = codomain.apply(arena, arg_val)?;
            let total = u_func.add(&u_arg.scale(mult))?;
            Ok((res_ty, total))
        }
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
        Term::Lam { .. } => Err(TypeError::CannotInferLambda),
        Term::Pair { .. } => Err(TypeError::CannotInferPair),
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
        _ => {
            let (actual, usage) = infer(arena, ctx, mode, id)?;
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
}
