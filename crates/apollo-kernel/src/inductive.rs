use std::fmt;

use crate::check::{Ctx, TypeError, check, check_is_type};
use crate::level::Level;
use crate::multiplicity::Multiplicity;
use crate::nbe::{Value, eval, quote};
use crate::term::{DeBruijnLevel, Term, TermArena, TermId};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct InductiveId(pub u32);

impl InductiveId {
    #[must_use]
    pub const fn raw(self) -> u32 {
        self.0
    }
}

impl fmt::Display for InductiveId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "data#{}", self.0)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParamDecl {
    pub mult: Multiplicity,
    pub ty: TermId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FieldDecl {
    pub mult: Multiplicity,
    pub ty: TermId,
    pub is_recursive: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PathBoundary {
    pub left: TermId,
    pub right: TermId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CtorDecl {
    pub fields: Vec<FieldDecl>,
    pub boundary: Option<PathBoundary>,
}

impl CtorDecl {
    #[must_use]
    pub const fn is_path(&self) -> bool {
        self.boundary.is_some()
    }

    #[must_use]
    pub fn recursive_count(&self) -> usize {
        self.fields.iter().filter(|f| f.is_recursive).count()
    }

    #[must_use]
    pub fn arg_arity(&self) -> usize {
        self.fields.len() + usize::from(self.is_path())
    }

    #[must_use]
    pub fn branch_arity(&self) -> usize {
        self.fields.len() + self.recursive_count() + usize::from(self.is_path())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InductiveDecl {
    pub params: Vec<ParamDecl>,
    pub level: Level,
    pub ctors: Vec<CtorDecl>,
}

fn any_term(arena: &TermArena, ids: &[TermId], pred: &impl Fn(&Term) -> bool) -> bool {
    ids.iter().any(|&id| term_any(arena, id, pred))
}

fn term_any(arena: &TermArena, id: TermId, pred: &impl Fn(&Term) -> bool) -> bool {
    let Some(term) = arena.get(id) else {
        return false;
    };
    if pred(term) {
        return true;
    }
    match term {
        Term::Lam { body: a, .. } | Term::Fst(a) | Term::Snd(a) | Term::PLam(a) | Term::Succ(a) => {
            term_any(arena, *a, pred)
        }
        Term::Pi {
            domain: a,
            codomain: b,
            ..
        }
        | Term::App { func: a, arg: b }
        | Term::Sigma {
            first: a,
            second: b,
            ..
        }
        | Term::Pair {
            first: a,
            second: b,
        }
        | Term::Ann { term: a, ty: b }
        | Term::VoidElim {
            motive: a,
            scrut: b,
        } => any_term(arena, &[*a, *b], pred),
        Term::Path {
            family: a,
            left: b,
            right: c,
        }
        | Term::UnitElim {
            motive: a,
            on_unit: b,
            scrut: c,
        }
        | Term::VIn {
            dim: a,
            left: b,
            right: c,
        } => any_term(arena, &[*a, *b, *c], pred),
        Term::PApp {
            path: a,
            left: b,
            right: c,
            dim: d,
        }
        | Term::Coe {
            line: a,
            src: b,
            dst: c,
            term: d,
        }
        | Term::VType {
            dim: a,
            ty0: b,
            ty1: c,
            equiv: d,
        }
        | Term::BoolElim {
            motive: a,
            on_true: b,
            on_false: c,
            scrut: d,
        }
        | Term::NatElim {
            motive: a,
            base: b,
            step: c,
            scrut: d,
        } => any_term(arena, &[*a, *b, *c, *d], pred),
        Term::VProj {
            dim,
            ty0,
            ty1,
            equiv,
            term,
        } => any_term(arena, &[*dim, *ty0, *ty1, *equiv, *term], pred),
        Term::HCom {
            ty,
            src,
            dst,
            branches,
            cap,
        } => {
            any_term(arena, &[*ty, *src, *dst, *cap], pred)
                || branches
                    .iter()
                    .any(|(_, tube)| term_any(arena, *tube, pred))
        }
        other => data_term_any(arena, other, pred),
    }
}

fn data_term_any(arena: &TermArena, term: &Term, pred: &impl Fn(&Term) -> bool) -> bool {
    match term {
        Term::Data { params, .. } => any_term(arena, params, pred),
        Term::Ctor { params, args, .. } => {
            any_term(arena, params, pred) || any_term(arena, args, pred)
        }
        Term::DataElim {
            params,
            motive,
            branches,
            scrut,
            ..
        } => {
            any_term(arena, &[*motive, *scrut], pred)
                || any_term(arena, params, pred)
                || any_term(arena, branches, pred)
        }
        _ => false,
    }
}

#[must_use]
pub fn term_mentions_inductive(arena: &TermArena, id: TermId, target: InductiveId) -> bool {
    term_any(arena, id, &|term| {
        matches!(
            term,
            Term::Data { id: did, .. }
                | Term::Ctor { id: did, .. }
                | Term::DataElim { id: did, .. }
                if *did == target
        )
    })
}

fn is_uniform_self_rec(
    arena: &TermArena,
    norm_ty: TermId,
    self_id: InductiveId,
    param_count: usize,
    depth: u32,
) -> bool {
    let Some(Term::Data { id, params }) = arena.get(norm_ty) else {
        return false;
    };
    if *id != self_id || params.len() != param_count {
        return false;
    }
    params.iter().enumerate().all(|(i, &p_id)| {
        let Ok(lvl) = u32::try_from(i) else {
            return false;
        };
        let Some(expected_idx) = DeBruijnLevel(lvl).to_index(depth) else {
            return false;
        };
        matches!(arena.get(p_id), Some(Term::Var(idx)) if *idx == expected_idx)
    })
}

pub fn check_and_define_inductive(
    arena: &mut TermArena,
    decl: InductiveDecl,
) -> Result<InductiveId, TypeError> {
    let self_id = arena.next_inductive_id();
    let placeholder = InductiveDecl {
        params: decl.params.clone(),
        level: decl.level.clone(),
        ctors: Vec::new(),
    };
    arena.push_inductive_raw(placeholder);

    let res = validate_inductive(arena, self_id, &decl);
    match res {
        Ok(checked_ctors) => {
            arena.set_inductive_raw(
                self_id,
                InductiveDecl {
                    params: decl.params,
                    level: decl.level,
                    ctors: checked_ctors,
                },
            );
            Ok(self_id)
        }
        Err(err) => {
            arena.pop_inductive_raw();
            Err(err)
        }
    }
}

fn validate_path_boundaries(
    arena: &TermArena,
    ctx: &mut Ctx,
    self_id: InductiveId,
    param_vars: &[Value],
    ctors: &[CtorDecl],
) -> Result<(), TypeError> {
    let data_ty = Value::Data {
        id: self_id,
        params: param_vars.to_vec(),
    };
    let uses_path_ctor = |term: &Term| {
        matches!(
            term,
            Term::Ctor { id, ctor, .. }
                if *id == self_id && ctors.get(*ctor as usize).is_some_and(CtorDecl::is_path)
        )
    };
    for ctor in ctors {
        let Some(boundary) = ctor.boundary else {
            continue;
        };
        if term_any(arena, boundary.left, &uses_path_ctor)
            || term_any(arena, boundary.right, &uses_path_ctor)
        {
            return Err(TypeError::HitBoundaryMismatch);
        }
        for field in &ctor.fields {
            let ty_val = eval(arena, ctx.env(), field.ty)?;
            let _ = ctx.push(ty_val);
        }
        let check_res = check(arena, ctx, Multiplicity::Zero, boundary.left, &data_ty)
            .and_then(|_| check(arena, ctx, Multiplicity::Zero, boundary.right, &data_ty));
        for _ in 0..ctor.fields.len() {
            ctx.pop();
        }
        let _ = check_res?;
    }
    Ok(())
}

fn validate_inductive(
    arena: &mut TermArena,
    self_id: InductiveId,
    decl: &InductiveDecl,
) -> Result<Vec<CtorDecl>, TypeError> {
    let mut ctx = Ctx::new();
    let mut param_vars = Vec::with_capacity(decl.params.len());
    for param in &decl.params {
        let _ = check_is_type(arena, &mut ctx, param.ty)?;
        let param_val = eval(arena, ctx.env(), param.ty)?;
        param_vars.push(ctx.push(param_val));
    }

    let param_count = decl.params.len();
    let mut checked_ctors = Vec::with_capacity(decl.ctors.len());
    for ctor in &decl.ctors {
        let mut checked_fields = Vec::with_capacity(ctor.fields.len());
        for field in &ctor.fields {
            let field_lvl = check_is_type(arena, &mut ctx, field.ty)?;
            if !field_lvl.leq(&decl.level) {
                return Err(TypeError::UniverseLevelTooHigh);
            }
            let ty_val = eval(arena, ctx.env(), field.ty)?;
            let depth = ctx.depth();
            let norm_ty = quote(arena, depth, &ty_val)?;
            let is_recursive = if is_uniform_self_rec(arena, norm_ty, self_id, param_count, depth) {
                true
            } else if term_mentions_inductive(arena, norm_ty, self_id) {
                return Err(TypeError::NonStrictlyPositive);
            } else {
                false
            };
            checked_fields.push(FieldDecl {
                mult: field.mult,
                ty: field.ty,
                is_recursive,
            });
            let _ = ctx.push(ty_val);
        }
        for _ in 0..ctor.fields.len() {
            ctx.pop();
        }
        checked_ctors.push(CtorDecl {
            fields: checked_fields,
            boundary: ctor.boundary,
        });
    }

    if checked_ctors.iter().any(CtorDecl::is_path) {
        arena.set_inductive_raw(
            self_id,
            InductiveDecl {
                params: decl.params.clone(),
                level: decl.level.clone(),
                ctors: checked_ctors.clone(),
            },
        );
        validate_path_boundaries(arena, &mut ctx, self_id, &param_vars, &checked_ctors)?;
    }

    Ok(checked_ctors)
}

#[cfg(test)]
mod tests {
    use super::{
        CtorDecl, FieldDecl, InductiveDecl, InductiveId, ParamDecl, PathBoundary,
        check_and_define_inductive, term_mentions_inductive,
    };
    use crate::Value;
    use crate::check::{TypeError, check_closed};
    use crate::level::Level;
    use crate::multiplicity::Multiplicity;
    use crate::nbe::{conv, eval, quote};
    use crate::term::{DeBruijnLevel, Index, TermArena, TermId};

    fn define_option(arena: &mut TermArena) -> InductiveId {
        let u0 = arena.universe(Level::zero());
        let v0 = arena.var(Index(0));
        let decl = InductiveDecl {
            params: vec![ParamDecl {
                mult: Multiplicity::Zero,
                ty: u0,
            }],
            level: Level::zero(),
            ctors: vec![
                CtorDecl {
                    fields: Vec::new(),
                    boundary: None,
                },
                CtorDecl {
                    fields: vec![FieldDecl {
                        mult: Multiplicity::One,
                        ty: v0,
                        is_recursive: false,
                    }],
                    boundary: None,
                },
            ],
        };
        let res = check_and_define_inductive(arena, decl);
        assert!(res.is_ok(), "Option definition failed: {:?}", res.err());
        res.unwrap_or(InductiveId(0))
    }

    fn define_list(arena: &mut TermArena) -> InductiveId {
        let self_id = arena.next_inductive_id();
        let u0 = arena.universe(Level::zero());
        let v0 = arena.var(Index(0));
        let v1 = arena.var(Index(1));
        let list_a = arena.data(self_id, vec![v1]);
        let decl = InductiveDecl {
            params: vec![ParamDecl {
                mult: Multiplicity::Zero,
                ty: u0,
            }],
            level: Level::zero(),
            ctors: vec![
                CtorDecl {
                    fields: Vec::new(),
                    boundary: None,
                },
                CtorDecl {
                    fields: vec![
                        FieldDecl {
                            mult: Multiplicity::One,
                            ty: v0,
                            is_recursive: false,
                        },
                        FieldDecl {
                            mult: Multiplicity::One,
                            ty: list_a,
                            is_recursive: false,
                        },
                    ],
                    boundary: None,
                },
            ],
        };
        let res = check_and_define_inductive(arena, decl);
        assert!(res.is_ok(), "List definition failed: {:?}", res.err());
        res.unwrap_or(InductiveId(0))
    }

    fn define_tree(arena: &mut TermArena) -> InductiveId {
        let self_id = arena.next_inductive_id();
        let u0 = arena.universe(Level::zero());
        let v0 = arena.var(Index(0));
        let v1 = arena.var(Index(1));
        let v2 = arena.var(Index(2));
        let tree_at_0 = arena.data(self_id, vec![v0]);
        let tree_at_2 = arena.data(self_id, vec![v2]);
        let decl = InductiveDecl {
            params: vec![ParamDecl {
                mult: Multiplicity::Zero,
                ty: u0,
            }],
            level: Level::zero(),
            ctors: vec![
                CtorDecl {
                    fields: Vec::new(),
                    boundary: None,
                },
                CtorDecl {
                    fields: vec![
                        FieldDecl {
                            mult: Multiplicity::One,
                            ty: tree_at_0,
                            is_recursive: false,
                        },
                        FieldDecl {
                            mult: Multiplicity::One,
                            ty: v1,
                            is_recursive: false,
                        },
                        FieldDecl {
                            mult: Multiplicity::One,
                            ty: tree_at_2,
                            is_recursive: false,
                        },
                    ],
                    boundary: None,
                },
            ],
        };
        let res = check_and_define_inductive(arena, decl);
        assert!(res.is_ok(), "Tree definition failed: {:?}", res.err());
        res.unwrap_or(InductiveId(0))
    }

    #[test]
    fn checks_option_point_empty_and_erased_proof_fields() {
        let mut arena = TermArena::new();
        let opt_id = define_option(&mut arena);
        let u0 = arena.universe(Level::zero());
        let v0 = arena.var(Index(0));
        let v1 = arena.var(Index(1));
        let v2 = arena.var(Index(2));
        let v3 = arena.var(Index(3));

        let opt_v0 = arena.data(opt_id, vec![v0]);
        let ty_inner = arena.pi(Multiplicity::Many, v1, v2);
        let ty_mid = arena.pi(Multiplicity::One, opt_v0, ty_inner);
        let ty = arena.pi(Multiplicity::Zero, u0, ty_mid);
        let elim = arena.data_elim(opt_id, vec![v2], v3, vec![v0, v0], v1);
        let lam_d = arena.lam(Multiplicity::Many, elim);
        let lam_o = arena.lam(Multiplicity::One, lam_d);
        let body = arena.lam(Multiplicity::Zero, lam_o);
        assert_eq!(check_closed(&arena, body, ty), Ok(()));

        let pt_decl = InductiveDecl {
            params: vec![ParamDecl {
                mult: Multiplicity::Zero,
                ty: u0,
            }],
            level: Level::zero(),
            ctors: vec![CtorDecl {
                fields: vec![
                    FieldDecl {
                        mult: Multiplicity::One,
                        ty: v0,
                        is_recursive: false,
                    },
                    FieldDecl {
                        mult: Multiplicity::One,
                        ty: v1,
                        is_recursive: false,
                    },
                ],
                boundary: None,
            }],
        };
        let pt_id = check_and_define_inductive(&mut arena, pt_decl).unwrap_or(InductiveId(0));
        let pt_v0 = arena.data(pt_id, vec![v0]);
        let pt_v1 = arena.data(pt_id, vec![v1]);
        let pt_v2 = arena.data(pt_id, vec![v2]);
        let swap_inner = arena.pi(Multiplicity::One, pt_v0, pt_v1);
        let swap_ty = arena.pi(Multiplicity::Zero, u0, swap_inner);
        let mk_swapped = arena.ctor(pt_id, 0, vec![v3], vec![v0, v1]);
        let swap_elim = arena.data_elim(pt_id, vec![v1], pt_v2, vec![mk_swapped], v0);
        let swap_lam = arena.lam(Multiplicity::One, swap_elim);
        let swap_body = arena.lam(Multiplicity::Zero, swap_lam);
        assert_eq!(check_closed(&arena, swap_body, swap_ty), Ok(()));

        let drop_inner = arena.pi(Multiplicity::One, pt_v0, v1);
        let bad_drop_ty = arena.pi(Multiplicity::Zero, u0, drop_inner);
        let drop_elim = arena.data_elim(pt_id, vec![v1], v2, vec![v1], v0);
        let drop_lam = arena.lam(Multiplicity::One, drop_elim);
        let bad_drop = arena.lam(Multiplicity::Zero, drop_lam);
        assert_eq!(
            check_closed(&arena, bad_drop, bad_drop_ty),
            Err(TypeError::BinderUsageViolation {
                used: Multiplicity::Zero,
                expected: Multiplicity::One,
            })
        );

        let empty_id = check_and_define_inductive(
            &mut arena,
            InductiveDecl {
                params: Vec::new(),
                level: Level::zero(),
                ctors: Vec::new(),
            },
        )
        .unwrap_or(InductiveId(0));
        let empty_ty = arena.data(empty_id, Vec::new());
        let abs_inner = arena.pi(Multiplicity::One, empty_ty, v1);
        let absurd_ty = arena.pi(Multiplicity::Zero, u0, abs_inner);
        let abs_elim = arena.data_elim(empty_id, Vec::new(), v2, Vec::new(), v0);
        let abs_lam = arena.lam(Multiplicity::One, abs_elim);
        let absurd_body = arena.lam(Multiplicity::Zero, abs_lam);
        assert_eq!(check_closed(&arena, absurd_body, absurd_ty), Ok(()));

        let d0 = arena.dim_zero();
        let d1 = arena.dim_one();
        let env1 = vec![Value::var(DeBruijnLevel(0))];
        let coerced = arena.coe(empty_ty, d0, d1, v0);
        assert_eq!(
            eval(&arena, &env1, coerced).and_then(|v| quote(&mut arena, 1, &v)),
            Ok(v0)
        );
    }

    #[test]
    fn checks_erased_proof_field_and_tree_double_recursion() {
        let mut arena = TermArena::new();
        let tree_id = define_tree(&mut arena);
        let nat = arena.nat();
        let zero = arena.zero();
        let one = arena.succ(zero);
        let two = arena.succ(one);
        let three = arena.succ(two);
        let v0 = arena.var(Index(0));
        let v1 = arena.var(Index(1));
        let v3 = arena.var(Index(3));

        let path_xx = arena.path(nat, v0, v0);
        let refined_id = check_and_define_inductive(
            &mut arena,
            InductiveDecl {
                params: Vec::new(),
                level: Level::zero(),
                ctors: vec![CtorDecl {
                    fields: vec![
                        FieldDecl {
                            mult: Multiplicity::One,
                            ty: nat,
                            is_recursive: false,
                        },
                        FieldDecl {
                            mult: Multiplicity::Zero,
                            ty: path_xx,
                            is_recursive: false,
                        },
                    ],
                    boundary: None,
                }],
            },
        )
        .unwrap_or(InductiveId(0));
        let refined_ty = arena.data(refined_id, Vec::new());
        let refl_zero = arena.plam(zero);
        let refined_val = arena.ctor(refined_id, 0, Vec::new(), vec![zero, refl_zero]);
        assert_eq!(check_closed(&arena, refined_val, refined_ty), Ok(()));

        let add_fn = {
            let add_inner = arena.pi(Multiplicity::One, nat, nat);
            let add_ty = arena.pi(Multiplicity::One, nat, add_inner);
            let succ_v0 = arena.succ(v0);
            let add_elim = arena.nat_elim(nat, v0, succ_v0, v1);
            let add_lam = arena.lam(Multiplicity::One, add_elim);
            let add_body = arena.lam(Multiplicity::One, add_lam);
            arena.ann(add_body, add_ty)
        };
        let tree_nat = arena.data(tree_id, vec![nat]);
        let sum_ty = arena.pi(Multiplicity::One, tree_nat, nat);
        let add_v1 = arena.app(add_fn, v1);
        let sum_children = arena.app(add_v1, v0);
        let add_v3 = arena.app(add_fn, v3);
        let sum_node = arena.app(add_v3, sum_children);
        let sum_elim = arena.data_elim(tree_id, vec![nat], nat, vec![zero, sum_node], v0);
        let sum_body = arena.lam(Multiplicity::One, sum_elim);
        assert_eq!(check_closed(&arena, sum_body, sum_ty), Ok(()));

        let leaf = arena.ctor(tree_id, 0, vec![nat], Vec::new());
        let right = arena.ctor(tree_id, 1, vec![nat], vec![leaf, two, leaf]);
        let root = arena.ctor(tree_id, 1, vec![nat], vec![leaf, one, right]);
        let sum_ann = arena.ann(sum_body, sum_ty);
        let call_sum = arena.app(sum_ann, root);
        assert_eq!(
            eval(&arena, &[], call_sum).and_then(|v| quote(&mut arena, 0, &v)),
            Ok(three)
        );
    }

    #[test]
    fn checks_list_append_cubical_induction_and_linear_rejection() {
        let mut arena = TermArena::new();
        let list_id = define_list(&mut arena);
        let u0 = arena.universe(Level::zero());
        let nat = arena.nat();
        let zero = arena.zero();
        let one = arena.succ(zero);
        let v0 = arena.var(Index(0));
        let v1 = arena.var(Index(1));
        let v2 = arena.var(Index(2));
        let v3 = arena.var(Index(3));
        let v5 = arena.var(Index(5));

        let list_v0 = arena.data(list_id, vec![v0]);
        let list_v1 = arena.data(list_id, vec![v1]);
        let list_v2 = arena.data(list_id, vec![v2]);
        let list_v3 = arena.data(list_id, vec![v3]);
        let app_pi_tail = arena.pi(Multiplicity::Many, list_v1, list_v2);
        let app_pi_head = arena.pi(Multiplicity::One, list_v0, app_pi_tail);
        let append_ty = arena.pi(Multiplicity::Zero, u0, app_pi_head);
        let cons_branch = arena.ctor(list_id, 1, vec![v5], vec![v2, v0]);
        let app_elim = arena.data_elim(list_id, vec![v2], list_v3, vec![v0, cons_branch], v1);
        let app_lam_tail = arena.lam(Multiplicity::Many, app_elim);
        let app_lam_head = arena.lam(Multiplicity::One, app_lam_tail);
        let append_body = arena.lam(Multiplicity::Zero, app_lam_head);
        assert_eq!(check_closed(&arena, append_body, append_ty), Ok(()));

        let append_ann = arena.ann(append_body, append_ty);
        let nil_nat = arena.ctor(list_id, 0, vec![nat], Vec::new());
        let xs_zero = arena.ctor(list_id, 1, vec![nat], vec![zero, nil_nat]);
        let xs_one = arena.ctor(list_id, 1, vec![nat], vec![one, nil_nat]);
        let xs_pair = arena.ctor(list_id, 1, vec![nat], vec![zero, xs_one]);
        let app_nat = arena.app(append_ann, nat);
        let app_xs = arena.app(app_nat, xs_zero);
        let app_both = arena.app(app_xs, xs_one);
        assert_eq!(
            eval(&arena, &[], app_both).and_then(|v| quote(&mut arena, 0, &v)),
            Ok(xs_pair)
        );

        let nil_v1 = arena.ctor(list_id, 0, vec![v1], Vec::new());
        let app_v1 = arena.app(append_ann, v1);
        let app_v1_v0 = arena.app(app_v1, v0);
        let lhs_ty = arena.app(app_v1_v0, nil_v1);
        let path_ty = arena.path(list_v2, lhs_ty, v0);
        let thm_inner = arena.pi(Multiplicity::Zero, list_v0, path_ty);
        let thm_ty = arena.pi(Multiplicity::Zero, u0, thm_inner);
        let nil_v2 = arena.ctor(list_id, 0, vec![v2], Vec::new());
        let m_app1 = arena.app(append_ann, v2);
        let m_app2 = arena.app(m_app1, v0);
        let motive_lhs = arena.app(m_app2, nil_v2);
        let motive = arena.path(list_v3, motive_lhs, v0);
        let nil_proof = arena.plam(nil_v2);
        let nil_v5 = arena.ctor(list_id, 0, vec![v5], Vec::new());
        let p_app1 = arena.app(append_ann, v5);
        let p_app2 = arena.app(p_app1, v2);
        let p_left = arena.app(p_app2, nil_v5);
        let ih_at_i = arena.papp(v1, p_left, v2, v0);
        let cons_inner = arena.ctor(list_id, 1, vec![v5], vec![v3, ih_at_i]);
        let cons_proof = arena.plam(cons_inner);
        let thm_elim = arena.data_elim(list_id, vec![v1], motive, vec![nil_proof, cons_proof], v0);
        let thm_lam = arena.lam(Multiplicity::Zero, thm_elim);
        let thm_body = arena.lam(Multiplicity::Zero, thm_lam);
        assert_eq!(check_closed(&arena, thm_body, thm_ty), Ok(()));

        let dup_app1 = arena.app(append_ann, v5);
        let dup_app2 = arena.app(dup_app1, v1);
        let dup_app3 = arena.app(dup_app2, v0);
        let bad_dup_branch = arena.ctor(list_id, 1, vec![v5], vec![v2, dup_app3]);
        let dup_elim = arena.data_elim(list_id, vec![v2], list_v3, vec![v0, bad_dup_branch], v1);
        let dup_lam_tail = arena.lam(Multiplicity::Many, dup_elim);
        let dup_lam_head = arena.lam(Multiplicity::One, dup_lam_tail);
        let bad_dup = arena.lam(Multiplicity::Zero, dup_lam_head);
        assert_eq!(
            check_closed(&arena, bad_dup, append_ty),
            Err(TypeError::BinderUsageViolation {
                used: Multiplicity::Many,
                expected: Multiplicity::One,
            })
        );
    }

    #[test]
    fn rejects_non_strictly_positive_and_bad_universes_with_rollback() {
        let mut arena = TermArena::new();
        let u0 = arena.universe(Level::zero());
        let u1 = arena.universe(Level::zero().succ());
        let void = arena.void();
        let v0 = arena.var(Index(0));

        // Negative occurrence: enum Bad { Mk((1 _: Bad) -> Void) }
        let bad_id = arena.next_inductive_id();
        let bad_ref = arena.data(bad_id, Vec::new());
        let neg_field = arena.pi(Multiplicity::One, bad_ref, void);
        let res_neg = check_and_define_inductive(
            &mut arena,
            InductiveDecl {
                params: Vec::new(),
                level: Level::zero(),
                ctors: vec![CtorDecl {
                    fields: vec![FieldDecl {
                        mult: Multiplicity::One,
                        ty: neg_field,
                        is_recursive: false,
                    }],
                    boundary: None,
                }],
            },
        );
        assert_eq!(res_neg, Err(TypeError::NonStrictlyPositive));
        assert_eq!(arena.inductive_count(), 0);

        // Disguised beta-redex negative occurrence: (|0 X| (1 _: X) -> Void)(Bad)
        let neg_pi = arena.pi(Multiplicity::One, v0, void);
        let lam_neg = arena.lam(Multiplicity::Zero, neg_pi);
        let lam_ty = arena.pi(Multiplicity::Zero, u0, u0);
        let ann_lam = arena.ann(lam_neg, lam_ty);
        let disguised = arena.app(ann_lam, bad_ref);
        let res_disguised = check_and_define_inductive(
            &mut arena,
            InductiveDecl {
                params: Vec::new(),
                level: Level::zero(),
                ctors: vec![CtorDecl {
                    fields: vec![FieldDecl {
                        mult: Multiplicity::One,
                        ty: disguised,
                        is_recursive: false,
                    }],
                    boundary: None,
                }],
            },
        );
        assert_eq!(res_disguised, Err(TypeError::NonStrictlyPositive));
        assert_eq!(arena.inductive_count(), 0);

        // Universe too high: Type 0 field (which lives in Type 1) inside Type 0 inductive
        let res_lvl = check_and_define_inductive(
            &mut arena,
            InductiveDecl {
                params: Vec::new(),
                level: Level::zero(),
                ctors: vec![CtorDecl {
                    fields: vec![FieldDecl {
                        mult: Multiplicity::One,
                        ty: u0,
                        is_recursive: false,
                    }],
                    boundary: None,
                }],
            },
        );
        assert_eq!(res_lvl, Err(TypeError::UniverseLevelTooHigh));
        assert_eq!(arena.inductive_count(), 0);
        let _ = u1;
    }

    #[test]
    fn reports_inductive_errors_and_accepts_higher_universe() {
        let mut arena = TermArena::new();
        let u0 = arena.universe(Level::zero());
        let ok_u1 = check_and_define_inductive(
            &mut arena,
            InductiveDecl {
                params: Vec::new(),
                level: Level::zero().succ(),
                ctors: vec![CtorDecl {
                    fields: vec![FieldDecl {
                        mult: Multiplicity::Zero,
                        ty: u0,
                        is_recursive: false,
                    }],
                    boundary: None,
                }],
            },
        );
        assert!(ok_u1.is_ok());
        assert_eq!(arena.inductive_count(), 1);

        let unknown = InductiveId(99);
        let bad_data = arena.data(unknown, Vec::new());
        assert_eq!(
            check_closed(&arena, bad_data, u0),
            Err(TypeError::InvalidInductiveId(unknown))
        );
        let bad_ctor = arena.ctor(InductiveId(0), 5, Vec::new(), Vec::new());
        assert_eq!(
            check_closed(&arena, bad_ctor, u0),
            Err(TypeError::InvalidCtorIndex {
                id: InductiveId(0),
                ctor: 5,
            })
        );
        let bad_arity = arena.data(InductiveId(0), vec![u0]);
        assert_eq!(
            check_closed(&arena, bad_arity, u0),
            Err(TypeError::ArityMismatch {
                expected: 0,
                actual: 1,
            })
        );
        assert!(term_mentions_inductive(&arena, bad_data, unknown));
        assert!(!term_mentions_inductive(&arena, u0, unknown));
        assert_eq!(unknown.to_string(), "data#99");
        for err in [
            TypeError::InvalidInductiveId(unknown),
            TypeError::InvalidCtorIndex {
                id: unknown,
                ctor: 2,
            },
            TypeError::ArityMismatch {
                expected: 1,
                actual: 2,
            },
            TypeError::NonStrictlyPositive,
            TypeError::UniverseLevelTooHigh,
        ] {
            assert_ne!(err.to_string(), "");
        }
    }

    #[test]
    fn quotes_formats_and_converts_data_terms_at_depth() {
        let mut arena = TermArena::new();
        let opt_id = define_option(&mut arena);
        let list_id = define_list(&mut arena);
        let nat = arena.nat();
        let zero = arena.zero();
        let one = arena.succ(zero);
        let v0 = arena.var(Index(0));
        let v1 = arena.var(Index(1));
        let v2 = arena.var(Index(2));
        let v3 = arena.var(Index(3));

        let opt_nat = arena.data(opt_id, vec![nat]);
        let some_0 = arena.ctor(opt_id, 1, vec![nat], vec![zero]);
        let some_1 = arena.ctor(opt_id, 1, vec![nat], vec![one]);
        let none_nat = arena.ctor(opt_id, 0, vec![nat], Vec::new());
        assert!(arena.format_term(opt_nat).contains("data#0"));
        assert!(arena.format_term(some_0).contains("c1"));

        let env3 = vec![
            Value::var(DeBruijnLevel(0)),
            Value::var(DeBruijnLevel(1)),
            Value::var(DeBruijnLevel(2)),
        ];
        let dep_motive = arena.app(v3, v0);
        let alt_motive = arena.app(v3, v1);
        let elim_a = arena.data_elim(opt_id, vec![v2], dep_motive, vec![zero, v0], v0);
        let elim_diff_s = arena.data_elim(opt_id, vec![v2], dep_motive, vec![zero, v0], v1);
        let elim_diff_p = arena.data_elim(opt_id, vec![v1], dep_motive, vec![zero, v0], v0);
        let elim_diff_m = arena.data_elim(opt_id, vec![v2], alt_motive, vec![zero, v0], v0);
        let elim_diff_b = arena.data_elim(opt_id, vec![v2], dep_motive, vec![one, v0], v0);
        assert!(arena.format_term(elim_a).contains("data_elim"));

        let val_a = eval(&arena, &env3, elim_a);
        assert!(val_a.is_ok());
        if let Ok(va) = val_a {
            assert_eq!(quote(&mut arena, 3, &va), Ok(elim_a));
            assert_eq!(conv(&arena, 3, &va, &va), Ok(true));
            for other in [elim_diff_s, elim_diff_p, elim_diff_m, elim_diff_b] {
                if let Ok(vb) = eval(&arena, &env3, other) {
                    assert_eq!(conv(&arena, 3, &va, &vb), Ok(false));
                }
            }
        }

        // Test Ctor conversion (equal, diff ctor, diff args, diff id)
        let nil_nat = arena.ctor(list_id, 0, vec![nat], Vec::new());
        let pairs: &[(TermId, TermId, bool)] = &[
            (some_0, some_0, true),
            (some_0, some_1, false),
            (some_0, none_nat, false),
            (none_nat, nil_nat, false),
        ];
        for &(lhs, rhs, expected) in pairs {
            if let (Ok(vl), Ok(vr)) = (eval(&arena, &[], lhs), eval(&arena, &[], rhs)) {
                assert_eq!(conv(&arena, 0, &vl, &vr), Ok(expected));
            }
        }
    }

    #[test]
    fn mentions_and_uniform_rec_checks_handle_all_data_and_hcom_forms() {
        use crate::term::CofTerm;

        let mut arena = TermArena::new();
        let opt_id = define_option(&mut arena);
        let u0 = arena.universe(Level::constant(0));
        let nat = arena.nat();
        let zero = arena.zero();
        let v0 = arena.var(Index(0));

        // Wrapper(0 A: Type 0) { Wrap(1 x: Option(A)) } shares param_count == 1 with Option,
        // but must NOT be marked as a recursive self-reference.
        let opt_a = arena.data(opt_id, vec![v0]);
        let wrap_id = check_and_define_inductive(
            &mut arena,
            InductiveDecl {
                params: vec![ParamDecl {
                    mult: Multiplicity::Zero,
                    ty: u0,
                }],
                level: Level::constant(0),
                ctors: vec![CtorDecl {
                    fields: vec![FieldDecl {
                        mult: Multiplicity::One,
                        ty: opt_a,
                        is_recursive: false,
                    }],
                    boundary: None,
                }],
            },
        );
        assert!(wrap_id.is_ok());
        if let Ok(wid) = wrap_id {
            let decl = arena.get_inductive(wid);
            assert!(decl.is_some());
            if let Some(d) = decl {
                assert!(!d.ctors[0].fields[0].is_recursive);
            }
        }

        let target = InductiveId(7);
        let other = InductiveId(8);
        let t_data = arena.data(target, Vec::new());

        // Term::Ctor cases: self id, in params, in args, and none.
        let c_self = arena.ctor(target, 0, Vec::new(), Vec::new());
        let c_param = arena.ctor(other, 0, vec![t_data], Vec::new());
        let c_arg = arena.ctor(other, 0, Vec::new(), vec![t_data]);
        let c_none = arena.ctor(other, 0, vec![nat], vec![zero]);
        assert!(term_mentions_inductive(&arena, c_self, target));
        assert!(term_mentions_inductive(&arena, c_param, target));
        assert!(term_mentions_inductive(&arena, c_arg, target));
        assert!(!term_mentions_inductive(&arena, c_none, target));

        let d_param = arena.data(other, vec![t_data]);
        let d_none = arena.data(other, vec![nat]);
        assert!(term_mentions_inductive(&arena, d_param, target));
        assert!(!term_mentions_inductive(&arena, d_none, target));

        // Term::DataElim cases: self id, in motive, in params, in branches, and none.
        let e_self = arena.data_elim(target, Vec::new(), nat, Vec::new(), zero);
        let e_mot = arena.data_elim(other, Vec::new(), t_data, Vec::new(), zero);
        let e_par = arena.data_elim(other, vec![t_data], nat, Vec::new(), zero);
        let e_br = arena.data_elim(other, Vec::new(), nat, vec![t_data], zero);
        let e_none = arena.data_elim(other, vec![nat], nat, vec![zero], zero);
        assert!(term_mentions_inductive(&arena, e_self, target));
        assert!(term_mentions_inductive(&arena, e_mot, target));
        assert!(term_mentions_inductive(&arena, e_par, target));
        assert!(term_mentions_inductive(&arena, e_br, target));
        assert!(!term_mentions_inductive(&arena, e_none, target));

        // Term::HCom cases: mention in ty only vs in tube branch only.
        let d0 = arena.dim_zero();
        let d1 = arena.dim_one();
        let h_ty = arena.hcom(t_data, d0, d1, Vec::new(), zero);
        let h_tube = arena.hcom(nat, d0, d1, vec![(CofTerm::Top, t_data)], zero);
        let h_none = arena.hcom(nat, d0, d1, vec![(CofTerm::Top, zero)], zero);
        assert!(term_mentions_inductive(&arena, h_ty, target));
        assert!(term_mentions_inductive(&arena, h_tube, target));
        assert!(!term_mentions_inductive(&arena, h_none, target));
    }

    #[test]
    fn checks_circle_s1_upair_and_rejects_bad_hit_boundaries() {
        let mut arena = TermArena::new();
        let u0 = arena.universe(Level::zero());
        let bool_ty = arena.bool_ty();
        let b_true = arena.bool_true();
        let b_false = arena.bool_false();
        let d0 = arena.dim_zero();
        let d1 = arena.dim_one();
        let v0 = arena.var(Index(0));
        let v1 = arena.var(Index(1));
        let v2 = arena.var(Index(2));

        // Circle S1 { Base, Loop(<i>) = Base .. Base }
        let s1_id = arena.next_inductive_id();
        let s1_base = arena.ctor(s1_id, 0, Vec::new(), Vec::new());
        let s1_res = check_and_define_inductive(
            &mut arena,
            InductiveDecl {
                params: Vec::new(),
                level: Level::zero(),
                ctors: vec![
                    CtorDecl {
                        fields: Vec::new(),
                        boundary: None,
                    },
                    CtorDecl {
                        fields: Vec::new(),
                        boundary: Some(PathBoundary {
                            left: s1_base,
                            right: s1_base,
                        }),
                    },
                ],
            },
        );
        assert_eq!(s1_res, Ok(s1_id));
        let s1_ty = arena.data(s1_id, Vec::new());

        let loop_i = arena.ctor(s1_id, 1, Vec::new(), vec![v0]);
        let loop_path = arena.plam(loop_i);
        let loop_ty = arena.path(s1_ty, s1_base, s1_base);
        assert_eq!(check_closed(&arena, loop_path, loop_ty), Ok(()));

        // Loop(0) == Base, Loop(1) == Base; missing dim arg fails arity check.
        let loop_0 = arena.ctor(s1_id, 1, Vec::new(), vec![d0]);
        let loop_1 = arena.ctor(s1_id, 1, Vec::new(), vec![d1]);
        assert_eq!(
            eval(&arena, &[], loop_0).and_then(|v| quote(&mut arena, 0, &v)),
            Ok(s1_base)
        );
        assert_eq!(
            eval(&arena, &[], loop_1).and_then(|v| quote(&mut arena, 0, &v)),
            Ok(s1_base)
        );
        let bad_loop_arity = arena.ctor(s1_id, 1, Vec::new(), Vec::new());
        assert_eq!(
            check_closed(&arena, bad_loop_arity, s1_ty),
            Err(TypeError::ArityMismatch {
                expected: 1,
                actual: 0,
            })
        );

        // S1 eliminator: coherent passes, incoherent fails with HitBoundaryMismatch.
        let s1_to_bool = arena.pi(Multiplicity::One, s1_ty, bool_ty);
        let ok_elim = arena.data_elim(s1_id, Vec::new(), bool_ty, vec![b_true, b_true], v0);
        let ok_fn = arena.lam(Multiplicity::One, ok_elim);
        assert_eq!(check_closed(&arena, ok_fn, s1_to_bool), Ok(()));

        let bad_elim = arena.data_elim(s1_id, Vec::new(), bool_ty, vec![b_true, b_false], v0);
        let bad_fn = arena.lam(Multiplicity::One, bad_elim);
        assert_eq!(
            check_closed(&arena, bad_fn, s1_to_bool),
            Err(TypeError::HitBoundaryMismatch)
        );

        // Neutral HIT eliminator quote & conv with dim-using Loop branch (Path(Bool, true, true) @ i).
        let refl_true = arena.plam(b_true);
        let papp_i = arena.papp(refl_true, b_true, b_true, v0);
        let neu_elim = arena.data_elim(s1_id, Vec::new(), bool_ty, vec![b_true, papp_i], v0);
        let env1 = vec![Value::var(DeBruijnLevel(0))];
        if let Ok(v_neu) = eval(&arena, &env1, neu_elim) {
            assert!(quote(&mut arena, 1, &v_neu).is_ok());
            assert_eq!(conv(&arena, 1, &v_neu, &v_neu), Ok(true));
        }

        // Cyclic boundary in left or right must be rejected and rolled back.
        let bad_hit_id = arena.next_inductive_id();
        let bad_b = arena.ctor(bad_hit_id, 0, Vec::new(), Vec::new());
        let bad_l = arena.ctor(bad_hit_id, 1, Vec::new(), vec![d0]);
        for (l, r) in [(bad_l, bad_b), (bad_b, bad_l)] {
            let cyc = check_and_define_inductive(
                &mut arena,
                InductiveDecl {
                    params: Vec::new(),
                    level: Level::zero(),
                    ctors: vec![
                        CtorDecl {
                            fields: Vec::new(),
                            boundary: None,
                        },
                        CtorDecl {
                            fields: Vec::new(),
                            boundary: Some(PathBoundary { left: l, right: r }),
                        },
                    ],
                },
            );
            assert_eq!(cyc, Err(TypeError::HitBoundaryMismatch));
            assert_eq!(arena.next_inductive_id(), bad_hit_id);
        }
        assert_ne!(TypeError::HitBoundaryMismatch.to_string(), "");
        let _ = (u0, v1, v2);
    }

    #[test]
    fn checks_upair_asymmetry_rejection() {
        let mut arena = TermArena::new();
        let u0 = arena.universe(Level::zero());
        let bool_ty = arena.bool_ty();
        let v0 = arena.var(Index(0));
        let v1 = arena.var(Index(1));
        let v2 = arena.var(Index(2));

        // UPair(0 A: Type 0) { Pair(1 a: A, 1 b: A), Swap(1 a: A, 1 b: A, <i>) = Pair(a, b) .. Pair(b, a) }
        let up_id = arena.next_inductive_id();
        let pair_ab = arena.ctor(up_id, 0, vec![v2], vec![v1, v0]);
        let pair_ba = arena.ctor(up_id, 0, vec![v2], vec![v0, v1]);
        let up_res = check_and_define_inductive(
            &mut arena,
            InductiveDecl {
                params: vec![ParamDecl {
                    mult: Multiplicity::Zero,
                    ty: u0,
                }],
                level: Level::zero(),
                ctors: vec![
                    CtorDecl {
                        fields: vec![
                            FieldDecl {
                                mult: Multiplicity::Many,
                                ty: v0,
                                is_recursive: false,
                            },
                            FieldDecl {
                                mult: Multiplicity::Many,
                                ty: v1,
                                is_recursive: false,
                            },
                        ],
                        boundary: None,
                    },
                    CtorDecl {
                        fields: vec![
                            FieldDecl {
                                mult: Multiplicity::Many,
                                ty: v0,
                                is_recursive: false,
                            },
                            FieldDecl {
                                mult: Multiplicity::Many,
                                ty: v1,
                                is_recursive: false,
                            },
                        ],
                        boundary: Some(PathBoundary {
                            left: pair_ab,
                            right: pair_ba,
                        }),
                    },
                ],
            },
        );
        assert_eq!(up_res, Ok(up_id));

        // Asymmetric projection fails on right endpoint (Swap => a) and left endpoint (Swap => b).
        let up_bool = arena.data(up_id, vec![bool_ty]);
        let up_fn_ty = arena.pi(Multiplicity::One, up_bool, bool_ty);
        for swap_body in [v2, v1] {
            let asym = arena.data_elim(up_id, vec![bool_ty], bool_ty, vec![v1, swap_body], v0);
            let asym_lam = arena.lam(Multiplicity::One, asym);
            assert_eq!(
                check_closed(&arena, asym_lam, up_fn_ty),
                Err(TypeError::HitBoundaryMismatch)
            );
        }
    }

    #[test]
    fn checks_recursive_truncation_hit_eliminator() {
        let mut arena = TermArena::new();
        let u0 = arena.universe(Level::zero());
        let v0 = arena.var(Index(0));
        let v1 = arena.var(Index(1));
        let v2 = arena.var(Index(2));
        let v3 = arena.var(Index(3));
        let v4 = arena.var(Index(4));
        let v6 = arena.var(Index(6));

        // Recursive HIT: Trunc(0 A: Type 0) { In(1 x: A), Squash(1 x: Trunc(A), 1 y: Trunc(A), <i>) = x .. y }
        let tr_id = arena.next_inductive_id();
        let tr_v0 = arena.data(tr_id, vec![v0]);
        let tr_v1 = arena.data(tr_id, vec![v1]);
        let tr_res = check_and_define_inductive(
            &mut arena,
            InductiveDecl {
                params: vec![ParamDecl {
                    mult: Multiplicity::Zero,
                    ty: u0,
                }],
                level: Level::zero(),
                ctors: vec![
                    CtorDecl {
                        fields: vec![FieldDecl {
                            mult: Multiplicity::One,
                            ty: v0,
                            is_recursive: false,
                        }],
                        boundary: None,
                    },
                    CtorDecl {
                        fields: vec![
                            FieldDecl {
                                mult: Multiplicity::One,
                                ty: tr_v0,
                                is_recursive: false,
                            },
                            FieldDecl {
                                mult: Multiplicity::One,
                                ty: tr_v1,
                                is_recursive: false,
                            },
                        ],
                        boundary: Some(PathBoundary {
                            left: v1,
                            right: v0,
                        }),
                    },
                ],
            },
        );
        assert_eq!(tr_res, Ok(tr_id));

        // trunc_rec: (0 A, 0 B, 1 f: (1 _: A) -> B, 0 p: (0 x: B, 0 y: B) -> Path(_ => B, x, y), 1 t: Trunc(A)) -> B
        let tr_a = arena.data(tr_id, vec![v3]);
        let b_path = arena.path(v4, v1, v0);
        let p_inner = arena.pi(Multiplicity::Zero, v2, b_path);
        let p_ty = arena.pi(Multiplicity::Zero, v1, p_inner);
        let f_ty = arena.pi(Multiplicity::One, v1, v1);
        let rec_ty_t = arena.pi(Multiplicity::One, tr_a, v3);
        let rec_ty_p = arena.pi(Multiplicity::Zero, p_ty, rec_ty_t);
        let rec_ty_f = arena.pi(Multiplicity::One, f_ty, rec_ty_p);
        let rec_ty_b = arena.pi(Multiplicity::Zero, u0, rec_ty_f);
        let rec_ty = arena.pi(Multiplicity::Zero, u0, rec_ty_b);

        let in_branch = arena.app(v3, v0);
        let p_ihx = arena.app(v6, v2);
        let p_ihx_ihy = arena.app(p_ihx, v1);
        let sq_branch = arena.papp(p_ihx_ihy, v2, v1, v0);
        let tr_elim = arena.data_elim(tr_id, vec![v4], v4, vec![in_branch, sq_branch], v0);
        let l1 = arena.lam(Multiplicity::One, tr_elim);
        let l2 = arena.lam(Multiplicity::Zero, l1);
        let l3 = arena.lam(Multiplicity::One, l2);
        let l4 = arena.lam(Multiplicity::Zero, l3);
        let rec_body = arena.lam(Multiplicity::Zero, l4);
        assert_eq!(check_closed(&arena, rec_body, rec_ty), Ok(()));
    }
}
