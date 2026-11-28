use std::sync::Arc;

use crate::check::{Ctx, TypeError, check, check_is_type, infer};
use crate::cubical::Dim;
use crate::multiplicity::{Multiplicity, UsageVec};
use crate::nbe::{Env, Value, apply, conv, eval, proj_fst};
use crate::term::{DeBruijnLevel, TermArena, TermId};

fn check_nondep_pi(
    arena: &TermArena,
    depth: u32,
    ty: &Value,
    expected_dom: &Value,
    expected_cod: &Value,
) -> Result<(), TypeError> {
    let Value::Pi {
        domain, codomain, ..
    } = ty
    else {
        return Err(TypeError::InvalidEquivalence);
    };
    if !conv(arena, depth, domain, expected_dom)? {
        return Err(TypeError::InvalidEquivalence);
    }
    let var = Value::var(DeBruijnLevel(depth));
    let cod_val = codomain.apply(arena, var)?;
    if !conv(arena, depth + 1, &cod_val, expected_cod)? {
        return Err(TypeError::InvalidEquivalence);
    }
    Ok(())
}

fn check_inv_path(
    arena: &TermArena,
    depth: u32,
    ty: &Value,
    dom_ty: &Value,
    outer_fn: &Value,
    inner_fn: &Value,
) -> Result<(), TypeError> {
    let Value::Pi {
        domain, codomain, ..
    } = ty
    else {
        return Err(TypeError::InvalidEquivalence);
    };
    if !conv(arena, depth, domain, dom_ty)? {
        return Err(TypeError::InvalidEquivalence);
    }
    let x = Value::var(DeBruijnLevel(depth));
    let cod_val = codomain.apply(arena, x.clone())?;
    let Value::Path {
        family,
        left,
        right,
    } = cod_val
    else {
        return Err(TypeError::InvalidEquivalence);
    };
    let fam_val = family.apply(arena, Value::dim_var(depth + 1))?;
    if !conv(arena, depth + 2, &fam_val, dom_ty)? {
        return Err(TypeError::InvalidEquivalence);
    }
    let inner_x = apply(arena, inner_fn, x.clone())?;
    let roundtrip = apply(arena, outer_fn, inner_x)?;
    if !conv(arena, depth + 1, &left, &roundtrip)? || !conv(arena, depth + 1, &right, &x)? {
        return Err(TypeError::InvalidEquivalence);
    }
    Ok(())
}

fn check_equiv(
    arena: &TermArena,
    depth: u32,
    equiv_ty: &Value,
    ty0: &Value,
    ty1: &Value,
) -> Result<(), TypeError> {
    let Value::Sigma {
        first: f_ty,
        second: rest1,
        ..
    } = equiv_ty
    else {
        return Err(TypeError::InvalidEquivalence);
    };
    check_nondep_pi(arena, depth, f_ty, ty0, ty1)?;

    let f_var = Value::var(DeBruijnLevel(depth));
    let rest1_val = rest1.apply(arena, f_var.clone())?;
    let Value::Sigma {
        first: g_ty,
        second: rest2,
        ..
    } = rest1_val
    else {
        return Err(TypeError::InvalidEquivalence);
    };
    check_nondep_pi(arena, depth + 1, &g_ty, ty1, ty0)?;

    let g_var = Value::var(DeBruijnLevel(depth + 1));
    let rest2_val = rest2.apply(arena, g_var.clone())?;
    let Value::Sigma {
        first: sec_ty,
        second: ret_cl,
        ..
    } = rest2_val
    else {
        return Err(TypeError::InvalidEquivalence);
    };
    check_inv_path(arena, depth + 2, &sec_ty, ty1, &f_var, &g_var)?;

    let sec_var = Value::var(DeBruijnLevel(depth + 2));
    let ret_ty = ret_cl.apply(arena, sec_var)?;
    check_inv_path(arena, depth + 3, &ret_ty, ty0, &g_var, &f_var)
}

impl Ctx {
    pub(crate) fn infer_v_type(
        &mut self,
        arena: &TermArena,
        dim: TermId,
        ty0: TermId,
        ty1: TermId,
        equiv: TermId,
    ) -> Result<(Value, UsageVec), TypeError> {
        let _ = check(arena, self, Multiplicity::Zero, dim, &Value::Interval)?;
        let l0 = check_is_type(arena, self, ty0)?;
        let l1 = check_is_type(arena, self, ty1)?;
        let ty0_val = eval(arena, self.env(), ty0)?;
        let ty1_val = eval(arena, self.env(), ty1)?;
        let (equiv_ty, _) = infer(arena, self, Multiplicity::Zero, equiv)?;
        check_equiv(arena, self.depth(), &equiv_ty, &ty0_val, &ty1_val)?;
        Ok((Value::Universe(l0.max(&l1)), UsageVec::zero(self.len())))
    }

    pub(crate) fn infer_v_proj(
        &mut self,
        arena: &TermArena,
        mode: Multiplicity,
        parts: (TermId, TermId, TermId, TermId, TermId),
    ) -> Result<(Value, UsageVec), TypeError> {
        let (dim, ty0, ty1, equiv, term) = parts;
        let _ = check(arena, self, Multiplicity::Zero, dim, &Value::Interval)?;
        let _ = check_is_type(arena, self, ty0)?;
        let _ = check_is_type(arena, self, ty1)?;
        let ty0_val = eval(arena, self.env(), ty0)?;
        let ty1_val = eval(arena, self.env(), ty1)?;
        let (equiv_ty, _) = infer(arena, self, Multiplicity::Zero, equiv)?;
        check_equiv(arena, self.depth(), &equiv_ty, &ty0_val, &ty1_val)?;

        let v_ty = match eval(arena, self.env(), dim)? {
            Value::Dim(Dim::Zero) => ty0_val,
            Value::Dim(Dim::One) => ty1_val.clone(),
            Value::Dim(d) => Value::VType {
                dim: d,
                ty0: Arc::new(ty0_val),
                ty1: Arc::new(ty1_val.clone()),
                equiv: Arc::new(eval(arena, self.env(), equiv)?),
            },
            _ => return Err(TypeError::TypeMismatch),
        };
        let u_term = check(arena, self, mode, term, &v_ty)?;
        Ok((ty1_val, u_term))
    }

    pub(crate) fn check_v_in(
        &mut self,
        arena: &TermArena,
        mode: Multiplicity,
        dim: TermId,
        left: TermId,
        right: TermId,
        expected: &Value,
    ) -> Result<UsageVec, TypeError> {
        let _ = check(arena, self, Multiplicity::Zero, dim, &Value::Interval)?;
        match eval(arena, self.env(), dim)? {
            Value::Dim(Dim::Zero) => check(arena, self, mode, left, expected),
            Value::Dim(Dim::One) => check(arena, self, mode, right, expected),
            Value::Dim(d @ Dim::Var(_)) => {
                let Value::VType {
                    dim: exp_dim,
                    ty0,
                    ty1,
                    equiv,
                } = expected
                else {
                    return Err(TypeError::TypeMismatch);
                };
                if *exp_dim != d {
                    return Err(TypeError::TypeMismatch);
                }
                let u_left = check(arena, self, mode, left, ty0)?;
                let u_right = check(arena, self, mode, right, ty1)?;

                let env0: Env = self
                    .env()
                    .iter()
                    .map(|v| match v {
                        Value::Dim(ev) if *ev == d => Value::Dim(Dim::Zero),
                        other => other.clone(),
                    })
                    .collect();
                let left_at_0 = eval(arena, &env0, left)?;
                let right_at_0 = eval(arena, &env0, right)?;
                let fwd_left_0 = apply(arena, &proj_fst(equiv), left_at_0)?;
                if !conv(arena, self.depth(), &fwd_left_0, &right_at_0)? {
                    return Err(TypeError::VBoundaryMismatch);
                }
                Ok(u_left.join(&u_right)?)
            }
            _ => Err(TypeError::TypeMismatch),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::check::{TypeError, check_closed, infer_closed};
    use crate::cubical::Dim;
    use crate::inductive::{InductiveId, term_mentions_inductive};
    use crate::level::Level;
    use crate::multiplicity::Multiplicity;
    use crate::nbe::{Closure, TypeLine, Value, coe_line, conv, eval, quote};
    use crate::term::{DeBruijnLevel, Index, TermArena, TermId};

    fn build_equiv_type(arena: &mut TermArena, a: TermId, b: TermId) -> TermId {
        let v0 = arena.var(Index(0));
        let v1 = arena.var(Index(1));
        let v2 = arena.var(Index(2));
        let v3 = arena.var(Index(3));

        // Under f (v3), g (v2), sec (v1), a_x (v0): Path(_ => a, g(f(a_x)), a_x)
        let f_ax = arena.app(v3, v0);
        let gf_ax = arena.app(v2, f_ax);
        let ret_path = arena.path(a, gf_ax, v0);
        let ret_ty = arena.pi(Multiplicity::Zero, a, ret_path);

        // Under f (v2), g (v1), b_x (v0): Path(_ => b, f(g(b_x)), b_x)
        let g_bx = arena.app(v1, v0);
        let fg_bx = arena.app(v2, g_bx);
        let sec_path = arena.path(b, fg_bx, v0);
        let sec_ty = arena.pi(Multiplicity::Zero, b, sec_path);

        let sig_sec = arena.sigma(Multiplicity::Zero, sec_ty, ret_ty);
        let b_to_a = arena.pi(Multiplicity::One, b, a);
        let sig_g = arena.sigma(Multiplicity::Zero, b_to_a, sig_sec);
        let a_to_b = arena.pi(Multiplicity::One, a, b);
        arena.sigma(Multiplicity::Zero, a_to_b, sig_g)
    }

    fn build_not_equiv(arena: &mut TermArena) -> (TermId, TermId) {
        let bool_ty = arena.bool_ty();
        let b_true = arena.bool_true();
        let b_false = arena.bool_false();
        let v0 = arena.var(Index(0));

        let not_body = arena.bool_elim(bool_ty, b_false, b_true, v0);
        let not_fn = arena.lam(Multiplicity::One, not_body);
        let not_ty = arena.pi(Multiplicity::One, bool_ty, bool_ty);
        let not_ann = arena.ann(not_fn, not_ty);

        let not_x = arena.app(not_ann, v0);
        let not_not_x = arena.app(not_ann, not_x);
        let motive = arena.path(bool_ty, not_not_x, v0);
        let refl_true = arena.plam(b_true);
        let refl_false = arena.plam(b_false);
        let inv_body = arena.bool_elim(motive, refl_true, refl_false, v0);
        let inv_proof = arena.lam(Multiplicity::Zero, inv_body);

        let eq_ty = build_equiv_type(arena, bool_ty, bool_ty);
        let p3 = arena.pair(inv_proof, inv_proof);
        let p2 = arena.pair(not_fn, p3);
        let eq_val = arena.pair(not_fn, p2);
        let eq_ann = arena.ann(eq_val, eq_ty);
        (eq_ty, eq_ann)
    }

    #[test]
    fn proves_ua_and_computes_univalence_coercion_and_vproj() {
        let mut arena = TermArena::new();
        let u0 = arena.universe(Level::zero());
        let bool_ty = arena.bool_ty();
        let b_true = arena.bool_true();
        let b_false = arena.bool_false();
        let d0 = arena.dim_zero();
        let d1 = arena.dim_one();
        let v0 = arena.var(Index(0));

        let (eq_ty, not_equiv) = build_not_equiv(&mut arena);
        assert_eq!(check_closed(&arena, not_equiv, eq_ty), Ok(()));

        // ua(not_equiv) = <i> V(i, Bool, Bool, not_equiv) : Path(_ => Type 0, Bool, Bool)
        let v_line = arena.v_type(v0, bool_ty, bool_ty, not_equiv);
        let ua_not = arena.plam(v_line);
        let ua_ty = arena.path(u0, bool_ty, bool_ty);
        assert_eq!(check_closed(&arena, ua_not, ua_ty), Ok(()));

        // Computational univalence: coe(0 -> 1, true) == false and coe(1 -> 0, true) == false.
        let ua_ann = arena.ann(ua_not, ua_ty);
        let line_at_i = arena.papp(ua_ann, bool_ty, bool_ty, v0);
        let coe_fwd = arena.coe(line_at_i, d0, d1, b_true);
        let coe_inv = arena.coe(line_at_i, d1, d0, b_true);
        let fwd_path = arena.path(bool_ty, coe_fwd, b_false);
        let inv_path = arena.path(bool_ty, coe_inv, b_false);
        let refl_false = arena.plam(b_false);
        assert_eq!(check_closed(&arena, refl_false, fwd_path), Ok(()));
        assert_eq!(check_closed(&arena, refl_false, inv_path), Ok(()));

        // Dependent coercion 0 -> i produces vin(i, true, false) : Path(i => ua_not @ i, true, false).
        let coe_dep = arena.coe(line_at_i, d0, v0, b_true);
        let dep_term = arena.plam(coe_dep);
        let dep_type = arena.path(line_at_i, b_true, b_false);
        assert_eq!(check_closed(&arena, dep_term, dep_type), Ok(()));

        // Direct vin introduction & vproj elimination at i, 0, and 1.
        let vin_tm = arena.v_in(v0, b_true, b_false);
        let vin_path = arena.plam(vin_tm);
        assert_eq!(check_closed(&arena, vin_path, dep_type), Ok(()));

        let vp_i = arena.v_proj(v0, bool_ty, bool_ty, not_equiv, vin_tm);
        let vp_path = arena.plam(vp_i);
        let const_false_ty = arena.path(bool_ty, b_false, b_false);
        assert_eq!(check_closed(&arena, vp_path, const_false_ty), Ok(()));

        let vp_0 = arena.v_proj(d0, bool_ty, bool_ty, not_equiv, b_true);
        let vp_1 = arena.v_proj(d1, bool_ty, bool_ty, not_equiv, b_false);
        let vp_0_eq = arena.path(bool_ty, vp_0, b_false);
        let vp_1_eq = arena.path(bool_ty, vp_1, b_false);
        assert_eq!(check_closed(&arena, refl_false, vp_0_eq), Ok(()));
        assert_eq!(check_closed(&arena, refl_false, vp_1_eq), Ok(()));

        // vin at concrete 0 and 1 typechecks against endpoints.
        let vin_0 = arena.v_in(d0, b_true, b_false);
        let vin_1 = arena.v_in(d1, b_true, b_false);
        assert_eq!(check_closed(&arena, vin_0, bool_ty), Ok(()));
        assert_eq!(check_closed(&arena, vin_1, bool_ty), Ok(()));
        assert_eq!(
            infer_closed(&arena, vin_0).err(),
            Some(TypeError::CannotInferVIn)
        );
    }

    #[test]
    fn quotes_converts_formats_and_rejects_invalid_vtypes() {
        let mut arena = TermArena::new();
        let bool_ty = arena.bool_ty();
        let nat = arena.nat();
        let b_true = arena.bool_true();
        let b_false = arena.bool_false();
        let d0 = arena.dim_zero();
        let d1 = arena.dim_one();
        let v0 = arena.var(Index(0));
        let v1 = arena.var(Index(1));

        let (_, not_equiv) = build_not_equiv(&mut arena);

        // VBoundaryMismatch: vin(i, true, true) fails because not(true) = false != true.
        let v_line = arena.v_type(v0, bool_ty, bool_ty, not_equiv);
        let bad_vin = arena.v_in(v0, b_true, b_true);
        let bad_plam = arena.plam(bad_vin);
        let bad_path_ty = arena.path(v_line, b_true, b_true);
        assert_eq!(
            check_closed(&arena, bad_plam, bad_path_ty),
            Err(TypeError::VBoundaryMismatch)
        );

        // TypeMismatch when vin checks against non-VType or mismatched dim.
        let non_v_path = arena.path(bool_ty, b_true, b_false);
        let vin_i = arena.v_in(v0, b_true, b_false);
        let vin_plam = arena.plam(vin_i);
        assert_eq!(
            check_closed(&arena, vin_plam, non_v_path),
            Err(TypeError::TypeMismatch)
        );

        // InvalidEquivalence: non-Sigma, wrong domain, wrong codomain, wrong sec/ret.
        let bad_v1 = arena.v_type(d0, bool_ty, bool_ty, b_true);
        assert_eq!(
            infer_closed(&arena, bad_v1).err(),
            Some(TypeError::InvalidEquivalence)
        );
        let bad_v2 = arena.v_type(d0, nat, bool_ty, not_equiv);
        assert_eq!(
            infer_closed(&arena, bad_v2).err(),
            Some(TypeError::InvalidEquivalence)
        );
        let bad_v3 = arena.v_type(d0, bool_ty, nat, not_equiv);
        assert_eq!(
            infer_closed(&arena, bad_v3).err(),
            Some(TypeError::InvalidEquivalence)
        );

        // Format, mentions, neutral VProj quote/conv, and neutral coe_v_line.
        let vp_neu = arena.v_proj(v1, bool_ty, bool_ty, not_equiv, v0);
        assert!(arena.format_term(v_line).starts_with("V("));
        assert!(arena.format_term(vin_i).starts_with("vin("));
        assert!(arena.format_term(vp_neu).starts_with("vproj("));

        let tid = InductiveId(42);
        let tdata = arena.data(tid, Vec::new());
        let mentions_vtype = arena.v_type(d0, tdata, bool_ty, b_true);
        let mentions_vin = arena.v_in(d0, tdata, b_false);
        let mentions_vproj = arena.v_proj(d0, bool_ty, bool_ty, b_true, tdata);
        assert!(term_mentions_inductive(&arena, mentions_vtype, tid));
        assert!(term_mentions_inductive(&arena, mentions_vin, tid));
        assert!(term_mentions_inductive(&arena, mentions_vproj, tid));

        let fixed_v = arena.v_type(v1, bool_ty, bool_ty, not_equiv);
        let fixed_line = TypeLine::Closure(Closure::new(vec![Value::dim_var(0)], fixed_v));
        let fixed_coe = coe_line(&arena, &fixed_line, Dim::Zero, Dim::One, Value::True);
        assert!(matches!(fixed_coe, Ok(Value::Neutral(_))));
        let ua_line = TypeLine::Closure(Closure::new(Vec::new(), v_line));
        let back_open = coe_line(
            &arena,
            &ua_line,
            Dim::One,
            Dim::Var(crate::cubical::DimVar(0)),
            Value::True,
        );
        assert!(matches!(back_open, Ok(Value::Neutral(_))));
        let _ = d1;

        for err in [
            TypeError::InvalidEquivalence,
            TypeError::VBoundaryMismatch,
            TypeError::CannotInferVIn,
        ] {
            assert_ne!(err.to_string(), "");
        }
    }

    #[test]
    fn quotes_and_distinguishes_vtype_vin_and_vproj_values() {
        let mut arena = TermArena::new();
        let bool_ty = arena.bool_ty();
        let nat = arena.nat();
        let b_true = arena.bool_true();
        let b_false = arena.bool_false();
        let d0 = arena.dim_zero();
        let v0 = arena.var(Index(0));
        let v1 = arena.var(Index(1));
        let v2 = arena.var(Index(2));
        let v3 = arena.var(Index(3));
        let (_, not_equiv) = build_not_equiv(&mut arena);

        let env2 = vec![Value::dim_var(0), Value::var(DeBruijnLevel(1))];
        let open_vtype = arena.v_type(v1, bool_ty, bool_ty, not_equiv);
        let open_vin = arena.v_in(v1, b_true, b_false);
        let vp_neu = arena.v_proj(v1, bool_ty, bool_ty, not_equiv, v0);
        let alt_vtype_dim = arena.v_type(d0, bool_ty, bool_ty, not_equiv);
        let alt_vtype_ty0 = arena.v_type(v1, nat, bool_ty, not_equiv);
        let alt_vtype_ty1 = arena.v_type(v1, bool_ty, nat, not_equiv);
        let alt_vtype_eq = arena.v_type(v1, bool_ty, bool_ty, b_true);
        let alt_vin_left = arena.v_in(v1, b_false, b_false);
        let alt_vin_right = arena.v_in(v1, b_true, b_true);
        let alt_vp_ty0 = arena.v_proj(v1, nat, bool_ty, not_equiv, v0);
        let alt_vp_ty1 = arena.v_proj(v1, bool_ty, nat, not_equiv, v0);
        let alt_vp_eq = arena.v_proj(v1, bool_ty, bool_ty, b_true, v0);
        if let (Ok(vv), Ok(vi), Ok(vp)) = (
            eval(&arena, &env2, open_vtype),
            eval(&arena, &env2, open_vin),
            eval(&arena, &env2, vp_neu),
        ) {
            assert!(quote(&mut arena, 2, &vv).is_ok());
            assert!(quote(&mut arena, 2, &vi).is_ok());
            assert!(quote(&mut arena, 2, &vp).is_ok());
            assert_eq!(conv(&arena, 2, &vv, &vv), Ok(true));
            assert_eq!(conv(&arena, 2, &vi, &vi), Ok(true));
            assert_eq!(conv(&arena, 2, &vp, &vp), Ok(true));
            assert_eq!(conv(&arena, 2, &vv, &vi), Ok(false));
            for alt in [alt_vtype_dim, alt_vtype_ty0, alt_vtype_ty1, alt_vtype_eq] {
                if let Ok(va) = eval(&arena, &env2, alt) {
                    assert_eq!(conv(&arena, 2, &vv, &va), Ok(false));
                }
            }
            for alt in [alt_vin_left, alt_vin_right] {
                if let Ok(va) = eval(&arena, &env2, alt) {
                    assert_eq!(conv(&arena, 2, &vi, &va), Ok(false));
                }
            }
            for alt in [alt_vp_ty0, alt_vp_ty1, alt_vp_eq] {
                if let Ok(va) = eval(&arena, &env2, alt) {
                    assert_eq!(conv(&arena, 2, &vp, &va), Ok(false));
                }
            }
        }

        let env3 = vec![
            Value::dim_var(0),
            Value::dim_var(1),
            Value::var(DeBruijnLevel(2)),
            Value::var(DeBruijnLevel(3)),
        ];
        let vp_a = arena.v_proj(v3, bool_ty, bool_ty, not_equiv, v1);
        let vp_diff_dim = arena.v_proj(v2, bool_ty, bool_ty, not_equiv, v1);
        let vp_diff_tm = arena.v_proj(v3, bool_ty, bool_ty, not_equiv, v0);
        let vin_a = arena.v_in(v3, b_true, b_false);
        let vin_diff_dim = arena.v_in(v2, b_true, b_false);
        if let (Ok(va), Ok(vd), Ok(vt), Ok(via), Ok(vid)) = (
            eval(&arena, &env3, vp_a),
            eval(&arena, &env3, vp_diff_dim),
            eval(&arena, &env3, vp_diff_tm),
            eval(&arena, &env3, vin_a),
            eval(&arena, &env3, vin_diff_dim),
        ) {
            assert_eq!(conv(&arena, 4, &va, &vd), Ok(false));
            assert_eq!(conv(&arena, 4, &va, &vt), Ok(false));
            assert_eq!(conv(&arena, 4, &via, &vid), Ok(false));
        }
    }

    #[test]
    fn rejects_malformed_equivalence_components_and_mismatched_vin_dim() {
        let mut arena = TermArena::new();
        let bool_ty = arena.bool_ty();
        let nat = arena.nat();
        let b_true = arena.bool_true();
        let b_false = arena.bool_false();
        let d0 = arena.dim_zero();
        let v0 = arena.var(Index(0));
        let v1 = arena.var(Index(1));
        let (_, not_equiv) = build_not_equiv(&mut arena);

        // Wrong dim var in vin(i, ...) checked against V(j, ...).
        let vj_ty = arena.v_type(v0, bool_ty, bool_ty, not_equiv);
        let vin_outer = arena.v_in(v1, b_true, b_false);
        let inner_plam = arena.plam(vin_outer);
        let outer_plam = arena.plam(inner_plam);
        let inner_path = arena.path(vj_ty, b_true, b_false);
        let outer_path = arena.path(inner_path, b_true, b_false);
        assert_eq!(
            check_closed(&arena, outer_plam, outer_path),
            Err(TypeError::TypeMismatch)
        );

        let id_bool = arena.lam(Multiplicity::One, v0);
        let id_ty = arena.pi(Multiplicity::One, bool_ty, bool_ty);
        let pair_tt = arena.pair(b_true, b_true);
        let pair_id_t = arena.pair(id_bool, b_true);
        let bad_sig1_ty = arena.sigma(Multiplicity::Zero, bool_ty, bool_ty);
        let bad_sig1 = arena.ann(pair_tt, bad_sig1_ty);
        let bad_sig2_ty = arena.sigma(Multiplicity::Zero, id_ty, bool_ty);
        let bad_sig2 = arena.ann(pair_id_t, bad_sig2_ty);

        let bad_sig3_inner = arena.sigma(Multiplicity::Zero, id_ty, bool_ty);
        let bad_sig3_ty = arena.sigma(Multiplicity::Zero, id_ty, bad_sig3_inner);
        let bad_sig3_outer = arena.pair(id_bool, pair_id_t);
        let bad_sig3 = arena.ann(bad_sig3_outer, bad_sig3_ty);

        let bad_sec_nonpi_in = arena.sigma(Multiplicity::Zero, bool_ty, bool_ty);
        let bad_sec_nonpi_g = arena.sigma(Multiplicity::Zero, id_ty, bad_sec_nonpi_in);
        let bad_sec_nonpi_ty = arena.sigma(Multiplicity::Zero, id_ty, bad_sec_nonpi_g);
        let nonpi_inner = arena.pair(id_bool, pair_tt);
        let nonpi_outer = arena.pair(id_bool, nonpi_inner);
        let bad_sec_nonpi = arena.ann(nonpi_outer, bad_sec_nonpi_ty);

        let bad_sec_dom_pi = arena.pi(Multiplicity::Zero, nat, bool_ty);
        let bad_sec_dom_in = arena.sigma(Multiplicity::Zero, bad_sec_dom_pi, bool_ty);
        let bad_sec_dom_g = arena.sigma(Multiplicity::Zero, id_ty, bad_sec_dom_in);
        let bad_sec_dom_ty = arena.sigma(Multiplicity::Zero, id_ty, bad_sec_dom_g);
        let const_true_nat = arena.lam(Multiplicity::Zero, b_true);
        let p_dom1 = arena.pair(const_true_nat, b_true);
        let p_dom2 = arena.pair(id_bool, p_dom1);
        let p_dom3 = arena.pair(id_bool, p_dom2);
        let bad_sec_dom = arena.ann(p_dom3, bad_sec_dom_ty);

        let bad_sec_cod_in = arena.sigma(Multiplicity::Zero, id_ty, bool_ty);
        let bad_sec_cod_g = arena.sigma(Multiplicity::Zero, id_ty, bad_sec_cod_in);
        let bad_sec_cod_ty = arena.sigma(Multiplicity::Zero, id_ty, bad_sec_cod_g);
        let p_cod2 = arena.pair(id_bool, pair_id_t);
        let p_cod3 = arena.pair(id_bool, p_cod2);
        let bad_sec_cod = arena.ann(p_cod3, bad_sec_cod_ty);

        for bad_eq in [
            bad_sig1,
            bad_sig2,
            bad_sig3,
            bad_sec_nonpi,
            bad_sec_dom,
            bad_sec_cod,
        ] {
            let vt = arena.v_type(d0, bool_ty, bool_ty, bad_eq);
            assert_eq!(
                infer_closed(&arena, vt).err(),
                Some(TypeError::InvalidEquivalence)
            );
        }
    }
}
