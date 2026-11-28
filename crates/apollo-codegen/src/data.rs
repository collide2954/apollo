use std::collections::{BTreeSet, HashMap};

use apollo_elab::CheckedData;
use apollo_kernel::nbe::{Closure, Value, eval};
use apollo_kernel::{InductiveId, Multiplicity, TermArena, TermId};
use apollo_syntax::DataKind;

use crate::escape::escape_ident;
use crate::ir::{
    CaptureMode, RecCapture, RustDataDef, RustDataKind, RustEnumVariant, RustExpr, RustMatchArm,
    RustMatchPat, RustPatBinder, RustRecArm, RustStructField, RustType, collect_local_ids,
};
use crate::{
    Binding, CodegenError, DeclLowerer, LoweredCtorMeta, LoweredDataMeta, is_erased_value_type,
};

type LoweredArm = (
    RustMatchPat,
    Vec<(usize, String, usize, String)>,
    RustExpr,
    BTreeSet<usize>,
);

impl DeclLowerer<'_> {
    pub(crate) fn lower_data_defs(
        arena: &mut TermArena,
        data_decls: &[CheckedData],
    ) -> Result<(Vec<RustDataDef>, Vec<LoweredDataMeta>, bool), CodegenError> {
        let (mut metas, uses_alloc) = collect_initial_metas(arena, data_decls)?;
        let mut defs = Vec::with_capacity(data_decls.len());
        let empty_globals = HashMap::new();

        for (d_idx, data) in data_decls.iter().enumerate() {
            let Some(k_decl) = arena.get_inductive(data.id).cloned() else {
                return Err(CodegenError::InvalidTerm {
                    decl: data.name.clone(),
                });
            };
            let mut lowerer = DeclLowerer::new(arena, &empty_globals, &metas, data.name.clone());
            let mut type_params = Vec::new();
            for (p_decl, raw_name) in k_decl.params.iter().zip(&data.param_names) {
                let p_ty = lowerer.eval_term(p_decl.ty)?;
                if p_decl.mult.is_erased() && matches!(p_ty, Value::Universe(_)) {
                    let tp = escape_ident(raw_name);
                    type_params.push(tp.clone());
                    let _ = lowerer.push_binding(p_ty, Binding::TypeParam(tp));
                } else {
                    let _ = lowerer.push_binding(p_ty, Binding::Erased);
                }
            }
            let (kind, erased_slots) = lower_data_kind(&mut lowerer, data, &k_decl)?;
            for (c_idx, f_idx) in erased_slots {
                if let Some(slot) = metas
                    .get_mut(d_idx)
                    .and_then(|m| m.ctors.get_mut(c_idx))
                    .and_then(|cm| cm.field_keep.get_mut(f_idx))
                {
                    *slot = false;
                }
            }
            defs.push(RustDataDef {
                name: escape_ident(&data.name),
                type_params,
                kind,
            });
        }

        Ok((defs, metas, uses_alloc))
    }
}

fn collect_initial_metas(
    arena: &TermArena,
    data_decls: &[CheckedData],
) -> Result<(Vec<LoweredDataMeta>, bool), CodegenError> {
    let mut metas = Vec::with_capacity(data_decls.len());
    let mut uses_alloc = false;

    for data in data_decls {
        let Some(k_decl) = arena.get_inductive(data.id) else {
            return Err(CodegenError::InvalidTerm {
                decl: data.name.clone(),
            });
        };
        let mut param_keep = Vec::with_capacity(k_decl.params.len());
        let mut env = Vec::new();
        for (idx, p_decl) in k_decl.params.iter().enumerate() {
            let p_ty = eval(arena, &env, p_decl.ty).map_err(|err| CodegenError::Eval {
                decl: data.name.clone(),
                err,
            })?;
            param_keep.push(p_decl.mult.is_erased() && matches!(p_ty, Value::Universe(_)));
            let lvl = u32::try_from(idx).unwrap_or(u32::MAX);
            env.push(Value::var(apollo_kernel::DeBruijnLevel(lvl)));
        }
        let mut ctor_metas = Vec::with_capacity(data.ctors.len());
        for ctor in &data.ctors {
            let field_keep: Vec<bool> = ctor.fields.iter().map(|f| !f.mult.is_erased()).collect();
            let field_names: Vec<String> =
                ctor.fields.iter().map(|f| escape_ident(&f.name)).collect();
            let field_rec: Vec<bool> = ctor.fields.iter().map(|f| f.is_recursive).collect();
            if !ctor.is_path && field_rec.iter().any(|&r| r) {
                uses_alloc = true;
            }
            ctor_metas.push(LoweredCtorMeta {
                rust_name: escape_ident(&ctor.name),
                field_keep,
                field_names,
                field_rec,
            });
        }
        metas.push(LoweredDataMeta {
            rust_name: escape_ident(&data.name),
            kind: data.kind,
            param_keep,
            ctors: ctor_metas,
        });
    }
    Ok((metas, uses_alloc))
}

fn lower_data_kind(
    lowerer: &mut DeclLowerer<'_>,
    data: &CheckedData,
    k_decl: &apollo_kernel::InductiveDecl,
) -> Result<(RustDataKind, Vec<(usize, usize)>), CodegenError> {
    let mut erased_slots = Vec::new();
    match data.kind {
        DataKind::Enum => {
            let mut variants = Vec::with_capacity(data.ctors.len());
            for (c_idx, (ctor_info, k_ctor)) in data.ctors.iter().zip(&k_decl.ctors).enumerate() {
                if ctor_info.is_path {
                    continue;
                }
                let mut fields = Vec::new();
                for (f_idx, (f_info, k_field)) in
                    ctor_info.fields.iter().zip(&k_ctor.fields).enumerate()
                {
                    let f_ty_val = lowerer.eval_term(k_field.ty)?;
                    if !f_info.mult.is_erased() && !is_erased_value_type(&f_ty_val) {
                        let mut rty = lowerer.lower_val_ty(&f_ty_val, f_info.mult)?;
                        if f_info.is_recursive {
                            rty = RustType::Boxed(Box::new(rty));
                        }
                        fields.push(rty);
                    } else {
                        erased_slots.push((c_idx, f_idx));
                    }
                    let _ = lowerer.push_binding(f_ty_val, Binding::Erased);
                }
                for _ in &ctor_info.fields {
                    lowerer.pop_binding();
                }
                variants.push(RustEnumVariant {
                    name: escape_ident(&ctor_info.name),
                    fields,
                });
            }
            Ok((RustDataKind::Enum(variants), erased_slots))
        }
        DataKind::Struct => {
            let mut fields = Vec::new();
            if let (Some(ctor_info), Some(k_ctor)) = (data.ctors.first(), k_decl.ctors.first()) {
                for (f_idx, (f_info, k_field)) in
                    ctor_info.fields.iter().zip(&k_ctor.fields).enumerate()
                {
                    let f_ty_val = lowerer.eval_term(k_field.ty)?;
                    if !f_info.mult.is_erased() && !is_erased_value_type(&f_ty_val) {
                        let mut rty = lowerer.lower_val_ty(&f_ty_val, f_info.mult)?;
                        if f_info.is_recursive {
                            rty = RustType::Boxed(Box::new(rty));
                        }
                        fields.push(RustStructField {
                            name: escape_ident(&f_info.name),
                            ty: rty,
                        });
                    } else {
                        erased_slots.push((0, f_idx));
                    }
                    let _ = lowerer.push_binding(f_ty_val, Binding::Erased);
                }
                for _ in &ctor_info.fields {
                    lowerer.pop_binding();
                }
            }
            Ok((RustDataKind::Struct(fields), erased_slots))
        }
    }
}

struct ArmSpec<'a> {
    id: InductiveId,
    c_idx: usize,
    meta: &'a LoweredDataMeta,
    k_ctor: &'a apollo_kernel::CtorDecl,
    param_vals: &'a [Value],
    motive_cl: &'a Closure,
    branch_id: TermId,
}

impl DeclLowerer<'_> {
    pub(crate) fn lower_data_type(
        &mut self,
        id: InductiveId,
        params: &[Value],
    ) -> Result<RustType, CodegenError> {
        let Some(meta) = self.data_metas.get(id.raw() as usize).cloned() else {
            return Err(CodegenError::UnsupportedType {
                decl: self.decl_name.clone(),
            });
        };
        let mut args = Vec::new();
        for (p_val, &keep) in params.iter().zip(&meta.param_keep) {
            if keep {
                args.push(self.lower_val_ty(p_val, Multiplicity::One)?);
            }
        }
        Ok(RustType::Data {
            name: meta.rust_name,
            args,
        })
    }

    pub(crate) fn lower_ctor(
        &mut self,
        id: InductiveId,
        ctor: u32,
        params: &[TermId],
        args: &[TermId],
    ) -> Result<RustExpr, CodegenError> {
        let Some(meta) = self.data_metas.get(id.raw() as usize).cloned() else {
            return Err(CodegenError::InvalidTerm {
                decl: self.decl_name.clone(),
            });
        };
        let Some(ctor_meta) = meta.ctors.get(ctor as usize).cloned() else {
            return Err(CodegenError::InvalidTerm {
                decl: self.decl_name.clone(),
            });
        };
        let Some(k_ctor) = self
            .arena
            .get_inductive(id)
            .and_then(|d| d.ctors.get(ctor as usize))
            .cloned()
        else {
            return Err(CodegenError::InvalidTerm {
                decl: self.decl_name.clone(),
            });
        };

        let mut field_env = Vec::with_capacity(params.len() + args.len());
        for &p in params {
            field_env.push(self.eval_term(p)?);
        }

        let mut kept_args = Vec::new();
        for (idx, (&arg_id, k_field)) in args.iter().zip(&k_ctor.fields).enumerate() {
            let f_ty =
                eval(self.arena, &field_env, k_field.ty).map_err(|err| CodegenError::Eval {
                    decl: self.decl_name.clone(),
                    err,
                })?;
            if ctor_meta.field_keep.get(idx).copied().unwrap_or(false) {
                let mut expr = self.lower_expr(arg_id, Some(&f_ty))?;
                if ctor_meta.field_rec.get(idx).copied().unwrap_or(false) {
                    expr = RustExpr::BoxNew(Box::new(expr));
                }
                kept_args.push((ctor_meta.field_names[idx].clone(), expr));
            }
            field_env.push(self.eval_term(arg_id)?);
        }

        match meta.kind {
            DataKind::Enum => Ok(RustExpr::EnumCtor {
                enum_name: meta.rust_name,
                variant_name: ctor_meta.rust_name,
                args: kept_args.into_iter().map(|(_, e)| e).collect(),
            }),
            DataKind::Struct => Ok(RustExpr::StructInit {
                struct_name: meta.rust_name,
                fields: kept_args,
            }),
        }
    }

    pub(crate) fn lower_data_elim(
        &mut self,
        id: InductiveId,
        params: &[TermId],
        motive: TermId,
        branches: &[TermId],
        scrut: TermId,
        expected: Option<&Value>,
    ) -> Result<RustExpr, CodegenError> {
        let Some(meta) = self.data_metas.get(id.raw() as usize).cloned() else {
            return Err(CodegenError::InvalidTerm {
                decl: self.decl_name.clone(),
            });
        };
        let Some(k_decl) = self.arena.get_inductive(id).cloned() else {
            return Err(CodegenError::InvalidTerm {
                decl: self.decl_name.clone(),
            });
        };

        let mut param_vals = Vec::with_capacity(params.len());
        for &p in params {
            param_vals.push(self.eval_term(p)?);
        }
        let scrut_val_ty = Value::Data {
            id,
            params: param_vals.clone(),
        };
        let scrut_rty = self.lower_val_ty(&scrut_val_ty, Multiplicity::One)?;
        let scrut_expr = self.lower_expr(scrut, Some(&scrut_val_ty))?;
        let motive_cl = Closure::new(self.env.clone(), motive);

        let outer_runtime: Vec<(usize, String, RustType)> = self
            .bindings
            .iter()
            .filter_map(|b| match b {
                Binding::Runtime { id, name, ty, .. } => Some((*id, name.clone(), ty.clone())),
                _ => None,
            })
            .collect();
        let outer_type_params: Vec<String> = self
            .bindings
            .iter()
            .filter_map(|b| match b {
                Binding::TypeParam(name) => Some(name.clone()),
                _ => None,
            })
            .collect();

        let mut lowered_arms = Vec::with_capacity(branches.len());
        let mut uses_recursion = false;
        let mut max_rec_in_arm = 0_usize;
        for (c_idx, (k_ctor, &branch_id)) in k_decl.ctors.iter().zip(branches).enumerate() {
            if k_ctor.is_path() {
                continue;
            }
            let arm = self.lower_data_arm(&ArmSpec {
                id,
                c_idx,
                meta: &meta,
                k_ctor,
                param_vals: &param_vals,
                motive_cl: &motive_cl,
                branch_id,
            })?;
            if !arm.1.is_empty() {
                uses_recursion = true;
                max_rec_in_arm = max_rec_in_arm.max(arm.1.len());
            }
            lowered_arms.push(arm);
        }

        if !uses_recursion {
            let arms = lowered_arms
                .into_iter()
                .map(|(pat, _, body, _)| RustMatchArm { pat, body })
                .collect();
            return Ok(RustExpr::DataMatch {
                scrut: Box::new(scrut_expr),
                arms,
            });
        }

        let ret_val = if let Some(exp) = expected {
            exp.clone()
        } else {
            let scrut_val = self.eval_term(scrut)?;
            motive_cl
                .apply(self.arena, scrut_val)
                .map_err(|err| CodegenError::Eval {
                    decl: self.decl_name.clone(),
                    err,
                })?
        };
        let ret_ty = self.lower_val_ty(&ret_val, Multiplicity::One)?;
        let helper_id = self.alloc_rec_id();
        Ok(build_rec_data_match(RecMatchSpec {
            helper_id,
            scrut_ty: scrut_rty,
            ret_ty,
            scrut_expr,
            outer_runtime,
            outer_type_params,
            lowered_arms,
            max_rec_in_arm,
        }))
    }

    fn lower_data_arm(&mut self, spec: &ArmSpec<'_>) -> Result<LoweredArm, CodegenError> {
        let ctor_meta = &spec.meta.ctors[spec.c_idx];
        let mut field_env = spec.param_vals.to_vec();
        let mut field_vars = Vec::with_capacity(spec.k_ctor.fields.len());
        let mut pat_binders = Vec::new();
        let mut rec_field_info = Vec::new();
        let mut pushed = 0_usize;

        for (f_idx, k_field) in spec.k_ctor.fields.iter().enumerate() {
            let f_ty_val =
                eval(self.arena, &field_env, k_field.ty).map_err(|err| CodegenError::Eval {
                    decl: self.decl_name.clone(),
                    err,
                })?;
            let keep = ctor_meta.field_keep.get(f_idx).copied().unwrap_or(false);
            let is_rec = ctor_meta.field_rec.get(f_idx).copied().unwrap_or(false);
            let binding = if keep {
                let f_rty = self.lower_val_ty(&f_ty_val, k_field.mult)?;
                let local_id = self.alloc_id();
                let name = format!("v{local_id}");
                pat_binders.push((
                    ctor_meta.field_names[f_idx].clone(),
                    RustPatBinder {
                        id: local_id,
                        name: name.clone(),
                        ty: f_rty.clone(),
                    },
                ));
                if is_rec {
                    rec_field_info.push((f_idx, local_id, name.clone()));
                }
                Binding::Runtime {
                    id: local_id,
                    name,
                    ty: f_rty,
                    is_boxed: is_rec,
                }
            } else {
                Binding::Erased
            };
            let f_var = self.push_binding(f_ty_val, binding);
            pushed += 1;
            field_env.push(f_var.clone());
            field_vars.push(f_var);
        }

        let ih_bindings = self.push_arm_ihs(spec.motive_cl, &field_vars, &rec_field_info)?;
        pushed += ih_bindings.len();

        let ctor_val = Value::Ctor {
            id: spec.id,
            ctor: u32::try_from(spec.c_idx).unwrap_or(u32::MAX),
            params: spec.param_vals.to_vec(),
            args: field_vars,
        };
        let branch_ty =
            spec.motive_cl
                .apply(self.arena, ctor_val)
                .map_err(|err| CodegenError::Eval {
                    decl: self.decl_name.clone(),
                    err,
                })?;
        let body_res = self.lower_expr(spec.branch_id, Some(&branch_ty));
        for _ in 0..pushed {
            self.pop_binding();
        }
        let body = body_res?;

        let mut used_ids = BTreeSet::new();
        collect_local_ids(&body, &mut used_ids);
        let active_recs: Vec<(usize, String, usize, String)> = ih_bindings
            .into_iter()
            .filter(|(ih_id, _, _, _)| used_ids.contains(ih_id))
            .collect();

        let pat = match spec.meta.kind {
            DataKind::Enum => RustMatchPat::Enum {
                enum_name: spec.meta.rust_name.clone(),
                variant_name: ctor_meta.rust_name.clone(),
                binders: pat_binders.into_iter().map(|(_, b)| b).collect(),
            },
            DataKind::Struct => RustMatchPat::Struct {
                struct_name: spec.meta.rust_name.clone(),
                fields: pat_binders,
            },
        };
        Ok((pat, active_recs, body, used_ids))
    }

    fn push_arm_ihs(
        &mut self,
        motive_cl: &Closure,
        field_vars: &[Value],
        rec_field_info: &[(usize, usize, String)],
    ) -> Result<Vec<(usize, String, usize, String)>, CodegenError> {
        let mut ih_bindings = Vec::with_capacity(rec_field_info.len());
        for &(f_idx, field_id, ref field_name) in rec_field_info {
            let ih_ty_val = motive_cl
                .apply(self.arena, field_vars[f_idx].clone())
                .map_err(|err| CodegenError::Eval {
                    decl: self.decl_name.clone(),
                    err,
                })?;
            let ih_rty = self.lower_val_ty(&ih_ty_val, Multiplicity::One)?;
            let ih_id = self.alloc_id();
            let ih_name = format!("v{ih_id}");
            let _ = self.push_binding(
                ih_ty_val,
                Binding::Runtime {
                    id: ih_id,
                    name: ih_name.clone(),
                    ty: ih_rty,
                    is_boxed: false,
                },
            );
            ih_bindings.push((ih_id, ih_name, field_id, field_name.clone()));
        }
        Ok(ih_bindings)
    }
}

struct RecMatchSpec {
    helper_id: usize,
    scrut_ty: RustType,
    ret_ty: RustType,
    scrut_expr: RustExpr,
    outer_runtime: Vec<(usize, String, RustType)>,
    outer_type_params: Vec<String>,
    lowered_arms: Vec<LoweredArm>,
    max_rec_in_arm: usize,
}

fn build_rec_data_match(spec: RecMatchSpec) -> RustExpr {
    let mut captures = Vec::new();
    for (oid, oname, oty) in spec.outer_runtime {
        let used_anywhere = spec
            .lowered_arms
            .iter()
            .any(|(_, _, _, used)| used.contains(&oid));
        if !used_anywhere {
            continue;
        }
        let used_in_rec_arm = spec
            .lowered_arms
            .iter()
            .any(|(_, recs, _, used)| !recs.is_empty() && used.contains(&oid));
        let mode = if oty.is_copy() {
            CaptureMode::ByValue
        } else if oty.is_callable() {
            CaptureMode::ByRefCallable
        } else if used_in_rec_arm || spec.max_rec_in_arm > 1 {
            CaptureMode::ByRefClone
        } else {
            CaptureMode::ByValue
        };
        captures.push(RecCapture {
            id: oid,
            name: oname.clone(),
            ty: oty,
            mode,
            arg_expr: RustExpr::Local {
                id: oid,
                name: oname,
            },
        });
    }

    let mut referenced_tps = BTreeSet::new();
    spec.scrut_ty.collect_type_params(&mut referenced_tps);
    spec.ret_ty.collect_type_params(&mut referenced_tps);
    for cap in &captures {
        cap.ty.collect_type_params(&mut referenced_tps);
    }
    let type_params: Vec<String> = spec
        .outer_type_params
        .into_iter()
        .filter(|tp| referenced_tps.contains(tp))
        .collect();

    let rec_arms = spec
        .lowered_arms
        .into_iter()
        .map(|(pat, rec_bindings, body, _)| RustRecArm {
            pat,
            rec_bindings,
            body,
        })
        .collect();

    RustExpr::RecDataMatch {
        helper_name: format!("__apollo_rec_{}", spec.helper_id),
        type_params,
        clone_bounds: BTreeSet::new(),
        scrut_ty: spec.scrut_ty,
        ret_ty: spec.ret_ty,
        captures,
        scrut: Box::new(spec.scrut_expr),
        arms: rec_arms,
    }
}
