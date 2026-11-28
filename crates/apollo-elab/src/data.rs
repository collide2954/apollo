use std::collections::{HashMap, HashSet};

use apollo_kernel::nbe::{Closure, Value, eval, quote};
use apollo_kernel::{
    CtorDecl, FieldDecl, Index, InductiveDecl, InductiveId, Level, Multiplicity, ParamDecl,
    PathBoundary, TermId, TypeError, check_and_define_inductive, infer,
};
use apollo_syntax::{DataDecl, DataKind, Expr, Pattern, Span};

use crate::{
    CheckedCtor, CheckedData, CheckedField, DataMatchSpec, ElabError, Elaborator, to_mult,
};

struct DataBranchSpec<'a> {
    id: InductiveId,
    c_idx: usize,
    params: &'a [Value],
    motive_cl: &'a Closure,
    binders: &'a [String],
    body_expr: &'a Expr,
    span: Span,
}

impl Elaborator {
    pub(crate) fn check_data_decl(&mut self, data: &DataDecl) -> Result<CheckedData, ElabError> {
        if self.globals.contains_key(&data.name) || self.data_map.contains_key(&data.name) {
            return Err(ElabError::DuplicateDecl {
                name: data.name.clone(),
                span: data.span,
            });
        }
        self.decl_name.clone_from(&data.name);

        let self_id = self.arena.next_inductive_id();
        let placeholder_info = CheckedData {
            id: self_id,
            kind: data.kind,
            name: data.name.clone(),
            param_names: data.params.iter().map(|p| p.name.clone()).collect(),
            ctors: Vec::new(),
        };
        let _ = self.data_map.insert(data.name.clone(), placeholder_info);

        let (kernel_decl, mut checked_ctors) = match self.build_inductive_decl(data, self_id) {
            Ok(pair) => pair,
            Err(err) => {
                let _ = self.data_map.remove(&data.name);
                return Err(err);
            }
        };

        let id = match check_and_define_inductive(&mut self.arena, kernel_decl) {
            Ok(id) => id,
            Err(err) => {
                let _ = self.data_map.remove(&data.name);
                return Err(ElabError::Type {
                    decl: data.name.clone(),
                    err,
                    span: data.span,
                });
            }
        };

        if let Some(final_decl) = self.arena.get_inductive(id) {
            for (checked_ctor, k_ctor) in checked_ctors.iter_mut().zip(&final_decl.ctors) {
                for (checked_field, k_field) in checked_ctor.fields.iter_mut().zip(&k_ctor.fields) {
                    checked_field.is_recursive = k_field.is_recursive;
                }
            }
        }

        let checked = CheckedData {
            id,
            kind: data.kind,
            name: data.name.clone(),
            param_names: data.params.iter().map(|p| p.name.clone()).collect(),
            ctors: checked_ctors,
        };
        let _ = self.data_map.insert(data.name.clone(), checked.clone());
        self.data_decls.push(checked.clone());
        Ok(checked)
    }

    fn build_inductive_decl(
        &mut self,
        data: &DataDecl,
        self_id: InductiveId,
    ) -> Result<(InductiveDecl, Vec<CheckedCtor>), ElabError> {
        let mut params = Vec::with_capacity(data.params.len());
        let mut param_vars = Vec::with_capacity(data.params.len());
        let mut pushed_params = 0_usize;
        for param in &data.params {
            let ty_id = match self.elab_expr(&param.ty, None) {
                Ok(id) => id,
                Err(err) => {
                    for _ in 0..pushed_params {
                        self.pop_binding();
                    }
                    return Err(err);
                }
            };
            let ty_val = match self.eval_in_ctx(ty_id, param.span) {
                Ok(val) => val,
                Err(err) => {
                    for _ in 0..pushed_params {
                        self.pop_binding();
                    }
                    return Err(err);
                }
            };
            param_vars.push(self.push_var(param.name.clone(), ty_val));
            pushed_params += 1;
            params.push(ParamDecl {
                mult: to_mult(param.mult),
                ty: ty_id,
            });
        }

        let ctors_res = self.build_variants(data, self_id, &param_vars);
        for _ in 0..pushed_params {
            self.pop_binding();
        }
        let (ctors, checked_ctors) = ctors_res?;
        let level = Level::constant(data.level.unwrap_or(0));
        Ok((
            InductiveDecl {
                params,
                level,
                ctors,
            },
            checked_ctors,
        ))
    }

    fn build_variants(
        &mut self,
        data: &DataDecl,
        self_id: InductiveId,
        param_vars: &[Value],
    ) -> Result<(Vec<CtorDecl>, Vec<CheckedCtor>), ElabError> {
        let mut seen_variants = HashSet::new();
        let mut ctors = Vec::with_capacity(data.variants.len());
        let mut checked_ctors = Vec::with_capacity(data.variants.len());

        for variant in &data.variants {
            if !seen_variants.insert(variant.name.clone()) {
                return Err(ElabError::InvalidData {
                    message: format!("duplicate variant '{}'", variant.name),
                    span: variant.span,
                });
            }
            let mut fields = Vec::with_capacity(variant.fields.len());
            let mut checked_fields = Vec::with_capacity(variant.fields.len());
            let mut pushed = 0_usize;
            for field in &variant.fields {
                let ty_id = match self.elab_expr(&field.ty, None) {
                    Ok(id) => id,
                    Err(err) => {
                        for _ in 0..pushed {
                            self.pop_binding();
                        }
                        return Err(err);
                    }
                };
                let ty_val = match self.eval_in_ctx(ty_id, field.span) {
                    Ok(val) => val,
                    Err(err) => {
                        for _ in 0..pushed {
                            self.pop_binding();
                        }
                        return Err(err);
                    }
                };
                let mult = to_mult(field.mult);
                let _ = self.push_var(field.name.clone(), ty_val);
                pushed += 1;
                fields.push(FieldDecl {
                    mult,
                    ty: ty_id,
                    is_recursive: false,
                });
                checked_fields.push(CheckedField {
                    name: field.name.clone(),
                    mult,
                    is_recursive: false,
                });
            }
            for _ in 0..pushed {
                self.pop_binding();
            }
            ctors.push(CtorDecl {
                fields,
                boundary: None,
            });
            checked_ctors.push(CheckedCtor {
                name: variant.name.clone(),
                fields: checked_fields,
                is_path: variant.path.is_some(),
            });
        }

        if data.variants.iter().any(|v| v.path.is_some()) {
            if let Some(entry) = self.data_map.get_mut(&data.name) {
                entry.ctors.clone_from(&checked_ctors);
            }
            self.pending_inductive = Some((self_id, ctors.clone()));
            let res = self.elab_variant_boundaries(data, self_id, param_vars, &mut ctors);
            self.pending_inductive = None;
            res?;
        }
        Ok((ctors, checked_ctors))
    }

    fn elab_variant_boundaries(
        &mut self,
        data: &DataDecl,
        self_id: InductiveId,
        param_vars: &[Value],
        ctors: &mut [CtorDecl],
    ) -> Result<(), ElabError> {
        let data_ty = Value::Data {
            id: self_id,
            params: param_vars.to_vec(),
        };
        for (variant, ctor) in data.variants.iter().zip(ctors.iter_mut()) {
            let Some(path_ast) = &variant.path else {
                continue;
            };
            let mut pushed = 0_usize;
            for (field_ast, field_decl) in variant.fields.iter().zip(&ctor.fields) {
                let ty_val = match self.eval_in_ctx(field_decl.ty, field_ast.span) {
                    Ok(val) => val,
                    Err(err) => {
                        for _ in 0..pushed {
                            self.pop_binding();
                        }
                        return Err(err);
                    }
                };
                let _ = self.push_var(field_ast.name.clone(), ty_val);
                pushed += 1;
            }
            let boundary_res = self
                .elab_expr(&path_ast.left, Some(&data_ty))
                .and_then(|left| {
                    self.elab_expr(&path_ast.right, Some(&data_ty))
                        .map(|right| PathBoundary { left, right })
                });
            for _ in 0..pushed {
                self.pop_binding();
            }
            ctor.boundary = Some(boundary_res?);
        }
        Ok(())
    }

    pub(crate) fn elab_data_type_app(
        &mut self,
        name: &str,
        args: &[&Expr],
        span: Span,
    ) -> Result<TermId, ElabError> {
        let info = self
            .data_map
            .get(name)
            .cloned()
            .ok_or_else(|| ElabError::UnknownName {
                name: name.to_owned(),
                span,
            })?;
        if args.len() != info.param_names.len() {
            return Err(ElabError::InvalidData {
                message: format!(
                    "type '{}' expects {} arguments, got {}",
                    name,
                    info.param_names.len(),
                    args.len()
                ),
                span,
            });
        }
        let mut param_ids = Vec::with_capacity(args.len());
        for arg in args {
            param_ids.push(self.elab_expr(arg, None)?);
        }
        Ok(self.arena.data(info.id, param_ids))
    }

    pub(crate) fn elab_ctor(
        &mut self,
        type_name: &str,
        ctor_name: &str,
        args: &[Expr],
        expected: Option<&Value>,
        span: Span,
    ) -> Result<TermId, ElabError> {
        let info = self
            .data_map
            .get(type_name)
            .cloned()
            .ok_or_else(|| ElabError::UnknownName {
                name: type_name.to_owned(),
                span,
            })?;
        let Some((ctor_idx, ctor_info)) = info
            .ctors
            .iter()
            .enumerate()
            .find(|(_, c)| c.name == ctor_name)
        else {
            return Err(ElabError::InvalidData {
                message: format!("unknown constructor '{type_name}::{ctor_name}'"),
                span,
            });
        };

        let param_count = info.param_names.len();
        let arg_count = ctor_info.fields.len() + usize::from(ctor_info.is_path);
        let (param_ids, param_vals, field_exprs) = if args.len() == arg_count {
            let (p_ids, p_vals) =
                self.resolve_expected_params(info.id, param_count, expected, span)?;
            (p_ids, p_vals, args)
        } else if args.len() == param_count + arg_count {
            let (p_ids, p_vals) = self.elab_explicit_params(&args[..param_count])?;
            (p_ids, p_vals, &args[param_count..])
        } else {
            return Err(ElabError::InvalidData {
                message: format!(
                    "constructor '{type_name}::{ctor_name}' expects {arg_count} arguments, got {}",
                    args.len()
                ),
                span,
            });
        };

        let arg_ids = self.elab_ctor_fields(
            info.id,
            ctor_idx,
            &param_vals,
            field_exprs,
            ctor_info.is_path,
            span,
        )?;
        let ctor_u32 = u32::try_from(ctor_idx).unwrap_or(u32::MAX);
        Ok(self.arena.ctor(info.id, ctor_u32, param_ids, arg_ids))
    }

    pub(crate) fn elab_struct_lit(
        &mut self,
        type_name: &str,
        type_args: &[Expr],
        fields: &[(String, Expr)],
        expected: Option<&Value>,
        span: Span,
    ) -> Result<TermId, ElabError> {
        let info = self
            .data_map
            .get(type_name)
            .cloned()
            .ok_or_else(|| ElabError::UnknownName {
                name: type_name.to_owned(),
                span,
            })?;
        if info.kind != DataKind::Struct {
            return Err(ElabError::InvalidData {
                message: format!("'{type_name}' is not a struct"),
                span,
            });
        }
        let param_count = info.param_names.len();
        let (param_ids, param_vals) = if type_args.is_empty() {
            self.resolve_expected_params(info.id, param_count, expected, span)?
        } else if type_args.len() == param_count {
            self.elab_explicit_params(type_args)?
        } else {
            return Err(ElabError::InvalidData {
                message: format!(
                    "struct '{type_name}' expects {param_count} type arguments, got {}",
                    type_args.len()
                ),
                span,
            });
        };

        let Some(ctor_info) = info.ctors.first() else {
            return Err(ElabError::InvalidData {
                message: format!("struct '{type_name}' has no constructor"),
                span,
            });
        };
        let mut provided = HashMap::new();
        for (fname, fexpr) in fields {
            if provided.insert(fname.as_str(), fexpr).is_some() {
                return Err(ElabError::InvalidData {
                    message: format!("duplicate field '{fname}' in struct '{type_name}'"),
                    span,
                });
            }
        }
        if provided.len() != ctor_info.fields.len() {
            return Err(ElabError::InvalidData {
                message: format!(
                    "struct '{type_name}' expects {} fields, got {}",
                    ctor_info.fields.len(),
                    provided.len()
                ),
                span,
            });
        }

        let mut ordered_exprs = Vec::with_capacity(ctor_info.fields.len());
        for field in &ctor_info.fields {
            let Some(&fexpr) = provided.get(field.name.as_str()) else {
                return Err(ElabError::InvalidData {
                    message: format!("missing field '{}' in struct '{type_name}'", field.name),
                    span,
                });
            };
            ordered_exprs.push(fexpr.clone());
        }

        let arg_ids =
            self.elab_ctor_fields(info.id, 0, &param_vals, &ordered_exprs, false, span)?;
        Ok(self.arena.ctor(info.id, 0, param_ids, arg_ids))
    }

    pub(crate) fn elab_field(
        &mut self,
        target: &Expr,
        field_name: &str,
        span: Span,
    ) -> Result<TermId, ElabError> {
        let target_id = self.elab_expr(target, None)?;
        let (target_ty, _) = infer(&self.arena, &mut self.ctx, Multiplicity::Zero, target_id)
            .map_err(|err| ElabError::Type {
                decl: self.decl_name.clone(),
                err,
                span: target.span,
            })?;
        let Value::Data { id, params } = target_ty else {
            return Err(ElabError::InvalidData {
                message: format!("cannot project field '.{field_name}' on non-struct value"),
                span,
            });
        };
        let Some(info) = self.data_decls.get(id.raw() as usize).cloned() else {
            return Err(ElabError::InvalidData {
                message: format!("unknown data type {id}"),
                span,
            });
        };
        if info.kind != DataKind::Struct {
            return Err(ElabError::InvalidData {
                message: format!(
                    "cannot project field '.{field_name}' on enum '{}'",
                    info.name
                ),
                span,
            });
        }
        let Some(ctor_info) = info.ctors.first() else {
            return Err(ElabError::InvalidData {
                message: format!("struct '{}' has no fields", info.name),
                span,
            });
        };
        let Some(field_idx) = ctor_info.fields.iter().position(|f| f.name == field_name) else {
            return Err(ElabError::InvalidData {
                message: format!("struct '{}' has no field '{field_name}'", info.name),
                span,
            });
        };

        let depth = self.ctx.depth();
        let mut param_ids = Vec::with_capacity(params.len());
        for p in &params {
            param_ids.push(
                quote(&mut self.arena, depth, p).map_err(|err| ElabError::Type {
                    decl: self.decl_name.clone(),
                    err: TypeError::Eval(err),
                    span,
                })?,
            );
        }

        let k_field_ty = self
            .arena
            .get_inductive(id)
            .and_then(|d| d.ctors.first())
            .and_then(|c| c.fields.get(field_idx))
            .map(|f| f.ty)
            .ok_or_else(|| ElabError::InvalidData {
                message: format!("missing field metadata for '{field_name}'"),
                span,
            })?;
        let field_ty_val =
            eval(&self.arena, &params, k_field_ty).map_err(|err| ElabError::Type {
                decl: self.decl_name.clone(),
                err: TypeError::Eval(err),
                span,
            })?;
        let motive_id =
            quote(&mut self.arena, depth + 1, &field_ty_val).map_err(|err| ElabError::Type {
                decl: self.decl_name.clone(),
                err: TypeError::Eval(err),
                span,
            })?;
        let field_count = ctor_info.fields.len();
        let var_idx = u32::try_from(field_count - 1 - field_idx).unwrap_or(0);
        let branch = self.arena.var(Index(var_idx));
        Ok(self
            .arena
            .data_elim(id, param_ids, motive_id, vec![branch], target_id))
    }

    pub(crate) fn elab_data_match(
        &mut self,
        spec: &DataMatchSpec<'_>,
    ) -> Result<TermId, ElabError> {
        let Some(info) = self.data_decls.get(spec.id.raw() as usize).cloned() else {
            return Err(ElabError::InvalidMatch {
                message: format!("unknown data type {}", spec.id),
                span: spec.span,
            });
        };
        let mut mapped: Vec<Option<(Vec<String>, &Expr)>> = vec![None; info.ctors.len()];
        for arm in spec.arms {
            let (ctor_idx, binders) = match (&arm.pat, info.kind) {
                (
                    Pattern::Ctor {
                        type_name,
                        ctor_name,
                        binders,
                        ..
                    },
                    DataKind::Enum,
                ) if type_name == &info.name => {
                    let Some(idx) = info.ctors.iter().position(|c| &c.name == ctor_name) else {
                        return Err(ElabError::InvalidMatch {
                            message: format!("unknown constructor '{type_name}::{ctor_name}'"),
                            span: arm.span,
                        });
                    };
                    (idx, binders.clone())
                }
                (
                    Pattern::Struct {
                        type_name, fields, ..
                    },
                    DataKind::Struct,
                ) if type_name == &info.name => {
                    let binders = reorder_struct_pat_binders(&info, fields, arm.span)?;
                    (0, binders)
                }
                _ => {
                    return Err(ElabError::InvalidMatch {
                        message: format!("pattern does not match data type '{}'", info.name),
                        span: arm.span,
                    });
                }
            };
            if mapped[ctor_idx].is_some() {
                return Err(ElabError::InvalidMatch {
                    message: format!(
                        "duplicate match arm for '{}::{}'",
                        info.name, info.ctors[ctor_idx].name
                    ),
                    span: arm.span,
                });
            }
            mapped[ctor_idx] = Some((binders, &arm.body));
        }

        let depth = self.ctx.depth();
        let mut param_ids = Vec::with_capacity(spec.params.len());
        for p in spec.params {
            param_ids.push(
                quote(&mut self.arena, depth, p).map_err(|err| ElabError::Type {
                    decl: self.decl_name.clone(),
                    err: TypeError::Eval(err),
                    span: spec.span,
                })?,
            );
        }

        let mut branch_ids = Vec::with_capacity(info.ctors.len());
        for (c_idx, entry) in mapped.into_iter().enumerate() {
            let Some((binders, body_expr)) = entry else {
                return Err(ElabError::InvalidMatch {
                    message: format!(
                        "non-exhaustive match on '{}': missing '{}'",
                        info.name, info.ctors[c_idx].name
                    ),
                    span: spec.span,
                });
            };
            let branch_id = self.elab_data_branch(&DataBranchSpec {
                id: spec.id,
                c_idx,
                params: spec.params,
                motive_cl: spec.motive_cl,
                binders: &binders,
                body_expr,
                span: spec.span,
            })?;
            branch_ids.push(branch_id);
        }
        Ok(self.arena.data_elim(
            spec.id,
            param_ids,
            spec.motive_id,
            branch_ids,
            spec.scrut_id,
        ))
    }

    fn elab_data_branch(&mut self, spec: &DataBranchSpec<'_>) -> Result<TermId, ElabError> {
        let k_ctor = self
            .arena
            .get_inductive(spec.id)
            .and_then(|d| d.ctors.get(spec.c_idx))
            .cloned()
            .ok_or_else(|| ElabError::InvalidMatch {
                message: format!("unknown constructor index {}", spec.c_idx),
                span: spec.span,
            })?;
        let f_count = k_ctor.fields.len();
        let r_count = k_ctor.recursive_count();
        let p_extra = usize::from(k_ctor.is_path());
        if spec.binders.len() != f_count + p_extra
            && spec.binders.len() != f_count + r_count + p_extra
        {
            return Err(ElabError::InvalidMatch {
                message: format!(
                    "expected {} or {} binders, got {}",
                    f_count + p_extra,
                    f_count + r_count + p_extra,
                    spec.binders.len()
                ),
                span: spec.span,
            });
        }

        let mut field_env = spec.params.to_vec();
        let mut field_vars = Vec::with_capacity(f_count);
        for (idx, field) in k_ctor.fields.iter().enumerate() {
            let f_ty = eval(&self.arena, &field_env, field.ty).map_err(|err| ElabError::Type {
                decl: self.decl_name.clone(),
                err: TypeError::Eval(err),
                span: spec.span,
            })?;
            let f_var = self.push_var(spec.binders[idx].clone(), f_ty);
            field_env.push(f_var.clone());
            field_vars.push(f_var);
        }

        let ih_limit = spec.binders.len() - p_extra;
        let mut ih_idx = f_count;
        for (f_var, field) in field_vars.iter().zip(&k_ctor.fields) {
            if field.is_recursive {
                let ih_ty = spec
                    .motive_cl
                    .apply(&self.arena, f_var.clone())
                    .map_err(|err| ElabError::Type {
                        decl: self.decl_name.clone(),
                        err: TypeError::Eval(err),
                        span: spec.span,
                    })?;
                let ih_name = if ih_idx < ih_limit {
                    spec.binders[ih_idx].clone()
                } else {
                    "_".to_owned()
                };
                ih_idx += 1;
                let _ = self.push_var(ih_name, ih_ty);
            }
        }

        let mut ctor_args = field_vars;
        if k_ctor.is_path() {
            let dim_name = spec.binders[spec.binders.len() - 1].clone();
            ctor_args.push(self.push_dim(dim_name));
        }

        let ctor_val = Value::Ctor {
            id: spec.id,
            ctor: u32::try_from(spec.c_idx).unwrap_or(u32::MAX),
            params: spec.params.to_vec(),
            args: ctor_args,
        };
        let branch_ty =
            spec.motive_cl
                .apply(&self.arena, ctor_val)
                .map_err(|err| ElabError::Type {
                    decl: self.decl_name.clone(),
                    err: TypeError::Eval(err),
                    span: spec.span,
                })?;
        let body_res = self.elab_expr(spec.body_expr, Some(&branch_ty));
        for _ in 0..(f_count + r_count + p_extra) {
            self.pop_binding();
        }
        body_res
    }

    fn resolve_expected_params(
        &mut self,
        id: InductiveId,
        param_count: usize,
        expected: Option<&Value>,
        span: Span,
    ) -> Result<(Vec<TermId>, Vec<Value>), ElabError> {
        if param_count == 0 {
            return Ok((Vec::new(), Vec::new()));
        }
        let Some(Value::Data { id: exp_id, params }) = expected else {
            return Err(ElabError::InvalidData {
                message: "generic constructor requires explicit type arguments or expected type"
                    .to_owned(),
                span,
            });
        };
        if *exp_id != id || params.len() != param_count {
            return Err(ElabError::InvalidData {
                message: "constructor does not match expected data type".to_owned(),
                span,
            });
        }
        let depth = self.ctx.depth();
        let mut ids = Vec::with_capacity(params.len());
        for p in params {
            ids.push(
                quote(&mut self.arena, depth, p).map_err(|err| ElabError::Type {
                    decl: self.decl_name.clone(),
                    err: TypeError::Eval(err),
                    span,
                })?,
            );
        }
        Ok((ids, params.clone()))
    }

    fn elab_explicit_params(
        &mut self,
        exprs: &[Expr],
    ) -> Result<(Vec<TermId>, Vec<Value>), ElabError> {
        let mut ids = Vec::with_capacity(exprs.len());
        let mut vals = Vec::with_capacity(exprs.len());
        for expr in exprs {
            let id = self.elab_expr(expr, None)?;
            let val = self.eval_in_ctx(id, expr.span)?;
            ids.push(id);
            vals.push(val);
        }
        Ok((ids, vals))
    }

    fn elab_ctor_fields(
        &mut self,
        id: InductiveId,
        ctor_idx: usize,
        param_vals: &[Value],
        field_exprs: &[Expr],
        is_path: bool,
        span: Span,
    ) -> Result<Vec<TermId>, ElabError> {
        let k_fields = self
            .arena
            .get_inductive(id)
            .and_then(|d| d.ctors.get(ctor_idx))
            .or_else(|| {
                self.pending_inductive
                    .as_ref()
                    .filter(|(pid, _)| *pid == id)
                    .and_then(|(_, ctors)| ctors.get(ctor_idx))
            })
            .map(|c| c.fields.clone())
            .ok_or_else(|| ElabError::InvalidData {
                message: format!("unknown constructor index {ctor_idx}"),
                span,
            })?;
        let mut field_env = param_vals.to_vec();
        let mut arg_ids = Vec::with_capacity(field_exprs.len());
        for (expr, field) in field_exprs.iter().zip(&k_fields) {
            let expected_ty =
                eval(&self.arena, &field_env, field.ty).map_err(|err| ElabError::Type {
                    decl: self.decl_name.clone(),
                    err: TypeError::Eval(err),
                    span: expr.span,
                })?;
            let arg_id = self.elab_expr(expr, Some(&expected_ty))?;
            let arg_val = self.eval_in_ctx(arg_id, expr.span)?;
            field_env.push(arg_val);
            arg_ids.push(arg_id);
        }
        if is_path && let Some(dim_expr) = field_exprs.get(k_fields.len()) {
            arg_ids.push(self.elab_expr(dim_expr, Some(&Value::Interval))?);
        }
        Ok(arg_ids)
    }
}

fn reorder_struct_pat_binders(
    info: &CheckedData,
    fields: &[(String, String)],
    span: Span,
) -> Result<Vec<String>, ElabError> {
    let Some(ctor) = info.ctors.first() else {
        return Err(ElabError::InvalidMatch {
            message: format!("struct '{}' has no fields", info.name),
            span,
        });
    };
    let mut provided = HashMap::new();
    for (fname, binder) in fields {
        if provided.insert(fname.as_str(), binder.as_str()).is_some() {
            return Err(ElabError::InvalidMatch {
                message: format!("duplicate field '{fname}' in pattern for '{}'", info.name),
                span,
            });
        }
    }
    if provided.len() != ctor.fields.len() {
        return Err(ElabError::InvalidMatch {
            message: format!(
                "pattern for '{}' expects {} fields, got {}",
                info.name,
                ctor.fields.len(),
                provided.len()
            ),
            span,
        });
    }
    let mut ordered = Vec::with_capacity(ctor.fields.len());
    for field in &ctor.fields {
        let Some(&binder) = provided.get(field.name.as_str()) else {
            return Err(ElabError::InvalidMatch {
                message: format!(
                    "missing field '{}' in pattern for '{}'",
                    field.name, info.name
                ),
                span,
            });
        };
        ordered.push(binder.to_owned());
    }
    Ok(ordered)
}
