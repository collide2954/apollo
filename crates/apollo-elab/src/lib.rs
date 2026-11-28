mod data;

use std::collections::HashMap;
use std::fmt;
use std::sync::Arc;

use apollo_kernel::nbe::{Closure, Value, eval, quote};
use apollo_kernel::{
    CofTerm, Ctx, Index, InductiveId, Level, Multiplicity, TermArena, TermId, TypeError,
    check_closed, infer,
};
use apollo_syntax::{
    CofExpr, DataKind, Decl, DeclKind, Expr, ExprKind, MatchArm, ModuleItem, MultAst, ParseError,
    Pattern, Span, line_col, parse_module,
};

#[must_use]
pub const fn version() -> &'static str {
    env!("CARGO_PKG_VERSION")
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckedField {
    pub name: String,
    pub mult: Multiplicity,
    pub is_recursive: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckedCtor {
    pub name: String,
    pub fields: Vec<CheckedField>,
    pub is_path: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckedData {
    pub id: InductiveId,
    pub kind: DataKind,
    pub name: String,
    pub param_names: Vec<String>,
    pub ctors: Vec<CheckedCtor>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckedDecl {
    pub kind: DeclKind,
    pub name: String,
    pub param_names: Vec<String>,
    pub ty: TermId,
    pub body: TermId,
}

#[derive(Debug, Clone)]
pub struct CheckedModule {
    pub arena: TermArena,
    pub data_decls: Vec<CheckedData>,
    pub decls: Vec<CheckedDecl>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ElabError {
    Parse(ParseError),
    DuplicateDecl {
        name: String,
        span: Span,
    },
    UnknownName {
        name: String,
        span: Span,
    },
    ExpectedPath {
        span: Span,
    },
    UnsupportedUnannotatedLet {
        span: Span,
    },
    InvalidMatch {
        message: String,
        span: Span,
    },
    InvalidData {
        message: String,
        span: Span,
    },
    Type {
        decl: String,
        err: TypeError,
        span: Span,
    },
    AutoUnsupported {
        message: String,
        span: Span,
    },
    AutoFailed {
        lhs: String,
        rhs: String,
        lhs_normal: String,
        rhs_normal: String,
        span: Span,
    },
}

impl From<ParseError> for ElabError {
    fn from(value: ParseError) -> Self {
        Self::Parse(value)
    }
}

impl ElabError {
    #[must_use]
    pub const fn span(&self) -> Span {
        match self {
            Self::Parse(err) => err.span(),
            Self::DuplicateDecl { span, .. }
            | Self::UnknownName { span, .. }
            | Self::ExpectedPath { span }
            | Self::UnsupportedUnannotatedLet { span }
            | Self::InvalidMatch { span, .. }
            | Self::InvalidData { span, .. }
            | Self::Type { span, .. }
            | Self::AutoUnsupported { span, .. }
            | Self::AutoFailed { span, .. } => *span,
        }
    }

    #[must_use]
    pub fn format_diagnostic(&self, path: &str, source: &str) -> String {
        let loc = line_col(source, self.span().start);
        format!("{path}:{loc}: error: {self}")
    }
}

impl fmt::Display for ElabError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Parse(err) => write!(f, "parse error: {err}"),
            Self::DuplicateDecl { name, .. } => write!(f, "duplicate declaration '{name}'"),
            Self::UnknownName { name, .. } => write!(f, "unknown identifier '{name}'"),
            Self::ExpectedPath { .. } => {
                f.write_str("path application requires an expression of Path type")
            }
            Self::UnsupportedUnannotatedLet { .. } => {
                f.write_str("let expression requires a known expected type")
            }
            Self::InvalidMatch { message, .. } => write!(f, "invalid match: {message}"),
            Self::InvalidData { message, .. } => write!(f, "invalid data declaration: {message}"),
            Self::Type { decl, err, .. } => write!(f, "in '{decl}': {err}"),
            Self::AutoUnsupported { message, .. } => write!(f, "auto: {message}"),
            Self::AutoFailed {
                lhs,
                rhs,
                lhs_normal,
                rhs_normal,
                ..
            } => write!(
                f,
                "auto could not prove {lhs} = {rhs}; normal forms are {lhs_normal} and {rhs_normal}"
            ),
        }
    }
}

impl std::error::Error for ElabError {}

pub fn check_source(source: &str) -> Result<CheckedModule, ElabError> {
    let module = parse_module(source)?;
    let mut elab = Elaborator::new();
    let mut checked = Vec::new();
    for item in &module.items {
        match item {
            ModuleItem::Data(data) => {
                let _ = elab.check_data_decl(data)?;
            }
            ModuleItem::Decl(decl) => {
                checked.push(elab.check_decl(decl)?);
            }
        }
    }
    Ok(CheckedModule {
        arena: elab.arena,
        data_decls: elab.data_decls,
        decls: checked,
    })
}

pub(crate) const fn to_mult(mult: MultAst) -> Multiplicity {
    match mult {
        MultAst::Zero => Multiplicity::Zero,
        MultAst::One => Multiplicity::One,
        MultAst::Many => Multiplicity::Many,
    }
}

#[derive(Clone, Copy)]
struct LetParts<'a> {
    mult: MultAst,
    name: &'a str,
    ty: &'a Expr,
    value: &'a Expr,
    body: &'a Expr,
    span: Span,
}

struct DataMatchSpec<'a> {
    id: InductiveId,
    params: &'a [Value],
    motive_id: TermId,
    motive_cl: &'a Closure,
    scrut_id: TermId,
    arms: &'a [MatchArm],
    span: Span,
}

pub(crate) struct Elaborator {
    pub(crate) arena: TermArena,
    pub(crate) ctx: Ctx,
    pub(crate) env: Vec<Value>,
    pub(crate) locals: Vec<String>,
    pub(crate) globals: HashMap<String, (TermId, TermId)>,
    pub(crate) data_map: HashMap<String, CheckedData>,
    pub(crate) data_decls: Vec<CheckedData>,
    pub(crate) pending_inductive: Option<(InductiveId, Vec<apollo_kernel::CtorDecl>)>,
    pub(crate) decl_name: String,
}

impl Elaborator {
    fn new() -> Self {
        Self {
            arena: TermArena::new(),
            ctx: Ctx::new(),
            env: Vec::new(),
            locals: Vec::new(),
            globals: HashMap::new(),
            data_map: HashMap::new(),
            data_decls: Vec::new(),
            pending_inductive: None,
            decl_name: String::new(),
        }
    }

    pub(crate) fn push_var(&mut self, name: String, ty: Value) -> Value {
        let var = self.ctx.push(ty);
        self.env.push(var.clone());
        self.locals.push(name);
        var
    }

    pub(crate) fn push_dim(&mut self, name: String) -> Value {
        let dim = self.ctx.push_dim();
        self.env.push(dim.clone());
        self.locals.push(name);
        dim
    }

    pub(crate) fn pop_binding(&mut self) {
        self.ctx.pop();
        let _ = self.env.pop();
        let _ = self.locals.pop();
    }

    fn check_decl(&mut self, decl: &Decl) -> Result<CheckedDecl, ElabError> {
        if self.globals.contains_key(&decl.name) || self.data_map.contains_key(&decl.name) {
            return Err(ElabError::DuplicateDecl {
                name: decl.name.clone(),
                span: decl.span,
            });
        }
        self.decl_name.clone_from(&decl.name);

        let mut param_tys = Vec::with_capacity(decl.params.len());
        let mut param_mults = Vec::with_capacity(decl.params.len());
        for param in &decl.params {
            let ty_id = self.elab_expr(&param.ty, None)?;
            let ty_val = self.eval_in_ctx(ty_id, param.span)?;
            let _ = self.push_var(param.name.clone(), ty_val);
            param_tys.push(ty_id);
            param_mults.push(to_mult(param.mult));
        }

        let ret_ty_id = self.elab_expr(&decl.ret_ty, None)?;
        let ret_ty_val = self.eval_in_ctx(ret_ty_id, decl.ret_ty.span)?;
        let body_res = self.elab_expr(&decl.body, Some(&ret_ty_val));

        for _ in &decl.params {
            self.pop_binding();
        }

        let mut ty_id = ret_ty_id;
        let mut body_id = body_res?;
        for (&mult, &p_ty) in param_mults.iter().rev().zip(param_tys.iter().rev()) {
            ty_id = self.arena.pi(mult, p_ty, ty_id);
            body_id = self.arena.lam(mult, body_id);
        }

        check_closed(&self.arena, body_id, ty_id).map_err(|err| ElabError::Type {
            decl: decl.name.clone(),
            err,
            span: decl.span,
        })?;

        self.globals.insert(decl.name.clone(), (ty_id, body_id));
        Ok(CheckedDecl {
            kind: decl.kind,
            name: decl.name.clone(),
            param_names: decl.params.iter().map(|p| p.name.clone()).collect(),
            ty: ty_id,
            body: body_id,
        })
    }

    pub(crate) fn elab_expr(
        &mut self,
        expr: &Expr,
        expected: Option<&Value>,
    ) -> Result<TermId, ElabError> {
        match &expr.kind {
            ExprKind::Universe(level) => Ok(self.arena.universe(Level::constant(*level))),
            ExprKind::Interval => Ok(self.arena.interval()),
            ExprKind::DimZero => Ok(self.arena.dim_zero()),
            ExprKind::DimOne => Ok(self.arena.dim_one()),
            ExprKind::Var(name) => self.resolve_var(name, expr.span),
            ExprKind::Pi { params, codomain } => self.elab_pi(params, codomain),
            ExprKind::Lam { params, body } => self.elab_lam(params, body, expected),
            ExprKind::App { .. } => self.elab_app(expr),
            ExprKind::Sigma {
                mult,
                name,
                first,
                second,
            } => self.elab_sigma(*mult, name, first, second),
            ExprKind::Pair { first, second } => self.elab_pair(first, second, expected),
            ExprKind::Fst(inner) => {
                let pair_id = self.elab_expr(inner, None)?;
                Ok(self.arena.fst(pair_id))
            }
            ExprKind::Snd(inner) => {
                let pair_id = self.elab_expr(inner, None)?;
                Ok(self.arena.snd(pair_id))
            }
            ExprKind::Ann { term, ty } => {
                let ty_id = self.elab_expr(ty, None)?;
                let ty_val = self.eval_in_ctx(ty_id, ty.span)?;
                let term_id = self.elab_expr(term, Some(&ty_val))?;
                Ok(self.arena.ann(term_id, ty_id))
            }
            ExprKind::Path {
                dim_name,
                family,
                left,
                right,
            } => self.elab_path(dim_name, family, left, right),
            ExprKind::PLam { dim_name, body } => self.elab_plam(dim_name, body, expected),
            ExprKind::PApp { path, dim } => self.elab_papp(path, dim, expr.span),
            ExprKind::Coe {
                dim_name,
                line,
                src,
                dst,
                term,
            } => self.elab_coe(dim_name, line, src, dst, term),
            ExprKind::HCom {
                ty,
                src,
                dst,
                branches,
                cap,
            } => self.elab_hcom(ty, src, dst, branches, cap),
            ExprKind::Let {
                mult,
                name,
                ty,
                value,
                body,
            } => self.elab_let(
                LetParts {
                    mult: *mult,
                    name,
                    ty,
                    value,
                    body,
                    span: expr.span,
                },
                expected,
            ),
            ExprKind::Unit
            | ExprKind::Tt
            | ExprKind::Void
            | ExprKind::Bool
            | ExprKind::True
            | ExprKind::False
            | ExprKind::Nat
            | ExprKind::Zero
            | ExprKind::Succ(_)
            | ExprKind::Add { .. } => self.elab_primitive(&expr.kind),
            ExprKind::Match {
                scrut,
                motive,
                arms,
            } => self.elab_match(scrut, motive.as_ref(), arms, expected, expr.span),
            _ => self.elab_ext_expr(expr, expected),
        }
    }

    fn elab_ext_expr(
        &mut self,
        expr: &Expr,
        expected: Option<&Value>,
    ) -> Result<TermId, ElabError> {
        match &expr.kind {
            ExprKind::Ctor {
                type_name,
                ctor_name,
                args,
            } => self.elab_ctor(type_name, ctor_name, args, expected, expr.span),
            ExprKind::StructLit {
                type_name,
                type_args,
                fields,
            } => self.elab_struct_lit(type_name, type_args, fields, expected, expr.span),
            ExprKind::Field { target, name } => self.elab_field(target, name, expr.span),
            ExprKind::Auto => self.elab_auto(expected, expr.span),
            ExprKind::VType {
                dim,
                ty0,
                ty1,
                equiv,
            } => {
                let dim_id = self.elab_expr(dim, Some(&Value::Interval))?;
                let ty0_id = self.elab_expr(ty0, None)?;
                let ty1_id = self.elab_expr(ty1, None)?;
                let equiv_id = self.elab_expr(equiv, None)?;
                Ok(self.arena.v_type(dim_id, ty0_id, ty1_id, equiv_id))
            }
            ExprKind::VIn { dim, left, right } => {
                let dim_id = self.elab_expr(dim, Some(&Value::Interval))?;
                let (exp_left, exp_right) = match expected {
                    Some(Value::VType { ty0, ty1, .. }) => (Some(ty0.as_ref()), Some(ty1.as_ref())),
                    _ => (None, None),
                };
                let left_id = self.elab_expr(left, exp_left)?;
                let right_id = self.elab_expr(right, exp_right)?;
                Ok(self.arena.v_in(dim_id, left_id, right_id))
            }
            ExprKind::VProj {
                dim,
                ty0,
                ty1,
                equiv,
                term,
            } => {
                let dim_id = self.elab_expr(dim, Some(&Value::Interval))?;
                let ty0_id = self.elab_expr(ty0, None)?;
                let ty1_id = self.elab_expr(ty1, None)?;
                let equiv_id = self.elab_expr(equiv, None)?;
                let term_id = self.elab_expr(term, None)?;
                Ok(self.arena.v_proj(dim_id, ty0_id, ty1_id, equiv_id, term_id))
            }
            _ => Ok(self.arena.tt()),
        }
    }

    fn elab_pair(
        &mut self,
        first: &Expr,
        second: &Expr,
        expected: Option<&Value>,
    ) -> Result<TermId, ElabError> {
        let (first_ty, second_cl) = match expected {
            Some(Value::Sigma { first, second, .. }) => (Some((**first).clone()), Some(second)),
            _ => (None, None),
        };
        let first_id = self.elab_expr(first, first_ty.as_ref())?;
        let second_ty = match second_cl {
            Some(closure) => {
                let first_val = self.eval_in_ctx(first_id, first.span)?;
                closure.apply(&self.arena, first_val).ok()
            }
            None => None,
        };
        let second_id = self.elab_expr(second, second_ty.as_ref())?;
        Ok(self.arena.pair(first_id, second_id))
    }

    fn elab_auto(&mut self, expected: Option<&Value>, span: Span) -> Result<TermId, ElabError> {
        let Some(goal) = expected else {
            return Err(ElabError::AutoUnsupported {
                message: "auto requires a known Path goal type".to_owned(),
                span,
            });
        };
        match apollo_auto::prove(&mut self.arena, &mut self.ctx, goal) {
            Ok(term) => Ok(term),
            Err(apollo_auto::AutoError::Unproved {
                lhs,
                rhs,
                lhs_normal,
                rhs_normal,
            }) => {
                let show = |id| apollo_auto::render::render(&self.arena, id, &self.locals);
                Err(ElabError::AutoFailed {
                    lhs: show(lhs),
                    rhs: show(rhs),
                    lhs_normal: show(lhs_normal),
                    rhs_normal: show(rhs_normal),
                    span,
                })
            }
            Err(other) => Err(ElabError::AutoUnsupported {
                message: other.to_string(),
                span,
            }),
        }
    }

    fn elab_primitive(&mut self, kind: &ExprKind) -> Result<TermId, ElabError> {
        match kind {
            ExprKind::Unit => Ok(self.arena.unit()),
            ExprKind::Void => Ok(self.arena.void()),
            ExprKind::Bool => Ok(self.arena.bool_ty()),
            ExprKind::True => Ok(self.arena.bool_true()),
            ExprKind::False => Ok(self.arena.bool_false()),
            ExprKind::Nat => Ok(self.arena.nat()),
            ExprKind::Zero => Ok(self.arena.zero()),
            ExprKind::Succ(pred) => {
                let pred_id = self.elab_expr(pred, Some(&Value::Nat))?;
                Ok(self.arena.succ(pred_id))
            }
            ExprKind::Add { lhs, rhs } => {
                let lhs_id = self.elab_expr(lhs, Some(&Value::Nat))?;
                let rhs_id = self.elab_expr(rhs, Some(&Value::Nat))?;
                Ok(apollo_auto::add_term(&mut self.arena, lhs_id, rhs_id))
            }
            _ => Ok(self.arena.tt()),
        }
    }

    fn elab_app(&mut self, expr: &Expr) -> Result<TermId, ElabError> {
        let mut head = expr;
        let mut rev_args = Vec::new();
        while let ExprKind::App { func, arg } = &head.kind {
            rev_args.push(arg.as_ref());
            head = func.as_ref();
        }
        rev_args.reverse();

        if let ExprKind::Var(name) = &head.kind
            && !self.locals.iter().any(|l| l == name)
            && self.data_map.contains_key(name)
        {
            return self.elab_data_type_app(name, &rev_args, expr.span);
        }

        let mut func_id = self.elab_expr(head, None)?;
        for arg in rev_args {
            let expected_arg = infer(&self.arena, &mut self.ctx, Multiplicity::Zero, func_id)
                .ok()
                .and_then(|(ty, _)| match ty {
                    Value::Pi { domain, .. } => Some((*domain).clone()),
                    _ => None,
                });
            let arg_id = self.elab_expr(arg, expected_arg.as_ref())?;
            func_id = self.arena.app(func_id, arg_id);
        }
        Ok(func_id)
    }

    fn resolve_var(&mut self, name: &str, span: Span) -> Result<TermId, ElabError> {
        if let Some(pos) = self.locals.iter().rposition(|local| local == name) {
            let idx = u32::try_from(self.locals.len() - 1 - pos).unwrap_or(u32::MAX);
            return Ok(self.arena.var(Index(idx)));
        }
        if let Some(&(ty_id, body_id)) = self.globals.get(name) {
            return Ok(self.arena.ann(body_id, ty_id));
        }
        if self.data_map.contains_key(name) {
            return self.elab_data_type_app(name, &[], span);
        }
        Err(ElabError::UnknownName {
            name: name.to_owned(),
            span,
        })
    }

    fn elab_pi(
        &mut self,
        params: &[apollo_syntax::Param],
        codomain: &Expr,
    ) -> Result<TermId, ElabError> {
        let mut param_tys = Vec::with_capacity(params.len());
        let mut param_mults = Vec::with_capacity(params.len());
        for param in params {
            let ty_id = self.elab_expr(&param.ty, None)?;
            let ty_val = self.eval_in_ctx(ty_id, param.span)?;
            let _ = self.push_var(param.name.clone(), ty_val);
            param_tys.push(ty_id);
            param_mults.push(to_mult(param.mult));
        }
        let cod_res = self.elab_expr(codomain, None);
        for _ in params {
            self.pop_binding();
        }
        let mut result = cod_res?;
        for (&mult, &p_ty) in param_mults.iter().rev().zip(param_tys.iter().rev()) {
            result = self.arena.pi(mult, p_ty, result);
        }
        Ok(result)
    }

    fn elab_lam(
        &mut self,
        params: &[(MultAst, String)],
        body: &Expr,
        expected: Option<&Value>,
    ) -> Result<TermId, ElabError> {
        let mut current_expected = expected.cloned();
        let mut mults = Vec::with_capacity(params.len());
        for (mult, name) in params {
            let (dom_ty, next_expected) = match current_expected {
                Some(Value::Pi {
                    domain, codomain, ..
                }) => {
                    let var = Value::var(apollo_kernel::DeBruijnLevel(self.ctx.depth()));
                    let next = codomain.apply(&self.arena, var).ok();
                    ((*domain).clone(), next)
                }
                _ => (Value::Universe(Level::zero()), None),
            };
            let _ = self.push_var(name.clone(), dom_ty);
            mults.push(to_mult(*mult));
            current_expected = next_expected;
        }
        let body_res = self.elab_expr(body, current_expected.as_ref());
        for _ in params {
            self.pop_binding();
        }
        let mut result = body_res?;
        for &mult in mults.iter().rev() {
            result = self.arena.lam(mult, result);
        }
        Ok(result)
    }

    fn elab_sigma(
        &mut self,
        mult: MultAst,
        name: &str,
        first: &Expr,
        second: &Expr,
    ) -> Result<TermId, ElabError> {
        let first_id = self.elab_expr(first, None)?;
        let first_val = self.eval_in_ctx(first_id, first.span)?;
        let _ = self.push_var(name.to_owned(), first_val);
        let second_res = self.elab_expr(second, None);
        self.pop_binding();
        Ok(self.arena.sigma(to_mult(mult), first_id, second_res?))
    }

    fn elab_plam(
        &mut self,
        dim_name: &str,
        body: &Expr,
        expected: Option<&Value>,
    ) -> Result<TermId, ElabError> {
        let dim = self.push_dim(dim_name.to_owned());
        let next_expected = match expected {
            Some(Value::Path { family, .. }) => family.apply(&self.arena, dim).ok(),
            _ => None,
        };
        let body_res = self.elab_expr(body, next_expected.as_ref());
        self.pop_binding();
        Ok(self.arena.plam(body_res?))
    }

    fn elab_path(
        &mut self,
        dim_name: &str,
        family: &Expr,
        left: &Expr,
        right: &Expr,
    ) -> Result<TermId, ElabError> {
        let _ = self.push_dim(dim_name.to_owned());
        let fam_res = self.elab_expr(family, None);
        self.pop_binding();
        let fam_id = fam_res?;
        let left_id = self.elab_expr(left, None)?;
        let right_id = self.elab_expr(right, None)?;
        Ok(self.arena.path(fam_id, left_id, right_id))
    }

    fn elab_papp(&mut self, path: &Expr, dim: &Expr, span: Span) -> Result<TermId, ElabError> {
        let path_id = self.elab_expr(path, None)?;
        let dim_id = self.elab_expr(dim, None)?;
        let (path_ty, _) =
            infer(&self.arena, &mut self.ctx, Multiplicity::Zero, path_id).map_err(|err| {
                ElabError::Type {
                    decl: self.decl_name.clone(),
                    err,
                    span: path.span,
                }
            })?;
        let Value::Path { left, right, .. } = path_ty else {
            return Err(ElabError::ExpectedPath { span });
        };
        let depth = self.ctx.depth();
        let left_id = quote(&mut self.arena, depth, &left).map_err(|err| ElabError::Type {
            decl: self.decl_name.clone(),
            err: TypeError::Eval(err),
            span,
        })?;
        let right_id = quote(&mut self.arena, depth, &right).map_err(|err| ElabError::Type {
            decl: self.decl_name.clone(),
            err: TypeError::Eval(err),
            span,
        })?;
        Ok(self.arena.papp(path_id, left_id, right_id, dim_id))
    }

    fn elab_coe(
        &mut self,
        dim_name: &str,
        line: &Expr,
        src: &Expr,
        dst: &Expr,
        term: &Expr,
    ) -> Result<TermId, ElabError> {
        let _ = self.push_dim(dim_name.to_owned());
        let line_res = self.elab_expr(line, None);
        self.pop_binding();
        let line_id = line_res?;
        let src_id = self.elab_expr(src, None)?;
        let dst_id = self.elab_expr(dst, None)?;
        let term_id = self.elab_expr(term, None)?;
        Ok(self.arena.coe(line_id, src_id, dst_id, term_id))
    }

    fn elab_hcom(
        &mut self,
        ty: &Expr,
        src: &Expr,
        dst: &Expr,
        branches: &[apollo_syntax::HComBranch],
        cap: &Expr,
    ) -> Result<TermId, ElabError> {
        let ty_id = self.elab_expr(ty, None)?;
        let src_id = self.elab_expr(src, None)?;
        let dst_id = self.elab_expr(dst, None)?;
        let mut elab_branches = Vec::with_capacity(branches.len());
        for branch in branches {
            let cof = self.elab_cof(&branch.cof)?;
            let _ = self.push_dim(branch.dim_name.clone());
            let tube_res = self.elab_expr(&branch.tube, None);
            self.pop_binding();
            elab_branches.push((cof, tube_res?));
        }
        let cap_id = self.elab_expr(cap, None)?;
        Ok(self
            .arena
            .hcom(ty_id, src_id, dst_id, elab_branches, cap_id))
    }

    fn elab_cof(&mut self, cof: &CofExpr) -> Result<CofTerm, ElabError> {
        match cof {
            CofExpr::Top(_) => Ok(CofTerm::Top),
            CofExpr::Bot(_) => Ok(CofTerm::Bot),
            CofExpr::Eq { lhs, rhs, .. } => {
                let l_id = self.elab_expr(lhs, None)?;
                let r_id = self.elab_expr(rhs, None)?;
                Ok(CofTerm::Eq(l_id, r_id))
            }
            CofExpr::And { lhs, rhs, .. } => Ok(CofTerm::And(
                Box::new(self.elab_cof(lhs)?),
                Box::new(self.elab_cof(rhs)?),
            )),
            CofExpr::Or { lhs, rhs, .. } => Ok(CofTerm::Or(
                Box::new(self.elab_cof(lhs)?),
                Box::new(self.elab_cof(rhs)?),
            )),
        }
    }

    fn elab_let(
        &mut self,
        parts: LetParts<'_>,
        expected: Option<&Value>,
    ) -> Result<TermId, ElabError> {
        let Some(exp_val) = expected else {
            return Err(ElabError::UnsupportedUnannotatedLet { span: parts.span });
        };
        let ty_id = self.elab_expr(parts.ty, None)?;
        let ty_val = self.eval_in_ctx(ty_id, parts.ty.span)?;
        let val_id = self.elab_expr(parts.value, Some(&ty_val))?;
        let _ = self.push_var(parts.name.to_owned(), ty_val);
        let body_res = self.elab_expr(parts.body, Some(exp_val));
        let cod_res = quote(&mut self.arena, self.ctx.depth(), exp_val);
        self.pop_binding();
        let body_id = body_res?;
        let cod_id = cod_res.map_err(|err| ElabError::Type {
            decl: self.decl_name.clone(),
            err: TypeError::Eval(err),
            span: parts.span,
        })?;
        let k_mult = to_mult(parts.mult);
        let lam_id = self.arena.lam(k_mult, body_id);
        let pi_id = self.arena.pi(k_mult, ty_id, cod_id);
        let ann_id = self.arena.ann(lam_id, pi_id);
        Ok(self.arena.app(ann_id, val_id))
    }

    pub(crate) fn eval_in_ctx(&self, term_id: TermId, span: Span) -> Result<Value, ElabError> {
        eval(&self.arena, &self.env, term_id).map_err(|err| ElabError::Type {
            decl: self.decl_name.clone(),
            err: TypeError::Eval(err),
            span,
        })
    }

    fn elab_match(
        &mut self,
        scrut: &Expr,
        motive: Option<&(String, Box<Expr>)>,
        arms: &[MatchArm],
        expected: Option<&Value>,
        span: Span,
    ) -> Result<TermId, ElabError> {
        let scrut_id = self.elab_expr(scrut, None)?;
        let (scrut_ty, _) = infer(&self.arena, &mut self.ctx, Multiplicity::Zero, scrut_id)
            .map_err(|err| ElabError::Type {
                decl: self.decl_name.clone(),
                err,
                span: scrut.span,
            })?;

        let (motive_id, motive_cl) = if let Some((name, motive_expr)) = motive {
            let _ = self.push_var(name.clone(), scrut_ty.clone());
            let m_res = self.elab_expr(motive_expr, None);
            self.pop_binding();
            let m_id = m_res?;
            (m_id, Closure::new(self.env.clone(), m_id))
        } else if let Some(exp_val) = expected {
            let m_id = quote(&mut self.arena, self.ctx.depth() + 1, exp_val).map_err(|err| {
                ElabError::Type {
                    decl: self.decl_name.clone(),
                    err: TypeError::Eval(err),
                    span,
                }
            })?;
            (m_id, Closure::new(self.env.clone(), m_id))
        } else {
            return Err(ElabError::InvalidMatch {
                message: "match expression requires an explicit motive or known expected type"
                    .to_owned(),
                span,
            });
        };

        match scrut_ty {
            Value::Void => self.elab_void_match(motive_id, scrut_id, arms, span),
            Value::Unit => self.elab_unit_match(motive_id, &motive_cl, scrut_id, arms, span),
            Value::Bool => self.elab_bool_match(motive_id, &motive_cl, scrut_id, arms, span),
            Value::Nat => self.elab_nat_match(motive_id, &motive_cl, scrut_id, arms, span),
            Value::Data { id, params } => self.elab_data_match(&DataMatchSpec {
                id,
                params: &params,
                motive_id,
                motive_cl: &motive_cl,
                scrut_id,
                arms,
                span,
            }),
            _ => Err(ElabError::InvalidMatch {
                message: "scrutinee must have an inductive type".to_owned(),
                span: scrut.span,
            }),
        }
    }

    fn elab_void_match(
        &mut self,
        motive_id: TermId,
        scrut_id: TermId,
        arms: &[MatchArm],
        span: Span,
    ) -> Result<TermId, ElabError> {
        if !arms.is_empty() {
            return Err(ElabError::InvalidMatch {
                message: "match on Void must have zero arms".to_owned(),
                span,
            });
        }
        Ok(self.arena.void_elim(motive_id, scrut_id))
    }

    fn elab_unit_match(
        &mut self,
        motive_id: TermId,
        motive_cl: &Closure,
        scrut_id: TermId,
        arms: &[MatchArm],
        span: Span,
    ) -> Result<TermId, ElabError> {
        let [arm] = arms else {
            return Err(ElabError::InvalidMatch {
                message: "match on Unit must have exactly one '()' arm".to_owned(),
                span,
            });
        };
        if !matches!(arm.pat, Pattern::Unit(_)) {
            return Err(ElabError::InvalidMatch {
                message: "expected '()' pattern for Unit".to_owned(),
                span: arm.span,
            });
        }
        let exp = motive_cl
            .apply(&self.arena, Value::Tt)
            .map_err(|err| ElabError::Type {
                decl: self.decl_name.clone(),
                err: TypeError::Eval(err),
                span,
            })?;
        let on_unit = self.elab_expr(&arm.body, Some(&exp))?;
        Ok(self.arena.unit_elim(motive_id, on_unit, scrut_id))
    }

    fn elab_bool_match(
        &mut self,
        motive_id: TermId,
        motive_cl: &Closure,
        scrut_id: TermId,
        arms: &[MatchArm],
        span: Span,
    ) -> Result<TermId, ElabError> {
        let mut on_true_arm = None;
        let mut on_false_arm = None;
        for arm in arms {
            match arm.pat {
                Pattern::True(_) if on_true_arm.is_none() => on_true_arm = Some(&arm.body),
                Pattern::False(_) if on_false_arm.is_none() => on_false_arm = Some(&arm.body),
                _ => {
                    return Err(ElabError::InvalidMatch {
                        message: "expected unique 'true' and 'false' arms for Bool".to_owned(),
                        span: arm.span,
                    });
                }
            }
        }
        let (Some(true_expr), Some(false_expr)) = (on_true_arm, on_false_arm) else {
            return Err(ElabError::InvalidMatch {
                message: "match on Bool must cover both 'true' and 'false'".to_owned(),
                span,
            });
        };
        let true_ty = motive_cl
            .apply(&self.arena, Value::True)
            .map_err(|err| ElabError::Type {
                decl: self.decl_name.clone(),
                err: TypeError::Eval(err),
                span,
            })?;
        let false_ty =
            motive_cl
                .apply(&self.arena, Value::False)
                .map_err(|err| ElabError::Type {
                    decl: self.decl_name.clone(),
                    err: TypeError::Eval(err),
                    span,
                })?;
        let on_true = self.elab_expr(true_expr, Some(&true_ty))?;
        let on_false = self.elab_expr(false_expr, Some(&false_ty))?;
        Ok(self.arena.bool_elim(motive_id, on_true, on_false, scrut_id))
    }

    fn elab_nat_match(
        &mut self,
        motive_id: TermId,
        motive_cl: &Closure,
        scrut_id: TermId,
        arms: &[MatchArm],
        span: Span,
    ) -> Result<TermId, ElabError> {
        let mut zero_arm = None;
        let mut succ_arm = None;
        for arm in arms {
            match &arm.pat {
                Pattern::Zero(_) if zero_arm.is_none() => zero_arm = Some(&arm.body),
                Pattern::Succ { pred, ih, .. } if succ_arm.is_none() => {
                    succ_arm = Some((pred.as_str(), ih.as_deref(), &arm.body));
                }
                _ => {
                    return Err(ElabError::InvalidMatch {
                        message: "expected unique 'zero' and 'succ' arms for Nat".to_owned(),
                        span: arm.span,
                    });
                }
            }
        }
        let (Some(zero_expr), Some((pred_name, ih_name, succ_expr))) = (zero_arm, succ_arm) else {
            return Err(ElabError::InvalidMatch {
                message: "match on Nat must cover both 'zero' and 'succ'".to_owned(),
                span,
            });
        };
        let base_ty = motive_cl
            .apply(&self.arena, Value::Zero)
            .map_err(|err| ElabError::Type {
                decl: self.decl_name.clone(),
                err: TypeError::Eval(err),
                span,
            })?;
        let base_id = self.elab_expr(zero_expr, Some(&base_ty))?;

        let pred_var = self.push_var(pred_name.to_owned(), Value::Nat);
        let ih_ty = motive_cl
            .apply(&self.arena, pred_var.clone())
            .map_err(|err| ElabError::Type {
                decl: self.decl_name.clone(),
                err: TypeError::Eval(err),
                span,
            })?;
        let succ_ty = motive_cl
            .apply(&self.arena, Value::Succ(Arc::new(pred_var)))
            .map_err(|err| ElabError::Type {
                decl: self.decl_name.clone(),
                err: TypeError::Eval(err),
                span,
            })?;
        let ih_binding = ih_name.unwrap_or("_").to_owned();
        let _ = self.push_var(ih_binding, ih_ty);
        let step_res = self.elab_expr(succ_expr, Some(&succ_ty));
        self.pop_binding();
        self.pop_binding();
        Ok(self.arena.nat_elim(motive_id, base_id, step_res?, scrut_id))
    }
}

#[cfg(test)]
mod tests {
    use super::{ElabError, check_source, version};

    #[test]
    fn reports_package_version() {
        assert_eq!(version(), env!("CARGO_PKG_VERSION"));
    }

    #[test]
    fn elaborates_and_checks_full_cubical_qtt_module() {
        let src = r"
            fn id(0 A: Type 0, 1 x: A) -> A {
                x
            }

            fn dup(0 A: Type 0, ω x: A) -> Sigma(1 _: A, A) {
                (x, x)
            }

            fn swap(0 A: Type 0, 0 B: Type 0, ω p: Sigma(1 _: A, B)) -> Sigma(1 _: B, A) {
                (p.1, p.0)
            }

            fn use_id(0 A: Type 0, 1 x: A) -> A {
                let 1 y: A = id(A, x);
                (y : A)
            }

            theorem refl(0 A: Type 0, 0 x: A) -> Path(_ => A, x, x) {
                <i> x
            }

            theorem ap(
                0 A: Type 0,
                0 B: Type 0,
                0 f: (1 _: A) -> B,
                0 x: A,
                0 y: A,
                0 p: Path(_ => A, x, y),
            ) -> Path(_ => B, f(x), f(y)) {
                <i> f(p @ i)
            }

            theorem funext(
                0 A: Type 0,
                0 B: Type 0,
                0 f: (1 _: A) -> B,
                0 g: (1 _: A) -> B,
                0 h: (0 x: A) -> Path(_ => B, f(x), g(x)),
            ) -> Path(_ => (1 _: A) -> B, f, g) {
                <i> |1 x| (h(x)) @ i
            }

            fn transport(
                0 A: Type 0,
                0 B: Type 0,
                0 p: Path(_ => Type 0, A, B),
                1 x: A,
            ) -> B {
                coe(i => p @ i, 0, 1, x)
            }

            theorem sym(
                0 A: Type 0,
                0 x: A,
                0 y: A,
                0 p: Path(_ => A, x, y),
            ) -> Path(_ => A, y, x) {
                <i> hcom(A, 0, 1, [i = 0 => <j> p @ j, i = 1 => <j> x], x)
            }

            theorem trans(
                0 A: Type 0,
                0 x: A,
                0 y: A,
                0 z: A,
                0 p: Path(_ => A, x, y),
                0 q: Path(_ => A, y, z),
            ) -> Path(_ => A, x, z) {
                <i> hcom(A, 0, 1, [i = 0 => <j> x, i = 1 => <j> q @ j], p @ i)
            }

            fn cof_branches(0 A: Type 0, 1 x: A) -> A {
                hcom(
                    A,
                    0,
                    1,
                    [
                        top && (0 = 0) => <j> x,
                        bot || (0 = 1) => <j> x,
                    ],
                    x
                )
            }
        ";

        let checked = check_source(src);
        assert!(checked.is_ok(), "unexpected error: {:?}", checked.err());
        if let Ok(module) = checked {
            assert_eq!(module.decls.len(), 11);
            assert_eq!(module.decls[0].kind, apollo_syntax::DeclKind::Fn);
            assert_eq!(module.decls[0].name, "id");
            assert_eq!(module.decls[0].param_names, vec!["A", "x"]);
            assert_eq!(module.decls[4].kind, apollo_syntax::DeclKind::Theorem);
            assert_eq!(module.decls[10].name, "cof_branches");
        }
    }

    #[test]
    fn rejects_linear_violation_duplicates_unknowns_and_bad_paths() {
        let linear_dup = "fn bad(0 A: Type 0, 1 x: A) -> Sigma(1 _: A, A) { (x, x) }";
        let err = check_source(linear_dup).err();
        assert!(matches!(err, Some(ElabError::Type { .. })));
        if let Some(e) = err {
            let diag = e.format_diagnostic("bad.ap", linear_dup);
            assert!(diag.contains("bad.ap:1:1:"));
            assert!(diag.contains("in 'bad'"));
        }

        let dup_decl = "fn f(0 A: Type 0, 1 x: A) -> A { x }\nfn f(0 A: Type 0, 1 x: A) -> A { x }";
        assert!(matches!(
            check_source(dup_decl).err(),
            Some(ElabError::DuplicateDecl { .. })
        ));

        let unknown = "fn f(0 A: Type 0) -> A { missing }";
        assert!(matches!(
            check_source(unknown).err(),
            Some(ElabError::UnknownName { .. })
        ));

        let bad_papp = "fn f(0 A: Type 0, 0 x: A) -> A { x @ 0 }";
        assert!(matches!(
            check_source(bad_papp).err(),
            Some(ElabError::ExpectedPath { .. })
        ));

        let unannotated_let = "fn f(0 A: Type 0, 1 x: A) -> A { ({ let 1 y: A = x; y }).0 }";
        assert!(matches!(
            check_source(unannotated_let).err(),
            Some(ElabError::UnsupportedUnannotatedLet { .. })
        ));

        let pretype_interval = "fn bad_i(0 i: I) -> I { i }";
        assert!(matches!(
            check_source(pretype_interval).err(),
            Some(ElabError::Type {
                err: apollo_kernel::TypeError::ExpectedUniverse,
                ..
            })
        ));

        let bad_parse = "fn (";
        let parse_err = check_source(bad_parse).err();
        assert!(matches!(parse_err, Some(ElabError::Parse(_))));
        if let Some(e) = parse_err {
            assert_eq!(e.span().start, 3);
            assert!(e.to_string().contains("parse error:"));
        }

        for sample in [
            ElabError::DuplicateDecl {
                name: "x".to_owned(),
                span: apollo_syntax::Span::new(0, 1),
            },
            ElabError::UnknownName {
                name: "y".to_owned(),
                span: apollo_syntax::Span::new(0, 1),
            },
            ElabError::ExpectedPath {
                span: apollo_syntax::Span::new(0, 1),
            },
            ElabError::UnsupportedUnannotatedLet {
                span: apollo_syntax::Span::new(0, 1),
            },
            ElabError::InvalidMatch {
                message: "bad".to_owned(),
                span: apollo_syntax::Span::new(0, 1),
            },
        ] {
            assert_eq!(sample.span(), apollo_syntax::Span::new(0, 1));
            assert_ne!(sample.to_string(), "");
        }
    }

    #[test]
    fn elaborates_inductive_types_match_and_dependent_proofs() {
        let src = r"
            fn absurd(0 A: Type 0, 1 v: Void) -> A {
                match v {}
            }

            fn unit_id(1 u: Unit) -> Unit {
                match u { () => () }
            }

            fn not(1 b: Bool) -> Bool {
                match b {
                    true => false,
                    false => true,
                }
            }

            theorem not_not(0 b: Bool) -> Path(_ => Bool, not(not(b)), b) {
                match b as |x| Path(_ => Bool, not(not(x)), x) {
                    true => <i> true,
                    false => <i> false,
                }
            }

            fn pred(1 n: Nat) -> Nat {
                match n {
                    zero => zero,
                    succ(k) => k,
                }
            }

            fn add(1 n: Nat, 1 m: Nat) -> Nat {
                match n {
                    zero => m,
                    succ(_, ih) => succ(ih),
                }
            }

            theorem add_zero_right(0 n: Nat) -> Path(_ => Nat, add(n, zero), n) {
                match n as |x| Path(_ => Nat, add(x, zero), x) {
                    zero => <i> zero,
                    succ(k, ih) => <i> succ(ih @ i),
                }
            }

            fn mul(1 n: Nat, ω m: Nat) -> Nat {
                match n {
                    zero => zero,
                    succ(_, ih) => add(ih, m),
                }
            }
        ";

        let checked = check_source(src);
        assert!(checked.is_ok(), "unexpected error: {:?}", checked.err());
        if let Ok(module) = checked {
            assert_eq!(module.decls.len(), 8);
        }

        for bad in [
            "fn f(0 A: Type 0, 1 x: A) -> A { match x {} }",
            "fn f(1 v: Void) -> Unit { match v { () => () } }",
            "fn f(1 u: Unit) -> Unit { match u {} }",
            "fn f(1 u: Unit) -> Unit { match u { true => () } }",
            "fn f(1 b: Bool) -> Bool { match b { true => false } }",
            "fn f(1 b: Bool) -> Bool { match b { true => false, true => true } }",
            "fn f(1 b: Bool) -> Bool { match b { true => false, true => true, false => false } }",
            "fn f(1 b: Bool) -> Bool { match b { false => true, false => false, true => true } }",
            "fn f(1 n: Nat) -> Nat { match n { zero => zero } }",
            "fn f(1 n: Nat) -> Nat { match n { zero => zero, zero => zero, succ(k) => k } }",
            "fn f(1 n: Nat) -> Nat { match n { zero => zero, succ(k) => k, succ(k) => zero } }",
            "fn f(1 n: Nat) -> Nat { match n { zero => zero, true => zero } }",
            "fn f(1 b: Bool) -> Bool { (match b { true => false, false => true }).0 }",
        ] {
            assert!(
                matches!(
                    check_source(bad).err(),
                    Some(ElabError::InvalidMatch { .. })
                ),
                "expected InvalidMatch for: {bad}"
            );
        }
    }

    #[test]
    fn elaborates_enum_struct_recursion_and_rejects_bad_data() {
        let src = r"
            enum Color { Red, Green, Blue }

            enum Option(0 A: Type 0) {
                None,
                Some(1 val: A),
            }

            enum List(0 A: Type 0) {
                Nil,
                Cons(1 head: A, 1 tail: List(A)),
            }

            struct Point(0 A: Type 0) {
                1 x: A,
                1 y: A,
            }

            struct PairPoint(0 A: Type 0) {
                ω x: A,
                ω y: A,
            }

            fn unwrap_or(0 A: Type 0, 1 o: Option(A), ω d: A) -> A {
                match o {
                    Option::None => d,
                    Option::Some(v) => v,
                }
            }

            fn map_opt(0 A: Type 0, 0 B: Type 0, 1 o: Option(A), ω f: (1 _: A) -> B) -> Option(B) {
                match o {
                    Option::None => Option::None,
                    Option::Some(v) => Option::Some(f(v)),
                }
            }

            fn swap_pt(0 A: Type 0, 1 p: Point(A)) -> Point(A) {
                match p {
                    Point { x, y } => Point { x: y, y: x },
                }
            }

            fn get_x(0 A: Type 0, ω p: PairPoint(A)) -> A {
                p.x
            }

            fn mk_nat_pt() -> Point(Nat) {
                Point(Nat) { x: zero, y: succ(zero) }
            }

            fn append(0 A: Type 0, 1 xs: List(A), ω ys: List(A)) -> List(A) {
                match xs {
                    List::Nil => ys,
                    List::Cons(h, _, ih) => List::Cons(h, ih),
                }
            }

            theorem append_nil_right(
                0 A: Type 0,
                0 xs: List(A),
            ) -> Path(_ => List(A), append(A, xs, List::Nil), xs) {
                match xs as |l| Path(_ => List(A), append(A, l, List::Nil), l) {
                    List::Nil => <i> List::Nil,
                    List::Cons(h, t, ih) => <i> List::Cons(h, ih @ i),
                }
            }
        ";

        let checked = check_source(src);
        assert!(checked.is_ok(), "unexpected error: {:?}", checked.err());
        if let Ok(module) = checked {
            assert_eq!(module.data_decls.len(), 5);
            assert_eq!(module.decls.len(), 7);
        }
    }

    #[test]
    fn rejects_invalid_data_declarations_literals_and_patterns() {
        let bad_pos = check_source("enum Bad { Mk(1 f: (1 _: Bad) -> Void) }").err();
        assert!(matches!(bad_pos, Some(ElabError::Type { .. })));

        for bad_data in [
            "enum D { A, A }",
            "enum E(0 A: Type 0) { Mk } fn f(0 A: Type 0) -> E(A, A) { E::Mk }",
            "enum E { A } fn f() -> E { E::B }",
            "enum E(0 A: Type 0) { Mk(1 _: A) } fn f(0 A: Type 0) -> E(A) { E::Mk }",
            "struct S { 1 x: Nat } fn f() -> S { S { x: zero, x: zero } }",
            "struct S { 1 x: Nat, 1 y: Nat } fn f() -> S { S { x: zero } }",
            "struct S { 1 x: Nat } fn f() -> S { S { y: zero } }",
            "enum E { A } fn f() -> E { E {} }",
            "fn f(1 n: Nat) -> Nat { n.x }",
            "enum E { A } fn f(1 e: E) -> E { e.x }",
            "struct S { ω x: Nat } fn f(1 s: S) -> Nat { s.y }",
        ] {
            let err = check_source(bad_data).err();
            assert!(
                matches!(err, Some(ElabError::InvalidData { .. })),
                "expected InvalidData for: {bad_data}, got: {err:?}"
            );
            if let Some(e) = err {
                assert_ne!(e.to_string(), "");
            }
        }

        for bad_match in [
            "enum E { A, B } fn f(1 e: E) -> Nat { match e { E::A => zero } }",
            "enum E { A, B } fn f(1 e: E) -> Nat { match e { E::A => zero, E::A => zero, E::B => zero } }",
            "enum E { A } fn f(1 e: E) -> Nat { match e { E::B => zero } }",
            "enum E { A(1 _: Nat) } fn f(1 e: E) -> Nat { match e { E::A => zero } }",
            "struct S { 1 x: Nat } fn f(1 s: S) -> Nat { match s { S { y } => y } }",
            "struct S { 1 x: Nat } fn f(1 s: S) -> Nat { match s { S { x, x } => x } }",
            "struct S { 1 x: Nat, 1 y: Nat } fn f(1 s: S) -> Nat { match s { S { x } => x } }",
            "enum E1 { A } enum E2 { A } fn f(1 e: E1) -> Nat { match e { E2::A => zero } }",
            "struct S1 { 1 x: Nat } struct S2 { 1 x: Nat } fn f(1 s: S1) -> Nat { match s { S2 { x } => x } }",
        ] {
            assert!(
                matches!(
                    check_source(bad_match).err(),
                    Some(ElabError::InvalidMatch { .. })
                ),
                "expected InvalidMatch for: {bad_match}"
            );
        }

        // Duplicate data name and fn/data collision.
        for dup in [
            "enum E { A } enum E { B }",
            "fn E() -> Nat { zero } enum E { A }",
        ] {
            assert!(matches!(
                check_source(dup).err(),
                Some(ElabError::DuplicateDecl { .. })
            ));
        }

        // Expected data type mismatch with same parameter count.
        assert!(matches!(
            check_source(
                "enum A(0 T: Type 0) { Mk } enum B(0 T: Type 0) { Mk } fn f() -> A(Nat) { B::Mk }"
            )
            .err(),
            Some(ElabError::InvalidData { .. })
        ));

        // Scope cleanup after data params, struct fields, and multi-binder match branches.
        for leaked in [
            "enum E(0 A: Type 0) { Mk(1 _: A) } fn f() -> Type 0 { A }",
            "struct S { 1 x: Nat } fn f() -> Nat { x }",
            "enum List(0 A: Type 0) { Nil, Cons(ω h: A, 1 t: List(A)) } fn f(1 xs: List(Nat)) -> Nat { match xs { List::Nil => zero, List::Cons(h, _, ih) => ih } } fn after() -> Nat { h }",
            "enum List(0 A: Type 0) { Nil, Cons(ω h: A, 1 t: List(A)) } fn f(1 xs: List(Nat)) -> Nat { match xs { List::Nil => zero, List::Cons(h, _, ih) => ih } } fn after() -> List(Nat) { xs }",
        ] {
            assert!(
                matches!(
                    check_source(leaked).err(),
                    Some(ElabError::UnknownName { .. })
                ),
                "expected UnknownName for: {leaked}"
            );
        }

        // Explicit constructor type args, second struct field projection, and 2-IH Tree recursion.
        let ok_extra = r"
            fn add(1 n: Nat, 1 m: Nat) -> Nat {
                match n { zero => m, succ(_, acc) => succ(acc) }
            }
            enum Option(0 A: Type 0) { None, Some(1 val: A) }
            struct Hetero { ω a: Nat, ω b: Bool }
            enum Tree(0 A: Type 0) { Leaf, Node(1 l: Tree(A), 1 v: A, 1 r: Tree(A)) }
            fn explicit_some() -> Option(Nat) { Option::Some(Nat, zero) }
            fn get_b(ω h: Hetero) -> Bool { h.b }
            fn tree_sum(1 t: Tree(Nat)) -> Nat {
                match t {
                    Tree::Leaf => zero,
                    Tree::Node(_, v, _, ihl, ihr) => add(v, add(ihl, ihr)),
                }
            }
        ";
        assert!(check_source(ok_extra).is_ok());
    }

    #[test]
    fn elaborates_vtypes_univalence_vin_and_vproj() {
        let src = r"
            fn not(1 b: Bool) -> Bool {
                match b { true => false, false => true }
            }
            theorem not_not(0 b: Bool) -> Path(_ => Bool, not(not(b)), b) {
                match b as |x| Path(_ => Bool, not(not(x)), x) {
                    true => <i> true,
                    false => <i> false,
                }
            }
            theorem Equiv(0 A: Type 0, 0 B: Type 0) -> Type 0 {
                Sigma(0 f: (1 _: A) -> B, Sigma(0 g: (1 _: B) -> A, Sigma(0 sec: (0 b: B) -> Path(_ => B, f(g(b)), b), (0 a: A) -> Path(_ => A, g(f(a)), a))))
            }
            theorem not_equiv() -> Equiv(Bool, Bool) {
                (not, (not, (not_not, not_not)))
            }
            theorem ua(0 A: Type 0, 0 B: Type 0, 0 e: Equiv(A, B)) -> Path(_ => Type 0, A, B) {
                <i> V(i, A, B, e)
            }
            theorem bool_flip() -> Path(_ => Type 0, Bool, Bool) {
                ua(Bool, Bool, not_equiv)
            }
            theorem flip_dep() -> Path(i => bool_flip @ i, true, false) {
                <i> vin(i, true, false)
            }
            theorem vp_zero() -> Path(_ => Bool, vproj(0, Bool, Bool, not_equiv, true), false) {
                <i> false
            }
            enum Opt(0 A: Type 0) { None, Some(1 v: A) }
            fn id_opt(1 o: Opt(Bool)) -> Opt(Bool) { o }
            theorem id_opt_eq(0 o: Opt(Bool)) -> Path(_ => Opt(Bool), id_opt(id_opt(o)), o) {
                <i> o
            }
            theorem id_opt_equiv() -> Equiv(Opt(Bool), Opt(Bool)) {
                (id_opt, (id_opt, (id_opt_eq, id_opt_eq)))
            }
            theorem vin_inferred_ctor() -> Path(i => V(i, Opt(Bool), Opt(Bool), id_opt_equiv), (Opt::None : Opt(Bool)), (Opt::None : Opt(Bool))) {
                <i> vin(i, Opt::None, Opt::None)
            }
            fn flip_ua(1 b: Bool) -> Bool {
                coe(i => bool_flip @ i, 0, 1, b)
            }
        ";
        let checked = check_source(src);
        assert!(checked.is_ok(), "unexpected error: {:?}", checked.err());
        if let Ok(module) = checked {
            assert_eq!(module.decls.len(), 13);
        }
        assert!(matches!(
            check_source("theorem bad() -> Unit { I }"),
            Err(ElabError::Type {
                err: apollo_kernel::TypeError::ExpectedUniverse,
                ..
            })
        ));
    }

    #[test]
    fn elaborates_hits_s1_upair_trunc_and_rejects_incoherent_branches() {
        let src = r"
            enum S1 {
                Base,
                Loop(<i>) = S1::Base .. S1::Base,
            }
            fn not(1 b: Bool) -> Bool {
                match b { true => false, false => true }
            }
            theorem not_not(0 b: Bool) -> Path(_ => Bool, not(not(b)), b) {
                match b as |x| Path(_ => Bool, not(not(x)), x) {
                    true => <i> true,
                    false => <i> false,
                }
            }
            theorem Equiv(0 A: Type 0, 0 B: Type 0) -> Type 0 {
                Sigma(0 f: (1 _: A) -> B, Sigma(0 g: (1 _: B) -> A, Sigma(0 sec: (0 b: B) -> Path(_ => B, f(g(b)), b), (0 a: A) -> Path(_ => A, g(f(a)), a))))
            }
            theorem not_equiv() -> Equiv(Bool, Bool) {
                (not, (not, (not_not, not_not)))
            }
            theorem double_cover(1 x: S1) -> Type 0 {
                match x as |_| Type 0 {
                    S1::Base => Bool,
                    S1::Loop(i) => V(i, Bool, Bool, not_equiv),
                }
            }
            theorem loop_flips() -> Path(_ => Bool, coe(i => double_cover(S1::Loop(i)), 0, 1, true), false) {
                <i> false
            }
            enum UPair(0 A: Type 0) {
                Pair(1 a: A, 1 b: A),
                Swap(1 a: A, 1 b: A, <i>) = UPair::Pair(a, b) .. UPair::Pair(b, a),
            }
            fn swapped_explicit(1 a: Bool, 1 b: Bool) -> UPair(Bool) {
                UPair::Swap(Bool, a, b, 1)
            }
            enum RecS1 {
                Base,
                Step(1 next: RecS1, <i>) = RecS1::Base .. RecS1::Base,
            }
            fn rec_s1_const(1 r: RecS1) -> Unit {
                match r {
                    RecS1::Base => (),
                    RecS1::Step(_next, _i) => (),
                }
            }
            enum Trunc(0 A: Type 0) {
                In(1 x: A),
                Squash(1 x: Trunc(A), 1 y: Trunc(A), <i>) = x .. y,
            }
            fn trunc_rec(
                0 A: Type 0,
                0 B: Type 0,
                1 f: (1 _: A) -> B,
                0 prop: (0 x: B, 0 y: B) -> Path(_ => B, x, y),
                1 t: Trunc(A),
            ) -> B {
                match t {
                    Trunc::In(x) => f(x),
                    Trunc::Squash(x, y, ih_x, ih_y, i) => (prop(ih_x, ih_y)) @ i,
                }
            }
        ";
        let checked = check_source(src);
        assert!(checked.is_ok(), "unexpected error: {:?}", checked.err());
        if let Ok(m) = checked {
            assert_eq!(m.data_decls.len(), 4);
            assert!(m.data_decls[0].ctors[1].is_path);
        }

        let bad_hit = r"
            enum S1 { Base, Loop(<i>) = S1::Base .. S1::Base }
            fn bad(1 x: S1) -> Bool {
                match x { S1::Base => true, S1::Loop(i) => false }
            }
        ";
        assert!(matches!(
            check_source(bad_hit),
            Err(ElabError::Type {
                err: apollo_kernel::TypeError::HitBoundaryMismatch,
                ..
            })
        ));
        let bad_binders = r"
            enum S1 { Base, Loop(<i>) = S1::Base .. S1::Base }
            fn bad(1 x: S1) -> Bool {
                match x { S1::Base => true, S1::Loop => true }
            }
        ";
        assert!(matches!(
            check_source(bad_binders),
            Err(ElabError::InvalidMatch { .. })
        ));
        let bad_args = r"
            enum S1 { Base, Loop(<i>) = S1::Base .. S1::Base }
            theorem bad() -> S1 { S1::Loop }
        ";
        assert!(matches!(
            check_source(bad_args),
            Err(ElabError::InvalidData { .. })
        ));
    }

    #[test]
    fn elaborates_builtin_addition_with_definitional_computation() {
        let src = r"
            fn add(1 n: Nat, 1 m: Nat) -> Nat {
                match n { zero => m, succ(_, ih) => succ(ih) }
            }
            fn plus(1 a: Nat, 1 b: Nat) -> Nat { a + b }
            fn double(ω n: Nat) -> Nat { n + n }
            theorem zero_plus(0 n: Nat) -> Path(_ => Nat, zero + n, n) { <i> n }
            theorem succ_plus(0 a: Nat, 0 b: Nat) -> Path(_ => Nat, succ(a) + b, succ(a + b)) {
                <i> succ(a + b)
            }
            theorem two_plus_one() -> Path(_ => Nat, succ(succ(zero)) + succ(zero), succ(succ(succ(zero)))) {
                <i> succ(succ(succ(zero)))
            }
            theorem plus_is_add(0 a: Nat, 0 b: Nat) -> Path(_ => Nat, a + b, add(a, b)) {
                <i> a + b
            }
            theorem plus_zero(0 n: Nat) -> Path(_ => Nat, n + zero, n) {
                match n as |x| Path(_ => Nat, x + zero, x) {
                    zero => <i> zero,
                    succ(k, ih) => <i> succ(ih @ i),
                }
            }
        ";
        let checked = check_source(src);
        assert!(checked.is_ok(), "unexpected error: {:?}", checked.err());

        for bad in [
            "fn bad(1 b: Bool) -> Nat { b + zero }",
            "fn bad(1 n: Nat) -> Nat { n + n }",
            "theorem bad(0 a: Nat, 0 b: Nat) -> Path(_ => Nat, a + b, b + a) { <i> a + b }",
        ] {
            assert!(
                matches!(check_source(bad), Err(ElabError::Type { .. })),
                "expected type error for: {bad}"
            );
        }
    }

    #[test]
    fn proves_linear_nat_identities_with_auto() {
        let src = r"
            theorem comm(0 a: Nat, 0 b: Nat) -> Path(_ => Nat, a + b, b + a) { auto }
            theorem assoc(0 a: Nat, 0 b: Nat, 0 c: Nat) -> Path(_ => Nat, (a + b) + c, a + (b + c)) {
                auto
            }
            theorem unit_right(0 a: Nat) -> Path(_ => Nat, a + zero, a) { auto }
            theorem shift(0 a: Nat, 0 b: Nat) -> Path(_ => Nat, succ(a) + b, a + succ(b)) { auto }
            theorem spread(0 a: Nat, 0 b: Nat, 0 c: Nat) -> Path(
                _ => Nat,
                succ(c) + (b + succ(a + c)),
                (a + c) + (succ(succ(b)) + c)
            ) {
                auto
            }
            theorem numerals() -> Path(_ => Nat, succ(zero) + succ(zero), succ(succ(zero))) { auto }
            theorem by_cases(0 n: Nat) -> Path(_ => Nat, n + zero, n) {
                match n as |x| Path(_ => Nat, x + zero, x) {
                    zero => auto,
                    succ(k, ih) => auto,
                }
            }
            fn pred_or(ω n: Nat, ω m: Nat) -> Nat { match n { zero => m, succ(k, _) => succ(k) } }
            fn bump_or(ω n: Nat, ω m: Nat) -> Nat { match n { zero => m, succ(_, _) => succ(m) } }
            fn dbl(ω n: Nat) -> Nat { match n { zero => zero, succ(_, ih) => succ(succ(ih)) } }
            theorem pred_atom(0 a: Nat, 0 b: Nat) -> Path(_ => Nat, pred_or(a, b) + zero, pred_or(a, b)) {
                auto
            }
            theorem bump_atom(0 a: Nat, 0 b: Nat) -> Path(_ => Nat, bump_or(a, b) + zero, bump_or(a, b)) {
                auto
            }
            theorem dbl_atom(0 a: Nat) -> Path(_ => Nat, dbl(a) + succ(zero), succ(dbl(a))) { auto }
            fn refined(1 n: Nat) -> Sigma(1 m: Nat, Path(_ => Nat, m + zero, m)) { (n, auto) }
            fn tagged(0 n: Nat) -> Sigma(1 _: Nat, Path(_ => Nat, n + zero, n)) { (zero, auto) }
        ";
        let checked = check_source(src);
        assert!(checked.is_ok(), "unexpected error: {:?}", checked.err());
        if let Ok(module) = checked {
            assert_eq!(module.decls.len(), 15);
        }
        assert!(matches!(
            check_source(
                "fn bad(1 n: Nat) -> Sigma(1 m: Nat, Path(_ => Nat, m, n)) { (zero, auto) }"
            ),
            Err(ElabError::AutoFailed { lhs, rhs, .. }) if lhs == "zero" && rhs == "n"
        ));
    }

    #[test]
    fn proves_congruence_goals_from_path_hypotheses_with_auto() {
        let src = r"
            theorem refl_bool() -> Path(_ => Bool, true, true) { auto }
            theorem ap2(
                0 A: Type 0,
                0 f: (ω _: A) -> A,
                0 x: A,
                0 y: A,
                0 p: Path(_ => A, x, y),
            ) -> Path(_ => A, f(f(x)), f(f(y))) {
                auto
            }
            theorem chain(
                0 A: Type 0,
                0 x: A,
                0 y: A,
                0 z: A,
                0 p: Path(_ => A, x, y),
                0 q: Path(_ => A, z, y),
            ) -> Path(_ => A, x, z) {
                auto
            }
            theorem binary(
                0 A: Type 0,
                0 g: (ω _: A, ω _: A) -> A,
                0 x: A,
                0 y: A,
                0 p: Path(_ => A, y, x),
            ) -> Path(_ => A, g(x, y), g(y, x)) {
                auto
            }
            enum Box(0 A: Type 0) { Mk(1 v: A) }
            theorem ctor_cong(
                0 x: Nat,
                0 y: Nat,
                0 p: Path(_ => Nat, x, y),
            ) -> Path(_ => Box(Nat), Box::Mk(Nat, x), Box::Mk(Nat, y)) {
                auto
            }
            theorem mixed(
                0 a: Nat,
                0 b: Nat,
                0 c: Nat,
                0 p: Path(_ => Nat, a, b),
            ) -> Path(_ => Nat, a + c, c + b) {
                auto
            }
            theorem through_sum(
                0 a: Nat,
                0 b: Nat,
                0 c: Nat,
                0 p: Path(_ => Nat, a + b, c),
            ) -> Path(_ => Nat, b + a, c) {
                auto
            }
            theorem under_map(
                0 A: Type 0,
                0 f: (ω _: Nat) -> A,
                0 a: Nat,
                0 b: Nat,
                0 p: Path(_ => Nat, a + b, b),
            ) -> Path(_ => A, f(b + a), f(b)) {
                auto
            }
            theorem under_succ(
                0 f: (ω _: Nat) -> Nat,
                0 a: Nat,
                0 b: Nat,
                0 p: Path(_ => Nat, b + a, f(a)),
            ) -> Path(_ => Nat, succ(a + b), succ(f(a))) {
                auto
            }
        ";
        let checked = check_source(src);
        assert!(checked.is_ok(), "unexpected error: {:?}", checked.err());
        if let Ok(module) = checked {
            assert_eq!(module.decls.len(), 9);
        }
    }

    #[test]
    fn reports_auto_failures_with_named_normal_forms() {
        let unprovable =
            "theorem bad(0 a: Nat, 0 b: Nat) -> Path(_ => Nat, a + b, succ(a)) { auto }";
        let err = check_source(unprovable).err();
        assert!(
            matches!(
                &err,
                Some(ElabError::AutoFailed { lhs, rhs, lhs_normal, rhs_normal, span })
                    if lhs == "a + b"
                        && rhs == "succ(a)"
                        && lhs_normal.contains('a')
                        && lhs_normal.contains('b')
                        && lhs_normal == "a + (b + zero)"
                        && rhs_normal == "a + succ(zero)"
                        && span.start == 66
            ),
            "unexpected: {err:?}"
        );
        if let Some(e) = err {
            let text = e.to_string();
            assert!(text.contains("auto could not prove a + b = succ(a)"));
            assert!(text.contains("normal forms are"));
        }

        let wrong_bool = "theorem bad() -> Path(_ => Bool, true, false) { auto }";
        assert!(matches!(
            check_source(wrong_bool),
            Err(ElabError::AutoFailed { lhs_normal, rhs_normal, .. })
                if lhs_normal == "true" && rhs_normal == "false"
        ));

        let unused_hyp = r"
            theorem bad(0 A: Type 0, 0 x: A, 0 y: A, 0 z: A, 0 p: Path(_ => A, x, y)) -> Path(_ => A, x, z) {
                auto
            }
        ";
        assert!(matches!(
            check_source(unused_hyp),
            Err(ElabError::AutoFailed { lhs, rhs, .. }) if lhs == "x" && rhs == "z"
        ));

        for (src, needle) in [
            (
                "fn bad(1 n: Nat) -> Nat { auto }",
                "non-dependent Path goal",
            ),
            (
                "fn bad(1 n: Nat) -> Sigma(1 _: Nat, Nat) { (auto, n) }",
                "non-dependent Path goal",
            ),
            ("fn bad() -> Nat { (auto).0 }", "known Path goal"),
        ] {
            let err = check_source(src).err();
            assert!(
                matches!(&err, Some(ElabError::AutoUnsupported { message, .. }) if message.contains(needle)),
                "unexpected for {src}: {err:?}"
            );
            if let Some(e) = err {
                assert!(e.to_string().starts_with("auto: "));
                assert_ne!(e.span(), apollo_syntax::Span::new(0, 0));
            }
        }

        let dependent = r"
            fn not(1 b: Bool) -> Bool { match b { true => false, false => true } }
            theorem not_not(0 b: Bool) -> Path(_ => Bool, not(not(b)), b) {
                match b as |x| Path(_ => Bool, not(not(x)), x) { true => <i> true, false => <i> false }
            }
            theorem Equiv(0 A: Type 0, 0 B: Type 0) -> Type 0 {
                Sigma(0 f: (1 _: A) -> B, Sigma(0 g: (1 _: B) -> A, Sigma(0 sec: (0 b: B) -> Path(_ => B, f(g(b)), b), (0 a: A) -> Path(_ => A, g(f(a)), a))))
            }
            theorem not_equiv() -> Equiv(Bool, Bool) { (not, (not, (not_not, not_not))) }
            theorem flip() -> Path(i => V(i, Bool, Bool, not_equiv), true, false) { auto }
        ";
        assert!(matches!(
            check_source(dependent),
            Err(ElabError::AutoUnsupported { message, .. }) if message.contains("non-dependent")
        ));
    }

    #[test]
    fn scopes_hit_binders_and_checks_boundaries_at_field_depth() {
        let leaked_field = r"
            enum UPair(0 A: Type 0) {
                Pair(1 a: A, 1 b: A),
                Swap(1 a: A, 1 b: A, <i>) = UPair::Pair(a, b) .. UPair::Pair(b, a),
            }
            fn after() -> Nat { a }
        ";
        assert!(matches!(
            check_source(leaked_field),
            Err(ElabError::UnknownName { .. })
        ));

        let short_binders = r"
            enum Bin { Leaf, Join(1 l: Bin, 1 r: Bin, <i>) = Bin::Leaf .. Bin::Leaf }
            fn bin_unit(1 t: Bin) -> Unit {
                match t { Bin::Leaf => (), Bin::Join(l, r, i) => () }
            }
            enum Stack { Empty, Push(ω head: Nat, ω rest: Stack) }
            fn head_or_zero(1 s: Stack) -> Nat {
                match s { Stack::Empty => zero, Stack::Push(head, rest) => head }
            }
        ";
        let checked = check_source(short_binders);
        assert!(checked.is_ok(), "unexpected error: {:?}", checked.err());

        let after_hit_match = r"
            enum RecS1 { Base, Step(1 next: RecS1, <i>) = RecS1::Base .. RecS1::Base }
            fn after_match(1 r: RecS1, 1 n: Nat) -> Sigma(1 _: Unit, Nat) {
                (match r as |_| Unit { RecS1::Base => (), RecS1::Step(_next, _i) => () }, n)
            }
        ";
        let checked = check_source(after_hit_match);
        assert!(checked.is_ok(), "unexpected error: {:?}", checked.err());

        let field_capture = r"
            enum Cyl(0 A: Type 0) { Pt(ω a: A), Seg(ω a: A, <i>) = Cyl::Pt(a) .. Cyl::Pt(a) }
            fn bad(0 A: Type 0, 1 c: Cyl(A)) -> (ω _: A) -> A {
                match c { Cyl::Pt(a) => |ω z| z, Cyl::Seg(a, i) => |ω z| a }
            }
        ";
        assert!(matches!(
            check_source(field_capture),
            Err(ElabError::Type {
                err: apollo_kernel::TypeError::HitBoundaryMismatch,
                ..
            })
        ));
    }
}
