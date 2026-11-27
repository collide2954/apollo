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
            | Self::Type { span, .. } => *span,
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
            decl_name: String::new(),
        }
    }

    pub(crate) fn push_var(&mut self, name: String, ty: Value) -> Value {
        let var = self.ctx.push(ty);
        self.env.push(var.clone());
        self.locals.push(name);
        var
    }

    fn push_dim(&mut self, name: String) -> Value {
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
            ExprKind::Pair { first, second } => {
                let first_id = self.elab_expr(first, None)?;
                let second_id = self.elab_expr(second, None)?;
                Ok(self.arena.pair(first_id, second_id))
            }
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
            | ExprKind::Succ(_) => self.elab_primitive(&expr.kind),
            ExprKind::Match {
                scrut,
                motive,
                arms,
            } => self.elab_match(scrut, motive.as_ref(), arms, expected, expr.span),
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
        ] {
            assert!(
                matches!(
                    check_source(bad_match).err(),
                    Some(ElabError::InvalidMatch { .. })
                ),
                "expected InvalidMatch for: {bad_match}"
            );
        }
    }
}
