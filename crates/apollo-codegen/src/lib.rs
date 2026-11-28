mod data;
pub mod escape;
pub mod ir;

use std::collections::{BTreeSet, HashMap};
use std::fmt;
use std::sync::Arc;

use apollo_elab::{CheckedDecl, CheckedModule, ElabError, check_source};
use apollo_kernel::nbe::{Closure, EvalError, Neutral, Value, eval, quote};
use apollo_kernel::{Ctx, Multiplicity, Term, TermArena, TermId, TypeError, infer};
use apollo_syntax::DeclKind;

use crate::escape::escape_ident;
use crate::ir::{FnKind, RustExpr, RustFn, RustModule, RustParam, RustType};
use apollo_syntax::DataKind;

#[must_use]
pub const fn version() -> &'static str {
    env!("CARGO_PKG_VERSION")
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CodegenError {
    Eval { decl: String, err: EvalError },
    Type { decl: String, err: TypeError },
    UnreducibleCubical { decl: String },
    UnsupportedType { decl: String },
    UnsupportedExpr { decl: String },
    InvalidTerm { decl: String },
}

impl fmt::Display for CodegenError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Eval { decl, err } => write!(f, "in '{decl}': evaluation failed: {err}"),
            Self::Type { decl, err } => write!(f, "in '{decl}': type inspection failed: {err}"),
            Self::UnreducibleCubical { decl } => {
                write!(
                    f,
                    "in '{decl}': cannot extract un-reducible cubical operation to safe Rust"
                )
            }
            Self::UnsupportedType { decl } => {
                write!(f, "in '{decl}': unsupported type for Rust extraction")
            }
            Self::UnsupportedExpr { decl } => {
                write!(f, "in '{decl}': unsupported expression for Rust extraction")
            }
            Self::InvalidTerm { decl } => write!(f, "in '{decl}': invalid term in checked module"),
        }
    }
}

impl std::error::Error for CodegenError {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CompileError {
    Elab(ElabError),
    Codegen(CodegenError),
}

impl From<ElabError> for CompileError {
    fn from(value: ElabError) -> Self {
        Self::Elab(value)
    }
}

impl From<CodegenError> for CompileError {
    fn from(value: CodegenError) -> Self {
        Self::Codegen(value)
    }
}

impl fmt::Display for CompileError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Elab(err) => write!(f, "{err}"),
            Self::Codegen(err) => write!(f, "{err}"),
        }
    }
}

impl std::error::Error for CompileError {}

pub fn emit_module(module: &CheckedModule) -> Result<String, CodegenError> {
    let mut arena = module.arena.clone();
    let (data_defs, data_metas, uses_alloc) =
        DeclLowerer::lower_data_defs(&mut arena, &module.data_decls)?;
    let mut globals = HashMap::new();
    let mut functions = Vec::new();

    for decl in &module.decls {
        if decl.kind == DeclKind::Theorem {
            continue;
        }
        if let Some((rust_fn, sig)) = lower_decl(&mut arena, &globals, &data_metas, decl)? {
            let _ = globals.insert((decl.ty, decl.body), sig);
            functions.push(rust_fn);
        }
    }

    Ok(RustModule {
        uses_alloc,
        data_defs,
        functions,
    }
    .render())
}

pub fn compile_source(source: &str) -> Result<String, CompileError> {
    let checked = check_source(source)?;
    let rust_code = emit_module(&checked)?;
    Ok(rust_code)
}

#[derive(Debug, Clone)]
pub(crate) struct LoweredCtorMeta {
    pub(crate) rust_name: String,
    pub(crate) field_keep: Vec<bool>,
    pub(crate) field_names: Vec<String>,
    pub(crate) field_rec: Vec<bool>,
}

#[derive(Debug, Clone)]
pub(crate) struct LoweredDataMeta {
    pub(crate) rust_name: String,
    pub(crate) kind: DataKind,
    pub(crate) param_keep: Vec<bool>,
    pub(crate) ctors: Vec<LoweredCtorMeta>,
}

#[derive(Debug, Clone)]
pub(crate) struct GlobalSig {
    rust_name: String,
    param_keep: Vec<bool>,
}

#[derive(Debug, Clone)]
pub(crate) enum Binding {
    TypeParam(String),
    Erased,
    Runtime {
        id: usize,
        name: String,
        ty: RustType,
        is_boxed: bool,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SigmaShape {
    ErasedFirst,
    ErasedSecond,
    Both,
}

pub(crate) const fn is_erased_value_type(val: &Value) -> bool {
    matches!(
        val,
        Value::Path { .. } | Value::Universe(_) | Value::Interval
    )
}

pub(crate) struct DeclLowerer<'a> {
    pub(crate) arena: &'a mut TermArena,
    globals: &'a HashMap<(TermId, TermId), GlobalSig>,
    pub(crate) data_metas: &'a [LoweredDataMeta],
    pub(crate) decl_name: String,
    ctx: Ctx,
    pub(crate) env: Vec<Value>,
    pub(crate) bindings: Vec<Binding>,
    next_local_id: usize,
    next_rec_id: usize,
}

impl<'a> DeclLowerer<'a> {
    pub(crate) fn new(
        arena: &'a mut TermArena,
        globals: &'a HashMap<(TermId, TermId), GlobalSig>,
        data_metas: &'a [LoweredDataMeta],
        decl_name: String,
    ) -> Self {
        Self {
            arena,
            globals,
            data_metas,
            decl_name,
            ctx: Ctx::new(),
            env: Vec::new(),
            bindings: Vec::new(),
            next_local_id: 0,
            next_rec_id: 0,
        }
    }

    pub(crate) const fn alloc_id(&mut self) -> usize {
        let id = self.next_local_id;
        self.next_local_id += 1;
        id
    }

    pub(crate) const fn alloc_rec_id(&mut self) -> usize {
        let id = self.next_rec_id;
        self.next_rec_id += 1;
        id
    }

    pub(crate) fn push_binding(&mut self, ty_val: Value, binding: Binding) -> Value {
        let var = self.ctx.push(ty_val);
        self.env.push(var.clone());
        self.bindings.push(binding);
        var
    }

    pub(crate) fn pop_binding(&mut self) {
        self.ctx.pop();
        let _ = self.env.pop();
        let _ = self.bindings.pop();
    }

    pub(crate) fn eval_term(&self, id: TermId) -> Result<Value, CodegenError> {
        eval(self.arena, &self.env, id).map_err(|err| CodegenError::Eval {
            decl: self.decl_name.clone(),
            err,
        })
    }

    fn infer_val_ty(&mut self, id: TermId) -> Result<Value, CodegenError> {
        infer(self.arena, &mut self.ctx, Multiplicity::Zero, id)
            .map(|(ty, _)| ty)
            .map_err(|err| CodegenError::Type {
                decl: self.decl_name.clone(),
                err,
            })
    }

    fn sigma_shape(
        &self,
        mult: Multiplicity,
        second: &Closure,
    ) -> Result<SigmaShape, CodegenError> {
        if mult.is_erased() {
            return Ok(SigmaShape::ErasedFirst);
        }
        let fresh = Value::var(apollo_kernel::DeBruijnLevel(self.ctx.depth()));
        let second_val = second
            .apply(self.arena, fresh)
            .map_err(|err| CodegenError::Eval {
                decl: self.decl_name.clone(),
                err,
            })?;
        if is_erased_value_type(&second_val) {
            Ok(SigmaShape::ErasedSecond)
        } else {
            Ok(SigmaShape::Both)
        }
    }

    pub(crate) fn lower_val_ty(
        &mut self,
        val: &Value,
        fn_mult: Multiplicity,
    ) -> Result<RustType, CodegenError> {
        match val {
            Value::Unit => Ok(RustType::Unit),
            Value::Void => Ok(RustType::Void),
            Value::Bool => Ok(RustType::Bool),
            Value::Nat => Ok(RustType::Nat),
            Value::Data { id, params } => self.lower_data_type(*id, params),
            Value::Neutral(neutral) => match neutral.as_ref() {
                Neutral::Var(level) => match self.bindings.get(level.0 as usize) {
                    Some(Binding::TypeParam(name)) => Ok(RustType::Named(name.clone())),
                    _ => Err(CodegenError::UnsupportedType {
                        decl: self.decl_name.clone(),
                    }),
                },
                _ => Err(CodegenError::UnsupportedType {
                    decl: self.decl_name.clone(),
                }),
            },
            Value::Sigma {
                mult,
                first,
                second,
            } => match self.sigma_shape(*mult, second)? {
                SigmaShape::ErasedFirst => {
                    let fresh = self.push_binding((**first).clone(), Binding::Erased);
                    let second_val =
                        second
                            .apply(self.arena, fresh)
                            .map_err(|err| CodegenError::Eval {
                                decl: self.decl_name.clone(),
                                err,
                            })?;
                    let res = self.lower_val_ty(&second_val, Multiplicity::One);
                    self.pop_binding();
                    res
                }
                SigmaShape::ErasedSecond => self.lower_val_ty(first, Multiplicity::One),
                SigmaShape::Both => {
                    let fst_ty = self.lower_val_ty(first, Multiplicity::One)?;
                    let fresh = self.push_binding((**first).clone(), Binding::Erased);
                    let second_val =
                        second
                            .apply(self.arena, fresh)
                            .map_err(|err| CodegenError::Eval {
                                decl: self.decl_name.clone(),
                                err,
                            })?;
                    let snd_res = self.lower_val_ty(&second_val, Multiplicity::One);
                    self.pop_binding();
                    Ok(RustType::Tuple(Box::new(fst_ty), Box::new(snd_res?)))
                }
            },
            Value::Pi { .. } => self.lower_pi_ty(val, fn_mult),
            _ => Err(CodegenError::UnsupportedType {
                decl: self.decl_name.clone(),
            }),
        }
    }

    fn lower_pi_ty(
        &mut self,
        val: &Value,
        fn_mult: Multiplicity,
    ) -> Result<RustType, CodegenError> {
        let mut cur = val.clone();
        let mut params = Vec::new();
        let mut pushed = 0_usize;
        while let Value::Pi {
            mult,
            domain,
            codomain,
        } = cur
        {
            if !mult.is_erased() {
                let param_ty = self.lower_val_ty(&domain, mult)?;
                params.push(param_ty);
            }
            let fresh = self.push_binding((*domain).clone(), Binding::Erased);
            pushed += 1;
            cur = codomain
                .apply(self.arena, fresh)
                .map_err(|err| CodegenError::Eval {
                    decl: self.decl_name.clone(),
                    err,
                })?;
        }
        let ret_res = self.lower_val_ty(&cur, Multiplicity::One);
        for _ in 0..pushed {
            self.pop_binding();
        }
        let kind = if fn_mult == Multiplicity::Many {
            FnKind::Fn
        } else {
            FnKind::FnOnce
        };
        Ok(RustType::Callable {
            kind,
            params,
            ret: Box::new(ret_res?),
        })
    }

    pub(crate) fn lower_expr(
        &mut self,
        id: TermId,
        expected: Option<&Value>,
    ) -> Result<RustExpr, CodegenError> {
        let term = self
            .arena
            .get(id)
            .cloned()
            .ok_or_else(|| CodegenError::InvalidTerm {
                decl: self.decl_name.clone(),
            })?;

        match term {
            Term::Var(index) => {
                let pos = self
                    .bindings
                    .len()
                    .checked_sub(1 + index.0 as usize)
                    .ok_or_else(|| CodegenError::InvalidTerm {
                        decl: self.decl_name.clone(),
                    })?;
                match self.bindings.get(pos) {
                    Some(Binding::Runtime {
                        id, name, is_boxed, ..
                    }) => {
                        let local = RustExpr::Local {
                            id: *id,
                            name: name.clone(),
                        };
                        if *is_boxed {
                            Ok(RustExpr::Deref(Box::new(local)))
                        } else {
                            Ok(local)
                        }
                    }
                    _ => Err(CodegenError::UnsupportedExpr {
                        decl: self.decl_name.clone(),
                    }),
                }
            }
            Term::Ann { term: inner, ty } => {
                if let Some(sig) = self.globals.get(&(ty, inner)) {
                    let global = RustExpr::Global(sig.rust_name.clone());
                    return if sig.param_keep.is_empty() {
                        Ok(RustExpr::Call {
                            callee: Box::new(global),
                            args: Vec::new(),
                        })
                    } else {
                        Ok(global)
                    };
                }
                let ty_val = self.eval_term(ty)?;
                self.lower_expr(inner, Some(&ty_val))
            }
            Term::App { .. } => self.lower_app(id, expected),
            Term::Lam { .. } => self.lower_lam(id, expected),
            Term::Pair { first, second } => self.lower_pair(first, second, expected),
            Term::Fst(pair) => self.lower_proj(pair, true),
            Term::Snd(pair) => self.lower_proj(pair, false),
            Term::Coe { .. }
            | Term::HCom { .. }
            | Term::PApp { .. }
            | Term::VIn { .. }
            | Term::VProj { .. } => self.lower_cubical(id, expected),
            Term::Ctor {
                id: did,
                ctor,
                params,
                args,
            } => {
                if self
                    .arena
                    .get_inductive(did)
                    .and_then(|d| d.ctors.get(ctor as usize))
                    .is_some_and(apollo_kernel::CtorDecl::is_path)
                {
                    return self.lower_cubical(id, expected);
                }
                self.lower_ctor(did, ctor, &params, &args)
            }
            Term::DataElim {
                id,
                params,
                motive,
                branches,
                scrut,
            } => self.lower_data_elim(id, &params, motive, &branches, scrut, expected),
            _ => self.lower_inductive(&term),
        }
    }

    fn lower_inductive(&mut self, term: &Term) -> Result<RustExpr, CodegenError> {
        match *term {
            Term::Tt => Ok(RustExpr::Tt),
            Term::True => Ok(RustExpr::BoolLit(true)),
            Term::False => Ok(RustExpr::BoolLit(false)),
            Term::Zero => Ok(RustExpr::NatLit(0)),
            Term::Succ(pred) => match self.lower_expr(pred, Some(&Value::Nat))? {
                RustExpr::NatLit(val) => Ok(val.checked_add(1).map_or_else(
                    || RustExpr::Succ(Box::new(RustExpr::NatLit(val))),
                    RustExpr::NatLit,
                )),
                other => Ok(RustExpr::Succ(Box::new(other))),
            },
            Term::VoidElim { scrut, .. } => {
                let scrut_expr = self.lower_expr(scrut, Some(&Value::Void))?;
                Ok(RustExpr::VoidMatch(Box::new(scrut_expr)))
            }
            Term::UnitElim {
                motive,
                on_unit,
                scrut,
            } => {
                let scrut_expr = self.lower_expr(scrut, Some(&Value::Unit))?;
                let motive_cl = Closure::new(self.env.clone(), motive);
                let unit_ty =
                    motive_cl
                        .apply(self.arena, Value::Tt)
                        .map_err(|err| CodegenError::Eval {
                            decl: self.decl_name.clone(),
                            err,
                        })?;
                let body_expr = self.lower_expr(on_unit, Some(&unit_ty))?;
                Ok(RustExpr::UnitMatch {
                    scrut: Box::new(scrut_expr),
                    body: Box::new(body_expr),
                })
            }
            Term::BoolElim {
                motive,
                on_true,
                on_false,
                scrut,
            } => {
                let scrut_expr = self.lower_expr(scrut, Some(&Value::Bool))?;
                let motive_cl = Closure::new(self.env.clone(), motive);
                let true_ty =
                    motive_cl
                        .apply(self.arena, Value::True)
                        .map_err(|err| CodegenError::Eval {
                            decl: self.decl_name.clone(),
                            err,
                        })?;
                let false_ty = motive_cl.apply(self.arena, Value::False).map_err(|err| {
                    CodegenError::Eval {
                        decl: self.decl_name.clone(),
                        err,
                    }
                })?;
                let true_expr = self.lower_expr(on_true, Some(&true_ty))?;
                let false_expr = self.lower_expr(on_false, Some(&false_ty))?;
                Ok(RustExpr::BoolMatch {
                    scrut: Box::new(scrut_expr),
                    on_true: Box::new(true_expr),
                    on_false: Box::new(false_expr),
                })
            }
            Term::NatElim {
                motive,
                base,
                step,
                scrut,
            } => self.lower_nat_elim(motive, base, step, scrut),
            _ => Err(CodegenError::UnsupportedExpr {
                decl: self.decl_name.clone(),
            }),
        }
    }

    fn lower_nat_elim(
        &mut self,
        motive: TermId,
        base: TermId,
        step: TermId,
        scrut: TermId,
    ) -> Result<RustExpr, CodegenError> {
        let scrut_expr = self.lower_expr(scrut, Some(&Value::Nat))?;
        let motive_cl = Closure::new(self.env.clone(), motive);
        let base_ty =
            motive_cl
                .apply(self.arena, Value::Zero)
                .map_err(|err| CodegenError::Eval {
                    decl: self.decl_name.clone(),
                    err,
                })?;
        let base_expr = self.lower_expr(base, Some(&base_ty))?;

        let pred_id = self.alloc_id();
        let pred_name = format!("v{pred_id}");
        let k_var = self.push_binding(
            Value::Nat,
            Binding::Runtime {
                id: pred_id,
                name: pred_name.clone(),
                ty: RustType::Nat,
                is_boxed: false,
            },
        );
        let ih_ty =
            motive_cl
                .apply(self.arena, k_var.clone())
                .map_err(|err| CodegenError::Eval {
                    decl: self.decl_name.clone(),
                    err,
                })?;
        let acc_ty = match self.lower_val_ty(&ih_ty, Multiplicity::One) {
            Ok(ty) => ty,
            Err(err) => {
                self.pop_binding();
                return Err(err);
            }
        };
        let succ_ty = match motive_cl.apply(self.arena, Value::Succ(Arc::new(k_var))) {
            Ok(ty) => ty,
            Err(err) => {
                self.pop_binding();
                return Err(CodegenError::Eval {
                    decl: self.decl_name.clone(),
                    err,
                });
            }
        };

        let acc_id = self.alloc_id();
        let acc_name = format!("v{acc_id}");
        let _ = self.push_binding(
            ih_ty,
            Binding::Runtime {
                id: acc_id,
                name: acc_name.clone(),
                ty: acc_ty.clone(),
                is_boxed: false,
            },
        );
        let step_res = self.lower_expr(step, Some(&succ_ty));
        self.pop_binding();
        self.pop_binding();
        let step_expr = step_res?;

        Ok(RustExpr::NatLoop {
            scrut: Box::new(scrut_expr),
            acc_id,
            acc_name,
            acc_ty,
            pred_id,
            pred_name,
            base: Box::new(base_expr),
            step: Box::new(step_expr),
        })
    }

    fn lower_cubical(
        &mut self,
        id: TermId,
        expected: Option<&Value>,
    ) -> Result<RustExpr, CodegenError> {
        let reduced = self.eval_term(id)?;
        let depth = self.ctx.depth();
        let quoted = quote(self.arena, depth, &reduced).map_err(|err| CodegenError::Eval {
            decl: self.decl_name.clone(),
            err,
        })?;
        match self.arena.get(quoted) {
            Some(
                Term::Coe { .. }
                | Term::HCom { .. }
                | Term::PApp { .. }
                | Term::VIn { .. }
                | Term::VProj { .. }
                | Term::VType { .. }
                | Term::PLam(_)
                | Term::Path { .. }
                | Term::Interval
                | Term::DimZero
                | Term::DimOne,
            ) => Err(CodegenError::UnreducibleCubical {
                decl: self.decl_name.clone(),
            }),
            Some(Term::Ctor { id: did, ctor, .. })
                if self
                    .arena
                    .get_inductive(*did)
                    .and_then(|d| d.ctors.get(*ctor as usize))
                    .is_some_and(apollo_kernel::CtorDecl::is_path) =>
            {
                Err(CodegenError::UnreducibleCubical {
                    decl: self.decl_name.clone(),
                })
            }
            _ => self.lower_expr(quoted, expected),
        }
    }

    fn lower_pair(
        &mut self,
        first: TermId,
        second: TermId,
        expected: Option<&Value>,
    ) -> Result<RustExpr, CodegenError> {
        let Some(Value::Sigma {
            mult,
            first: fst_ty,
            second: snd_cl,
        }) = expected
        else {
            return Err(CodegenError::UnsupportedExpr {
                decl: self.decl_name.clone(),
            });
        };
        match self.sigma_shape(*mult, snd_cl)? {
            SigmaShape::ErasedFirst => {
                let fst_val = self.eval_term(first)?;
                let snd_ty =
                    snd_cl
                        .apply(self.arena, fst_val)
                        .map_err(|err| CodegenError::Eval {
                            decl: self.decl_name.clone(),
                            err,
                        })?;
                self.lower_expr(second, Some(&snd_ty))
            }
            SigmaShape::ErasedSecond => self.lower_expr(first, Some(fst_ty)),
            SigmaShape::Both => {
                let fst_expr = self.lower_expr(first, Some(fst_ty))?;
                let fst_val = self.eval_term(first)?;
                let snd_ty =
                    snd_cl
                        .apply(self.arena, fst_val)
                        .map_err(|err| CodegenError::Eval {
                            decl: self.decl_name.clone(),
                            err,
                        })?;
                let snd_expr = self.lower_expr(second, Some(&snd_ty))?;
                Ok(RustExpr::Tuple(Box::new(fst_expr), Box::new(snd_expr)))
            }
        }
    }

    fn lower_proj(&mut self, pair: TermId, is_fst: bool) -> Result<RustExpr, CodegenError> {
        let pair_ty = self.infer_val_ty(pair)?;
        let Value::Sigma {
            mult,
            second: snd_cl,
            ..
        } = pair_ty
        else {
            return Err(CodegenError::UnsupportedExpr {
                decl: self.decl_name.clone(),
            });
        };
        let shape = self.sigma_shape(mult, &snd_cl)?;
        let lowered = self.lower_expr(pair, None)?;
        match (shape, is_fst) {
            (SigmaShape::ErasedFirst, false) | (SigmaShape::ErasedSecond, true) => Ok(lowered),
            (SigmaShape::Both, true) => Ok(RustExpr::Field0(Box::new(lowered))),
            (SigmaShape::Both, false) => Ok(RustExpr::Field1(Box::new(lowered))),
            _ => Err(CodegenError::UnsupportedExpr {
                decl: self.decl_name.clone(),
            }),
        }
    }

    fn lower_lam(
        &mut self,
        id: TermId,
        expected: Option<&Value>,
    ) -> Result<RustExpr, CodegenError> {
        let mut cur_term = id;
        let mut cur_ty = expected.cloned();
        let mut params = Vec::new();
        let mut pushed = 0_usize;

        while let Some(Term::Lam { mult, body }) = self.arena.get(cur_term).cloned() {
            let Some(Value::Pi {
                domain, codomain, ..
            }) = cur_ty
            else {
                for _ in 0..pushed {
                    self.pop_binding();
                }
                return Err(CodegenError::UnsupportedExpr {
                    decl: self.decl_name.clone(),
                });
            };
            let binding = if mult.is_erased() {
                Binding::Erased
            } else {
                let dom_rty = self.lower_val_ty(&domain, mult)?;
                let local_id = self.alloc_id();
                let name = format!("v{local_id}");
                params.push((local_id, name.clone()));
                Binding::Runtime {
                    id: local_id,
                    name,
                    ty: dom_rty,
                    is_boxed: false,
                }
            };
            let var = self.push_binding((*domain).clone(), binding);
            pushed += 1;
            cur_ty = Some(
                codomain
                    .apply(self.arena, var)
                    .map_err(|err| CodegenError::Eval {
                        decl: self.decl_name.clone(),
                        err,
                    })?,
            );
            cur_term = body;
        }

        let body_res = self.lower_expr(cur_term, cur_ty.as_ref());
        for _ in 0..pushed {
            self.pop_binding();
        }
        let body = body_res?;
        if params.is_empty() {
            Ok(body)
        } else {
            Ok(RustExpr::Closure {
                params,
                body: Box::new(body),
            })
        }
    }

    fn lower_app(
        &mut self,
        id: TermId,
        expected: Option<&Value>,
    ) -> Result<RustExpr, CodegenError> {
        let mut head = id;
        let mut rev_args = Vec::new();
        while let Some(&Term::App { func, arg }) = self.arena.get(head) {
            rev_args.push(arg);
            head = func;
        }
        rev_args.reverse();

        if rev_args.len() == 1
            && let Some(let_expr) = self.try_lower_let(head, rev_args[0], expected)?
        {
            return Ok(let_expr);
        }

        if let Some(&Term::Ann {
            term: g_body,
            ty: g_ty,
        }) = self.arena.get(head)
            && let Some(sig) = self.globals.get(&(g_ty, g_body)).cloned()
            && rev_args.len() <= sig.param_keep.len()
        {
            return self.lower_global_call(&sig, head, &rev_args);
        }

        let mut head_ty = self.infer_val_ty(head)?;
        let callee = self.lower_expr(head, None)?;
        let mut kept_args = Vec::new();
        for arg in rev_args {
            let Value::Pi {
                mult,
                domain,
                codomain,
            } = head_ty
            else {
                return Err(CodegenError::UnsupportedExpr {
                    decl: self.decl_name.clone(),
                });
            };
            if !mult.is_erased() {
                kept_args.push(self.lower_expr(arg, Some(&domain))?);
            }
            let arg_val = self.eval_term(arg)?;
            head_ty = codomain
                .apply(self.arena, arg_val)
                .map_err(|err| CodegenError::Eval {
                    decl: self.decl_name.clone(),
                    err,
                })?;
        }

        if kept_args.is_empty() {
            Ok(callee)
        } else {
            Ok(RustExpr::Call {
                callee: Box::new(callee),
                args: kept_args,
            })
        }
    }

    fn try_lower_let(
        &mut self,
        head: TermId,
        val_term: TermId,
        expected: Option<&Value>,
    ) -> Result<Option<RustExpr>, CodegenError> {
        let Some(&Term::Ann {
            term: lam_id,
            ty: pi_id,
        }) = self.arena.get(head)
        else {
            return Ok(None);
        };
        if self.globals.contains_key(&(pi_id, lam_id)) {
            return Ok(None);
        }
        let Some(&Term::Lam { mult, body }) = self.arena.get(lam_id) else {
            return Ok(None);
        };
        let Some(&Term::Pi { domain, .. }) = self.arena.get(pi_id) else {
            return Ok(None);
        };

        let dom_val = self.eval_term(domain)?;
        if mult.is_erased() {
            let _ = self.push_binding(dom_val, Binding::Erased);
            let res = self.lower_expr(body, expected);
            self.pop_binding();
            return res.map(Some);
        }

        let rust_ty = self.lower_val_ty(&dom_val, mult)?;
        let value = self.lower_expr(val_term, Some(&dom_val))?;
        let local_id = self.alloc_id();
        let name = format!("v{local_id}");
        let _ = self.push_binding(
            dom_val,
            Binding::Runtime {
                id: local_id,
                name: name.clone(),
                ty: rust_ty.clone(),
                is_boxed: false,
            },
        );
        let body_res = self.lower_expr(body, expected);
        self.pop_binding();
        Ok(Some(RustExpr::Let {
            id: local_id,
            name,
            ty: rust_ty,
            value: Box::new(value),
            body: Box::new(body_res?),
        }))
    }

    fn lower_global_call(
        &mut self,
        sig: &GlobalSig,
        head: TermId,
        args: &[TermId],
    ) -> Result<RustExpr, CodegenError> {
        let mut head_ty = self.infer_val_ty(head)?;
        let mut kept_args = Vec::new();
        for (&arg, &keep) in args.iter().zip(sig.param_keep.iter()) {
            let Value::Pi {
                domain, codomain, ..
            } = head_ty
            else {
                return Err(CodegenError::UnsupportedExpr {
                    decl: self.decl_name.clone(),
                });
            };
            if keep {
                kept_args.push(self.lower_expr(arg, Some(&domain))?);
            }
            let arg_val = self.eval_term(arg)?;
            head_ty = codomain
                .apply(self.arena, arg_val)
                .map_err(|err| CodegenError::Eval {
                    decl: self.decl_name.clone(),
                    err,
                })?;
        }

        let callee = RustExpr::Global(sig.rust_name.clone());
        if args.len() < sig.param_keep.len() && kept_args.is_empty() {
            Ok(callee)
        } else {
            Ok(RustExpr::Call {
                callee: Box::new(callee),
                args: kept_args,
            })
        }
    }
}

fn lower_decl(
    arena: &mut TermArena,
    globals: &HashMap<(TermId, TermId), GlobalSig>,
    data_metas: &[LoweredDataMeta],
    decl: &CheckedDecl,
) -> Result<Option<(RustFn, GlobalSig)>, CodegenError> {
    let mut lowerer = DeclLowerer::new(arena, globals, data_metas, decl.name.clone());
    let mut cur_ty = decl.ty;
    let mut cur_body = decl.body;
    let mut type_params = Vec::new();
    let mut params = Vec::new();
    let mut param_keep = Vec::new();

    for raw_name in &decl.param_names {
        let Some(&Term::Pi {
            mult,
            domain,
            codomain,
        }) = lowerer.arena.get(cur_ty)
        else {
            return Err(CodegenError::InvalidTerm {
                decl: decl.name.clone(),
            });
        };
        let Some(&Term::Lam { body, .. }) = lowerer.arena.get(cur_body) else {
            return Err(CodegenError::InvalidTerm {
                decl: decl.name.clone(),
            });
        };

        let dom_val = lowerer.eval_term(domain)?;
        let rust_name = escape_ident(raw_name);
        if mult.is_erased() {
            param_keep.push(false);
            if matches!(dom_val, Value::Universe(_)) {
                type_params.push(rust_name.clone());
                let _ = lowerer.push_binding(dom_val, Binding::TypeParam(rust_name));
            } else {
                let _ = lowerer.push_binding(dom_val, Binding::Erased);
            }
        } else {
            param_keep.push(true);
            let rust_ty = lowerer.lower_val_ty(&dom_val, mult)?;
            let id = lowerer.alloc_id();
            params.push(RustParam {
                id,
                name: rust_name.clone(),
                ty: rust_ty.clone(),
            });
            let _ = lowerer.push_binding(
                dom_val,
                Binding::Runtime {
                    id,
                    name: rust_name,
                    ty: rust_ty,
                    is_boxed: false,
                },
            );
        }

        cur_ty = codomain;
        cur_body = body;
    }

    let ret_val = lowerer.eval_term(cur_ty)?;
    if is_erased_value_type(&ret_val) {
        return Ok(None);
    }

    let ret_ty = lowerer.lower_val_ty(&ret_val, Multiplicity::One)?;
    let body = lowerer.lower_expr(cur_body, Some(&ret_val))?;
    let rust_name = escape_ident(&decl.name);

    let mut rust_fn = RustFn {
        name: rust_name.clone(),
        type_params,
        clone_bounds: BTreeSet::new(),
        params,
        ret_ty,
        body,
    };
    rust_fn.finalize_ownership();

    let sig = GlobalSig {
        rust_name,
        param_keep,
    };
    Ok(Some((rust_fn, sig)))
}

#[cfg(test)]
mod tests {
    use super::{CodegenError, CompileError, compile_source, version};

    #[test]
    fn reports_package_version() {
        assert_eq!(version(), env!("CARGO_PKG_VERSION"));
    }

    #[test]
    fn extracts_linear_clone_and_hof_functions() {
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

            fn drop_second(0 A: Type 0, 0 B: Type 0, 1 x: A, ω y: B) -> A {
                x
            }

            fn apply(0 A: Type 0, 0 B: Type 0, 1 f: (1 _: A) -> B, 1 x: A) -> B {
                f(x)
            }

            fn twice(0 A: Type 0, ω f: (1 _: A) -> A, 1 x: A) -> A {
                f(f(x))
            }

            fn use_id(0 A: Type 0, 1 x: A) -> A {
                let 1 y: A = id(A, x);
                let 0 p: Path(_ => A, y, y) = <i> y;
                y
            }

            fn apply_id(0 A: Type 0, 1 x: A) -> A {
                apply(A, A, id(A), x)
            }

            fn const_fn(0 A: Type 0, 0 B: Type 0, 1 a: A) -> (ω _: B) -> A {
                |ω b| a
            }
        ";

        let emitted = compile_source(src);
        assert!(emitted.is_ok(), "unexpected error: {:?}", emitted.err());
        if let Ok(code) = emitted {
            let expected = "\
#![no_std]
#![forbid(unsafe_code)]

pub fn id<A>(x: A) -> A {
    x
}

pub fn dup<A: Clone>(x: A) -> (A, A) {
    (x.clone(), x)
}

pub fn swap<A: Clone, B: Clone>(p: (A, B)) -> (B, A) {
    (p.clone().1, p.0)
}

pub fn drop_second<A, B>(x: A, _y: B) -> A {
    x
}

pub fn apply<A, B>(f: impl FnOnce(A) -> B, x: A) -> B {
    f(x)
}

pub fn twice<A>(f: impl Fn(A) -> A, x: A) -> A {
    f(f(x))
}

pub fn use_id<A>(x: A) -> A {
    let v1: A = id(x);
    v1
}

pub fn apply_id<A>(x: A) -> A {
    apply(id, x)
}

pub fn const_fn<A, B>(a: A) -> impl FnOnce(B) -> A {
    move |_v1| a
}
";
            assert_eq!(code, expected);
        }
    }

    #[test]
    fn extracts_refinement_cubical_and_escaped_keywords() {
        let src = r"
            fn refine(0 A: Type 0, 1 x: A) -> Sigma(1 y: A, Path(_ => A, y, y)) {
                (x, <i> x)
            }

            fn unrefine(0 A: Type 0, 1 p: Sigma(1 y: A, Path(_ => A, y, y))) -> A {
                p.0
            }

            fn erased_first(0 A: Type 0, 0 x: A, 1 y: A) -> Sigma(0 _: Path(_ => A, x, x), A) {
                (<i> x, y)
            }

            fn project_erased_first(0 A: Type 0, 0 x: A, 1 p: Sigma(0 _: Path(_ => A, x, x), A)) -> A {
                p.1
            }

            fn coe_refl(0 A: Type 0, 1 x: A) -> A {
                coe(i => A, 0, 0, x)
            }

            fn hcom_top(0 A: Type 0, 1 x: A) -> A {
                hcom(A, 0, 1, [top => <j> x], x)
            }

            fn impl(0 A: Type 0, 1 type: A) -> A {
                type
            }

            theorem refl(0 A: Type 0, 0 x: A) -> Path(_ => A, x, x) {
                <i> x
            }

            fn erased_path_fn(0 A: Type 0, 0 x: A) -> Path(_ => A, x, x) {
                <i> x
            }
        ";

        let emitted = compile_source(src);
        assert!(emitted.is_ok(), "unexpected error: {:?}", emitted.err());
        if let Ok(code) = emitted {
            let expected = "\
#![no_std]
#![forbid(unsafe_code)]

pub fn refine<A>(x: A) -> A {
    x
}

pub fn unrefine<A>(p: A) -> A {
    p
}

pub fn erased_first<A>(y: A) -> A {
    y
}

pub fn project_erased_first<A>(p: A) -> A {
    p
}

pub fn coe_refl<A>(x: A) -> A {
    x
}

pub fn hcom_top<A>(x: A) -> A {
    x
}

pub fn r#impl<A>(r#type: A) -> A {
    r#type
}
";
            assert_eq!(code, expected);
        }
    }

    #[test]
    fn extracts_nested_lets_multi_arg_callables_and_filters_unused_generics() {
        let src = r"
            fn dup_let(0 A: Type 0, ω x: A) -> Sigma(1 _: A, A) {
                let ω y: A = (x : A);
                (y, y)
            }

            fn drop_let(0 A: Type 0, 0 B: Type 0, 1 x: A, ω z: B) -> A {
                let ω u: B = z;
                x
            }

            fn flip(
                0 A: Type 0,
                0 B: Type 0,
                0 C: Type 0,
                1 f: (1 _: A, 1 _: B) -> C,
                1 b: B,
                1 a: A,
            ) -> C {
                f(a, b)
            }

            fn mk_pair(0 A: Type 0, 0 B: Type 0) -> (1 _: A, 1 _: B) -> Sigma(1 _: A, B) {
                |1 a, 1 b| (a, b)
            }

            fn call_mk_pair(0 A: Type 0, 0 B: Type 0) -> (1 _: A, 1 _: B) -> Sigma(1 _: A, B) {
                mk_pair(A, B)
            }

            fn pair_with_closure(0 A: Type 0, 1 x: A) -> Sigma(1 _: (1 _: A) -> A, A) {
                (|1 a| a, x)
            }

            fn nested_let(0 A: Type 0, ω x: A) -> Sigma(1 _: A, A) {
                let ω y: A = x;
                (({ let 1 z: A = y; z } : A), y)
            }

            fn ignore_unused_ty(0 A: Type 0, 0 B: Type 0, 1 x: A) -> A {
                x
            }
        ";

        let emitted = compile_source(src);
        assert!(emitted.is_ok(), "unexpected error: {:?}", emitted.err());
        if let Ok(code) = emitted {
            assert!(code.contains("pub fn dup_let<A: Clone>(x: A) -> (A, A)"));
            assert!(code.contains("let v1: A = x;\n    (v1.clone(), v1)"));
            assert!(code.contains("let _v2: B = z;\n    x"));
            assert!(code.contains("f: impl FnOnce(A, B) -> C"));
            assert!(code.contains("f(a, b)"));
            assert!(code.contains("impl FnOnce(A, B) -> (A, B)"));
            assert!(code.contains("move |v0, v1| (v0, v1)"));
            assert!(code.contains(
                "pub fn call_mk_pair<A, B>() -> impl FnOnce(A, B) -> (A, B) {\n    mk_pair()\n}"
            ));
            assert!(code.contains("(move |v1| v1, x)"));
            assert!(
                code.contains("    ({\n        let v2: A = v1.clone();\n        v2\n    }, v1)")
            );
            assert!(code.contains("pub fn ignore_unused_ty<A>(x: A) -> A"));
        }
    }

    #[test]
    fn rejects_unreducible_cubical_and_reports_errors() {
        let transport = "
            fn transport(
                0 A: Type 0,
                0 B: Type 0,
                0 p: Path(_ => Type 0, A, B),
                1 x: A,
            ) -> B {
                coe(i => p @ i, 0, 1, x)
            }
        ";
        let err = compile_source(transport).err();
        assert!(matches!(
            err,
            Some(CompileError::Codegen(
                CodegenError::UnreducibleCubical { .. }
            ))
        ));
        if let Some(e) = err {
            assert!(e.to_string().contains("transport"));
        }

        let bad_elab = compile_source("fn (").err();
        assert!(matches!(bad_elab, Some(CompileError::Elab(_))));
        if let Some(e) = bad_elab {
            assert!(e.to_string().contains("parse error"));
        }

        for sample in [
            CodegenError::UnreducibleCubical {
                decl: "t".to_owned(),
            },
            CodegenError::UnsupportedType {
                decl: "t".to_owned(),
            },
            CodegenError::UnsupportedExpr {
                decl: "t".to_owned(),
            },
            CodegenError::InvalidTerm {
                decl: "t".to_owned(),
            },
        ] {
            assert_ne!(sample.to_string(), "");
        }
    }

    #[test]
    fn extracts_void_unit_and_bool_match() {
        let src = r"
            fn absurd(0 A: Type 0, 1 v: Void) -> A {
                match v {}
            }

            fn unit_id(1 u: Unit) -> Unit {
                match u {
                    () => (),
                }
            }

            fn not(1 b: Bool) -> Bool {
                match b {
                    true => false,
                    false => true,
                }
            }

            fn and(1 a: Bool, ω b: Bool) -> Bool {
                match a {
                    true => b,
                    false => false,
                }
            }

            fn choose(0 A: Type 0, 1 b: Bool, 1 x: A) -> A {
                match b {
                    true => x,
                    false => x,
                }
            }

            fn branch_dup(0 A: Type 0, 1 b: Bool, ω x: A, ω y: A) -> Sigma(1 _: A, A) {
                match b {
                    true => (x, y),
                    false => (x, x),
                }
            }

            fn after_branch(0 A: Type 0, 1 b: Bool, ω x: A, ω y: A) -> Sigma(1 _: A, A) {
                (match b as |_| A { true => x, false => y }, x)
            }

            fn dup_mixed(
                0 A: Type 0,
                ω p: Sigma(1 _: Nat, A),
            ) -> Sigma(1 _: Sigma(1 _: Nat, A), Sigma(1 _: Nat, A)) {
                (p, p)
            }

            theorem not_not(0 b: Bool) -> Path(_ => Bool, not(not(b)), b) {
                match b as |x| Path(_ => Bool, not(not(x)), x) {
                    true => <i> true,
                    false => <i> false,
                }
            }
        ";

        let emitted = compile_source(src);
        assert!(emitted.is_ok(), "unexpected error: {:?}", emitted.err());
        if let Ok(code) = emitted {
            assert!(!code.contains("not_not"));
            assert!(code.contains(
                "pub fn absurd<A>(v: core::convert::Infallible) -> A {\n    match v {}\n}"
            ));
            assert!(code.contains("pub fn unit_id(u: ()) -> () {\n    match u { () => () }\n}"));
            assert!(
                code.contains("pub fn not(b: bool) -> bool {\n    if b { false } else { true }\n}")
            );
            assert!(code.contains(
                "pub fn and(a: bool, b: bool) -> bool {\n    if a { b } else { false }\n}"
            ));
            assert!(
                code.contains(
                    "pub fn choose<A>(b: bool, x: A) -> A {\n    if b { x } else { x }\n}"
                )
            );
            assert!(code.contains(
                "pub fn branch_dup<A: Clone>(b: bool, x: A, y: A) -> (A, A) {\n    if b { (x.clone(), y) } else { (x.clone(), x) }\n}"
            ));
            assert!(code.contains(
                "pub fn after_branch<A: Clone>(b: bool, x: A, y: A) -> (A, A) {\n    (if b { x.clone() } else { y }, x)\n}"
            ));
            assert!(code.contains(
                "pub fn dup_mixed<A: Clone>(p: (u128, A)) -> ((u128, A), (u128, A)) {\n    (p.clone(), p)\n}"
            ));
        }
    }

    #[test]
    fn extracts_nat_loops_and_cloning() {
        let src = r"
            fn two() -> Nat {
                succ(succ(zero))
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
                    succ(_, acc) => succ(acc),
                }
            }

            fn add_two(1 n: Nat) -> Nat {
                add(two, n)
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
                    succ(_, acc) => add(m, acc),
                }
            }

            fn repeat(0 A: Type 0, 1 n: Nat, ω x: A) -> A {
                match n {
                    zero => x,
                    succ(_, _) => x,
                }
            }

            fn flip_n(0 A: Type 0, 1 n: Nat, 1 p: Sigma(1 _: A, A)) -> Sigma(1 _: A, A) {
                match n {
                    zero => p,
                    succ(_, acc) => (acc.1, acc.0),
                }
            }

            fn iter_n(0 A: Type 0, 1 n: Nat, 1 x: A, ω f: (1 _: A) -> A) -> A {
                match n {
                    zero => x,
                    succ(_, acc) => f(acc),
                }
            }

            fn double_n(1 n: Nat, 1 m: Nat) -> Nat {
                match n {
                    zero => m,
                    succ(_, acc) => add(acc, acc),
                }
            }

            fn step_let(1 n: Nat, 1 m: Nat) -> Nat {
                match n {
                    zero => m,
                    succ(_, acc) => {
                        let 1 tmp: Nat = succ(acc);
                        tmp
                    },
                }
            }
        ";

        let emitted = compile_source(src);
        assert!(emitted.is_ok(), "unexpected error: {:?}", emitted.err());
        if let Ok(code) = emitted {
            assert!(!code.contains("add_zero_right"));
            assert!(code.contains("pub fn two() -> u128 {\n    2_u128\n}"));
            assert!(code.contains("pub fn add_two(n: u128) -> u128 {\n    add(two(), n)\n}"));
            assert!(code.contains("pub fn pred(n: u128) -> u128 {\n    let mut v2: u128 = 0_u128;\n    for v1 in 0..n {\n        v2 = v1;\n    }\n    v2\n}"));
            assert!(code.contains("pub fn add(n: u128, m: u128) -> u128 {\n    let mut v3: u128 = m;\n    for _v2 in 0..n {\n        v3 = v3 + 1;\n    }\n    v3\n}"));
            assert!(code.contains("pub fn mul(n: u128, m: u128) -> u128 {\n    let mut v3: u128 = 0_u128;\n    for _v2 in 0..n {\n        v3 = add(m, v3);\n    }\n    v3\n}"));
            assert!(code.contains("pub fn repeat<A: Clone>(n: u128, x: A) -> A {\n    let mut v3: A = x.clone();\n    for _v2 in 0..n {\n        v3 = x.clone();\n    }\n    v3\n}"));
            assert!(code.contains("pub fn flip_n<A: Clone>(n: u128, p: (A, A)) -> (A, A) {\n    let mut v3: (A, A) = p;\n    for _v2 in 0..n {\n        v3 = (v3.clone().1, v3.0);\n    }\n    v3\n}"));
            assert!(code.contains("pub fn iter_n<A>(n: u128, x: A, f: impl Fn(A) -> A) -> A {\n    let mut v4: A = x;\n    for _v3 in 0..n {\n        v4 = f(v4);\n    }\n    v4\n}"));
            assert!(code.contains("pub fn double_n(n: u128, m: u128) -> u128 {\n    let mut v3: u128 = m;\n    for _v2 in 0..n {\n        v3 = add(v3, v3);\n    }\n    v3\n}"));
            assert!(code.contains("pub fn step_let(n: u128, m: u128) -> u128 {\n    let mut v3: u128 = m;\n    for _v2 in 0..n {\n        v3 = {\n            let v4: u128 = v3 + 1;\n            v4\n        };\n    }\n    v3\n}"));
        }
    }

    #[test]
    fn extracts_non_recursive_adts_without_alloc_and_erases_proof_fields() {
        let src = r"
            enum Empty {}
            enum Option(0 A: Type 0) {
                None,
                Some(1 val: A),
            }
            struct Point(0 A: Type 0) {
                1 x: A,
                1 y: A,
            }
            struct VerifiedNat {
                1 val: Nat,
                0 ok: Path(_ => Nat, val, val),
            }

            fn absurd_e(0 A: Type 0, 1 e: Empty) -> A {
                match e {}
            }

            fn unwrap_or(0 A: Type 0, 1 o: Option(A), ω d: A) -> A {
                match o {
                    Option::None => d,
                    Option::Some(v) => v,
                }
            }

            fn swap_pt(0 A: Type 0, 1 p: Point(A)) -> Point(A) {
                match p {
                    Point { x, y } => Point { x: y, y: x },
                }
            }

            fn mk_verified(1 n: Nat) -> VerifiedNat {
                VerifiedNat { val: n, ok: <i> n }
            }
        ";
        let emitted = compile_source(src);
        assert!(emitted.is_ok(), "unexpected error: {:?}", emitted.err());
        if let Ok(code) = emitted {
            assert!(!code.contains("extern crate alloc"));
            assert!(code.contains("pub enum Empty {\n}"));
            assert!(code.contains("pub enum Option<A> {\n    None,\n    Some(A),\n}"));
            assert!(code.contains("pub struct Point<A> {\n    pub x: A,\n    pub y: A,\n}"));
            assert!(code.contains("pub struct VerifiedNat {\n    pub val: u128,\n}"));
            assert!(!code.contains("ok:"));
            assert!(code.contains("VerifiedNat { val: n }"));
        }
    }

    #[test]
    fn extracts_recursive_list_and_tree_with_alloc_box_and_helpers() {
        let src = r"
            fn add(1 n: Nat, 1 m: Nat) -> Nat {
                match n { zero => m, succ(_, acc) => succ(acc) }
            }
            enum List(0 A: Type 0) {
                Nil,
                Cons(ω head: A, 1 tail: List(A)),
            }
            enum Tree(0 A: Type 0) {
                Leaf,
                Node(1 left: Tree(A), ω val: A, 1 right: Tree(A)),
            }
            fn tail_or_nil(0 A: Type 0, 1 xs: List(A)) -> List(A) {
                match xs {
                    List::Nil => List::Nil,
                    List::Cons(_, t) => t,
                }
            }
            fn append(0 A: Type 0, 1 xs: List(A), ω ys: List(A)) -> List(A) {
                match xs {
                    List::Nil => ys,
                    List::Cons(h, _, ih) => List::Cons(h, ih),
                }
            }
            fn list_map(0 A: Type 0, 0 B: Type 0, 1 xs: List(A), ω f: (1 _: A) -> B) -> List(B) {
                match xs {
                    List::Nil => List::Nil,
                    List::Cons(h, _, ih) => List::Cons(f(h), ih),
                }
            }
            fn list_fill(0 A: Type 0, 1 xs: List(A), ω v: A) -> List(A) {
                match xs {
                    List::Nil => List::Nil,
                    List::Cons(_, _, ih) => List::Cons(v, ih),
                }
            }
            fn tree_sum(1 t: Tree(Nat)) -> Nat {
                match t {
                    Tree::Leaf => zero,
                    Tree::Node(_, v, _, ihl, ihr) => add(v, add(ihl, ihr)),
                }
            }
        ";
        let emitted = compile_source(src);
        assert!(emitted.is_ok(), "unexpected error: {:?}", emitted.err());
        if let Ok(code) = emitted {
            assert!(code.contains("extern crate alloc;\nuse alloc::boxed::Box;"));
            assert!(code.contains("Cons(A, Box<List<A>>)"));
            assert!(code.contains("Node(Box<Tree<A>>, A, Box<Tree<A>>)"));
            assert!(
                code.contains("pub fn tail_or_nil<A>(xs: List<A>) -> List<A> {\n    match xs {")
            );
            assert!(code.contains("pub fn append<A>(xs: List<A>, ys: List<A>) -> List<A>"));
            assert!(code.contains("f: &impl Fn(A) -> B"));
            assert!(code.contains("pub fn list_fill<A: Clone>(xs: List<A>, v: A) -> List<A>"));
            assert!(code.contains("pub fn tree_sum(t: Tree<u128>) -> u128"));
            assert!(code.contains("v.clone()"));
            assert!(code.contains(
                "pub fn tail_or_nil<A>(xs: List<A>) -> List<A> {\n    match xs {\n        List::Nil => List::Nil,\n        List::Cons(_v1, v2) => (*v2),\n    }\n}"
            ));
            assert!(code.contains(
                "pub fn append<A>(xs: List<A>, ys: List<A>) -> List<A> {\n    fn __apollo_rec_0<A>(scrut: List<A>, ys: List<A>) -> List<A> {\n        match scrut {\n            List::Nil => ys,\n            List::Cons(v2, v3) => {\n                let v4: List<A> = __apollo_rec_0(*v3, ys);\n                List::Cons(v2, Box::new(v4))\n            },\n        }\n    }\n    __apollo_rec_0(xs, ys)\n}"
            ));
        }
    }

    #[test]
    fn extracts_data_erasure_multi_params_and_cloning() {
        let src = r"
            fn add(1 n: Nat, 1 m: Nat) -> Nat {
                match n { zero => m, succ(_, acc) => succ(acc) }
            }
            struct Bi(0 A: Type 0, 0 B: Type 0) { 1 fst: A, 1 snd: B }
            struct Tagged(0 n: Nat) { 1 val: Nat }
            enum GhostEnum { Mk(0 ghost: Nat, 1 v: Nat) }
            struct GhostStruct { 0 ghost: Nat, 1 v: Nat }
            enum OptMany(0 A: Type 0) { None, Some(ω val: A) }
            enum PairE(0 A: Type 0) { Both(1 a: A, 1 b: A) }
            struct Pt(0 A: Type 0) { 1 x: A, 1 y: A }
            struct Box1(0 A: Type 0) { 1 val: A }
            enum FnBox(0 A: Type 0) { Mk(ω f: (1 _: A) -> A) }

            fn mk_bi(0 A: Type 0, 0 B: Type 0, 1 a: A, 1 b: B) -> Bi(A, B) {
                Bi { fst: a, snd: b }
            }
            fn mk_tagged() -> Tagged(zero) { Tagged(zero) { val: zero } }
            fn dup_enum(0 A: Type 0, ω x: A) -> PairE(A) { PairE::Both(x, x) }
            fn dup_struct(0 A: Type 0, ω x: A) -> Pt(A) { Pt { x: x, y: x } }
            fn let_in_enum(0 A: Type 0, ω x: A) -> OptMany(Sigma(1 _: A, A)) {
                OptMany::Some({ let ω y: A = x; (y, y) })
            }
            fn let_in_struct(0 A: Type 0, ω x: A) -> Box1(Sigma(1 _: A, A)) {
                Box1 { val: { let ω y: A = x; (y, y) } }
            }
            fn dup_in_match(0 A: Type 0, 1 o: OptMany(A), ω d: A) -> Pt(A) {
                match o {
                    OptMany::None => { let ω z: A = d; Pt { x: z, y: z } },
                    OptMany::Some(v) => Pt { x: v, y: v },
                }
            }
            fn dup_nat_pat(1 o: OptMany(Nat)) -> Nat {
                match o {
                    OptMany::None => zero,
                    OptMany::Some(n) => add(n, n),
                }
            }
            fn dup_fn_pat(0 A: Type 0, 1 fb: FnBox(A), 1 x: A) -> A {
                match fb { FnBox::Mk(f) => f(f(x)) }
            }
        ";
        let emitted = compile_source(src);
        assert!(emitted.is_ok(), "unexpected error: {:?}", emitted.err());
        if let Ok(code) = emitted {
            assert!(code.contains("pub struct Bi<A, B>"));
            assert!(code.contains("-> Bi<A, B>"));
            assert!(code.contains("pub struct Tagged {\n    pub val: u128,\n}"));
            assert!(code.contains("pub fn mk_tagged() -> Tagged"));
            assert!(code.contains("pub enum GhostEnum {\n    Mk(u128),\n}"));
            assert!(code.contains("pub struct GhostStruct {\n    pub v: u128,\n}"));
            assert!(code.contains("PairE::Both(x.clone(), x)"));
            assert!(code.contains("Pt { x: x.clone(), y: x }"));
            assert!(code.contains("pub fn let_in_enum<A: Clone>(x: A)"));
            assert!(code.contains("(v1.clone(), v1)"));
            assert!(code.contains("pub fn let_in_struct<A: Clone>(x: A)"));
            assert!(code.contains(
                "        OptMany::None => {\n            let v2: A = d;\n            Pt { x: v2.clone(), y: v2 }\n        },\n        OptMany::Some(v3) => Pt { x: v3.clone(), y: v3 },"
            ));
            assert!(code.contains("OptMany::Some(v1) => add(v1, v1),"));
            assert!(code.contains("FnBox::Mk(v2) => v2(v2(x)),"));
        }
    }

    #[test]
    fn extracts_recursive_helpers_multi_rec_and_ih_cloning() {
        let src = r"
            fn add(1 n: Nat, 1 m: Nat) -> Nat {
                match n { zero => m, succ(_, acc) => succ(acc) }
            }
            enum List(0 A: Type 0) {
                Nil,
                Cons(ω head: A, ω tail: List(A)),
            }
            enum Tree(0 A: Type 0) {
                Leaf,
                Node(1 left: Tree(A), ω val: A, ω right: Tree(A)),
            }
            fn append(0 A: Type 0, 1 xs: List(A), ω ys: List(A)) -> List(A) {
                match xs {
                    List::Nil => ys,
                    List::Cons(h, _, ih) => List::Cons(h, ih),
                }
            }
            fn nil_let_rec(1 xs: List(Nat)) -> Nat {
                match xs {
                    List::Nil => { let 1 z: Nat = zero; z },
                    List::Cons(h, _, ih) => add(h, ih),
                }
            }
            fn two_recs(1 a: List(Nat), 1 b: List(Nat)) -> Nat {
                add(
                    match a { List::Nil => zero, List::Cons(h, _, ih) => add(h, ih) },
                    match b { List::Nil => zero, List::Cons(h, _, ih) => add(h, ih) },
                )
            }
            fn after_rec(1 xs: List(Nat), 1 y: Nat) -> Nat {
                let 1 r: Nat = match xs {
                    List::Nil => zero,
                    List::Cons(h, _, ih) => add(h, ih),
                };
                add(r, y)
            }
            fn tree_leaves(0 A: Type 0, 1 t: Tree(A), ω d: A) -> List(A) {
                match t {
                    Tree::Leaf => List::Cons(d, List::Nil),
                    Tree::Node(_, _, _, ihl, ihr) => append(A, ihl, ihr),
                }
            }
            fn dup_byval_cap(0 A: Type 0, 1 xs: List(A), ω ys: List(A)) -> List(A) {
                let 1 r: List(A) = match xs {
                    List::Nil => ys,
                    List::Cons(h, _, ih) => List::Cons(h, ih),
                };
                append(A, r, ys)
            }
            fn dup_ih_list(0 A: Type 0, 1 xs: List(A)) -> List(A) {
                match xs {
                    List::Nil => List::Nil,
                    List::Cons(_, _, ih) => append(A, ih, ih),
                }
            }
            fn dup_ih_nat(1 xs: List(Nat)) -> Nat {
                match xs {
                    List::Nil => zero,
                    List::Cons(_, _, ih) => add(ih, ih),
                }
            }
        ";
        let emitted = compile_source(src);
        assert!(emitted.is_ok(), "unexpected error: {:?}", emitted.err());
        if let Ok(code) = emitted {
            assert!(code.contains(
                "            List::Nil => {\n                let v1: u128 = 0_u128;\n                v1\n            },"
            ));
            assert!(code.contains("fn __apollo_rec_0(scrut: List<u128>)"));
            assert!(code.contains("fn __apollo_rec_1(scrut: List<u128>)"));
            assert!(code.contains("add(v5, y)"));
            assert!(code.contains("d: &A"));
            assert!(code.contains("d.clone()"));
            assert!(code.contains("__apollo_rec_0(xs, ys.clone())"));
            assert!(code.contains("append(v3.clone(), v3)"));
            assert!(code.contains("add(v3, v3)"));
        }
    }

    #[test]
    fn extracts_computational_univalence_to_zero_overhead_rust() {
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
            fn flip_via_ua(1 b: Bool) -> Bool {
                coe(i => bool_flip @ i, 0, 1, b)
            }
            fn flip_back_via_ua(1 b: Bool) -> Bool {
                coe(i => bool_flip @ i, 1, 0, b)
            }
            fn flip_via_vproj(1 b: Bool) -> Bool {
                vproj(0, Bool, Bool, not_equiv, b)
            }
            fn keep_via_vin(1 b: Bool) -> Bool {
                vin(0, b, false)
            }
        ";
        let emitted = compile_source(src);
        assert!(emitted.is_ok(), "unexpected error: {:?}", emitted.err());
        if let Ok(code) = emitted {
            assert!(!code.contains("bool_flip"));
            assert!(!code.contains("not_equiv"));
            assert!(code.contains(
                "pub fn flip_via_ua(b: bool) -> bool {\n    if b { false } else { true }\n}"
            ));
            assert!(code.contains(
                "pub fn flip_back_via_ua(b: bool) -> bool {\n    if b { false } else { true }\n}"
            ));
            assert!(code.contains(
                "pub fn flip_via_vproj(b: bool) -> bool {\n    if b { false } else { true }\n}"
            ));
            assert!(code.contains("pub fn keep_via_vin(b: bool) -> bool {\n    b\n}"));
        }
    }

    #[test]
    fn extracts_hit_quotients_without_alloc_and_rejects_open_path_ctor() {
        let src = r"
            enum S1 {
                Base,
                Loop(<i>) = S1::Base .. S1::Base,
            }
            enum Trunc(0 A: Type 0) {
                In(1 x: A),
                Squash(1 x: Trunc(A), 1 y: Trunc(A), <i>) = x .. y,
            }
            fn add(1 a: Nat, 1 b: Nat) -> Nat {
                match a { zero => b, succ(k, ih) => succ(ih) }
            }
            theorem add_zr(0 n: Nat) -> Path(_ => Nat, add(n, zero), n) {
                match n as |k| Path(_ => Nat, add(k, zero), k) {
                    zero => <i> zero,
                    succ(k, ih) => <i> succ(ih @ i),
                }
            }
            theorem add_sr(0 a: Nat, 0 b: Nat) -> Path(_ => Nat, add(a, succ(b)), succ(add(a, b))) {
                match a as |k| Path(_ => Nat, add(k, succ(b)), succ(add(k, b))) {
                    zero => <i> succ(b),
                    succ(k, ih) => <i> succ(ih @ i),
                }
            }
            theorem sym(0 A: Type 0, 0 x: A, 0 y: A, 0 p: Path(_ => A, x, y)) -> Path(_ => A, y, x) {
                <i> hcom(A, 0, 1, [i = 0 => <j> p @ j, i = 1 => <j> x], x)
            }
            theorem trans(0 A: Type 0, 0 x: A, 0 y: A, 0 z: A, 0 p: Path(_ => A, x, y), 0 q: Path(_ => A, y, z)) -> Path(_ => A, x, z) {
                <i> hcom(A, 0, 1, [i = 0 => <j> x, i = 1 => <j> q @ j], p @ i)
            }
            theorem add_comm(0 a: Nat, 0 b: Nat) -> Path(_ => Nat, add(a, b), add(b, a)) {
                match a as |k| Path(_ => Nat, add(k, b), add(b, k)) {
                    zero => sym(Nat, add(b, zero), b, add_zr(b)),
                    succ(k, ih) => trans(Nat, succ(add(k, b)), succ(add(b, k)), add(b, succ(k)), <i> succ(ih @ i), sym(Nat, add(b, succ(k)), succ(add(b, k)), add_sr(b, k))),
                }
            }
            enum UPair(0 A: Type 0) {
                Pair(1 a: A, 1 b: A),
                Swap(1 a: A, 1 b: A, <i>) = UPair::Pair(a, b) .. UPair::Pair(b, a),
            }
            fn sum_upair(1 p: UPair(Nat)) -> Nat {
                match p {
                    UPair::Pair(a, b) => add(a, b),
                    UPair::Swap(a, b, i) => add_comm(a, b) @ i,
                }
            }
            fn swapped_pair(1 a: Nat, 1 b: Nat) -> UPair(Nat) {
                UPair::Swap(a, b, 1)
            }
        ";
        let emitted = compile_source(src);
        assert!(emitted.is_ok(), "unexpected error: {:?}", emitted.err());
        if let Ok(code) = emitted {
            assert!(!code.contains("extern crate alloc"));
            assert!(!code.contains("Loop"));
            assert!(!code.contains("Squash"));
            assert!(!code.contains("Swap"));
            assert!(code.contains("pub enum S1 {\n    Base,\n}"));
            assert!(code.contains("pub enum Trunc<A> {\n    In(A),\n}"));
            assert!(code.contains("pub enum UPair<A> {\n    Pair(A, A),\n}"));
            assert!(code.contains("UPair::Pair(b, a)"));
        }

        // Open-dim path constructor in a runtime body must fail with UnreducibleCubical.
        let mut checked = apollo_elab::check_source(
            "enum S1 { Base, Loop(<i>) = S1::Base .. S1::Base }\nfn ok(0 _x: Bool) -> S1 { S1::Base }",
        );
        if let Ok(ref mut module) = checked {
            let s1_id = module.data_decls[0].id;
            let open_dim = module.arena.var(apollo_kernel::Index(0));
            let open_loop = module.arena.ctor(s1_id, 1, Vec::new(), vec![open_dim]);
            module.decls[0].body = module
                .arena
                .lam(apollo_kernel::Multiplicity::Zero, open_loop);
            let res = super::emit_module(module);
            assert!(matches!(res, Err(CodegenError::UnreducibleCubical { .. })));
        }
    }
}
