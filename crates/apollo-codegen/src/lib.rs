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
    let mut globals = HashMap::new();
    let mut functions = Vec::new();

    for decl in &module.decls {
        if decl.kind == DeclKind::Theorem {
            continue;
        }
        if let Some((rust_fn, sig)) = lower_decl(&mut arena, &globals, decl)? {
            let _ = globals.insert((decl.ty, decl.body), sig);
            functions.push(rust_fn);
        }
    }

    Ok(RustModule { functions }.render())
}

pub fn compile_source(source: &str) -> Result<String, CompileError> {
    let checked = check_source(source)?;
    let rust_code = emit_module(&checked)?;
    Ok(rust_code)
}

#[derive(Debug, Clone)]
struct GlobalSig {
    rust_name: String,
    param_keep: Vec<bool>,
}

#[derive(Debug, Clone)]
enum Binding {
    TypeParam(String),
    Erased,
    Runtime { id: usize, name: String },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SigmaShape {
    ErasedFirst,
    ErasedSecond,
    Both,
}

const fn is_erased_value_type(val: &Value) -> bool {
    matches!(
        val,
        Value::Path { .. } | Value::Universe(_) | Value::Interval
    )
}

struct DeclLowerer<'a> {
    arena: &'a mut TermArena,
    globals: &'a HashMap<(TermId, TermId), GlobalSig>,
    decl_name: String,
    ctx: Ctx,
    env: Vec<Value>,
    bindings: Vec<Binding>,
    next_local_id: usize,
}

impl<'a> DeclLowerer<'a> {
    fn new(
        arena: &'a mut TermArena,
        globals: &'a HashMap<(TermId, TermId), GlobalSig>,
        decl_name: String,
    ) -> Self {
        Self {
            arena,
            globals,
            decl_name,
            ctx: Ctx::new(),
            env: Vec::new(),
            bindings: Vec::new(),
            next_local_id: 0,
        }
    }

    const fn alloc_id(&mut self) -> usize {
        let id = self.next_local_id;
        self.next_local_id += 1;
        id
    }

    fn push_binding(&mut self, ty_val: Value, binding: Binding) -> Value {
        let var = self.ctx.push(ty_val);
        self.env.push(var.clone());
        self.bindings.push(binding);
        var
    }

    fn pop_binding(&mut self) {
        self.ctx.pop();
        let _ = self.env.pop();
        let _ = self.bindings.pop();
    }

    fn eval_term(&self, id: TermId) -> Result<Value, CodegenError> {
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

    fn lower_val_ty(
        &mut self,
        val: &Value,
        fn_mult: Multiplicity,
    ) -> Result<RustType, CodegenError> {
        match val {
            Value::Unit => Ok(RustType::Unit),
            Value::Void => Ok(RustType::Void),
            Value::Bool => Ok(RustType::Bool),
            Value::Nat => Ok(RustType::Nat),
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

    fn lower_expr(
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
                    Some(Binding::Runtime { id, name }) => Ok(RustExpr::Local {
                        id: *id,
                        name: name.clone(),
                    }),
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
            Term::Coe { .. } | Term::HCom { .. } | Term::PApp { .. } => {
                self.lower_cubical(id, expected)
            }
            Term::PLam(_) | Term::Path { .. } | Term::Interval | Term::DimZero | Term::DimOne => {
                Err(CodegenError::UnreducibleCubical {
                    decl: self.decl_name.clone(),
                })
            }
            Term::Tt
            | Term::UnitElim { .. }
            | Term::VoidElim { .. }
            | Term::True
            | Term::False
            | Term::BoolElim { .. }
            | Term::Zero
            | Term::Succ(_)
            | Term::NatElim { .. } => self.lower_inductive(&term),
            Term::Universe(_)
            | Term::Pi { .. }
            | Term::Sigma { .. }
            | Term::Unit
            | Term::Void
            | Term::Bool
            | Term::Nat => Err(CodegenError::UnsupportedExpr {
                decl: self.decl_name.clone(),
            }),
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
                | Term::PLam(_)
                | Term::Path { .. }
                | Term::Interval
                | Term::DimZero
                | Term::DimOne,
            ) => Err(CodegenError::UnreducibleCubical {
                decl: self.decl_name.clone(),
            }),
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
                let local_id = self.alloc_id();
                let name = format!("v{local_id}");
                params.push((local_id, name.clone()));
                Binding::Runtime { id: local_id, name }
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
    decl: &CheckedDecl,
) -> Result<Option<(RustFn, GlobalSig)>, CodegenError> {
    let mut lowerer = DeclLowerer::new(arena, globals, decl.name.clone());
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
                ty: rust_ty,
            });
            let _ = lowerer.push_binding(
                dom_val,
                Binding::Runtime {
                    id,
                    name: rust_name,
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

            fn struct(0 A: Type 0, 1 type: A) -> A {
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

pub fn r#struct<A>(r#type: A) -> A {
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
        }
    }
}
