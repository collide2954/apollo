use std::fmt;
use std::sync::Arc;

use crate::cubical::{Cof, Dim, DimVar};
use crate::inductive::InductiveId;
use crate::level::Level;
use crate::multiplicity::Multiplicity;
use crate::term::{CofTerm, DeBruijnLevel, Index, Term, TermArena, TermId};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EvalError {
    InvalidTermId(TermId),
    UnboundIndex { index: Index, env_len: usize },
    InvalidLevel { level: DeBruijnLevel, depth: u32 },
}

impl fmt::Display for EvalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidTermId(id) => write!(f, "invalid term id {}", id.raw()),
            Self::UnboundIndex { index, env_len } => {
                write!(
                    f,
                    "unbound variable {index} in environment of length {env_len}"
                )
            }
            Self::InvalidLevel { level, depth } => {
                write!(f, "invalid level {level} at depth {depth}")
            }
        }
    }
}

impl std::error::Error for EvalError {}

pub type Env = Vec<Value>;

#[derive(Debug, Clone)]
pub enum TypeLine {
    Closure(Closure),
    PiDom(Box<Self>),
    PiCod {
        line: Box<Self>,
        dst: Dim,
        arg: Arc<Value>,
    },
    SigmaFirst(Box<Self>),
    SigmaSecond {
        line: Box<Self>,
        src: Dim,
        first_at_src: Arc<Value>,
    },
}

impl TypeLine {
    pub fn apply(&self, arena: &TermArena, dim: Dim) -> Result<Value, EvalError> {
        match self {
            Self::Closure(closure) => closure.apply(arena, Value::Dim(dim)),
            Self::PiDom(line) => match line.apply(arena, dim)? {
                Value::Pi { domain, .. } => Ok((*domain).clone()),
                other => Ok(other),
            },
            Self::PiCod { line, dst, arg } => match line.apply(arena, dim)? {
                Value::Pi { codomain, .. } => {
                    let dom_line = Self::PiDom(line.clone());
                    let arg_at_dim = coe_line(arena, &dom_line, *dst, dim, (**arg).clone())?;
                    codomain.apply(arena, arg_at_dim)
                }
                other => Ok(other),
            },
            Self::SigmaFirst(line) => match line.apply(arena, dim)? {
                Value::Sigma { first, .. } => Ok((*first).clone()),
                other => Ok(other),
            },
            Self::SigmaSecond {
                line,
                src,
                first_at_src,
            } => match line.apply(arena, dim)? {
                Value::Sigma { second, .. } => {
                    let fst_line = Self::SigmaFirst(line.clone());
                    let fst_at_dim =
                        coe_line(arena, &fst_line, *src, dim, (**first_at_src).clone())?;
                    second.apply(arena, fst_at_dim)
                }
                other => Ok(other),
            },
        }
    }
}

#[derive(Debug, Clone)]
pub enum Closure {
    Term {
        env: Env,
        body: TermId,
    },
    CoePi {
        line: Box<TypeLine>,
        src: Dim,
        dst: Dim,
        func: Arc<Value>,
    },
    HComPi {
        codomain: Box<Self>,
        src: Dim,
        dst: Dim,
        branches: Vec<(Cof, Self)>,
        cap: Arc<Value>,
    },
    AppArg {
        tube: Box<Self>,
        arg: Arc<Value>,
    },
}

impl Closure {
    #[must_use]
    pub const fn new(env: Env, body: TermId) -> Self {
        Self::Term { env, body }
    }

    pub fn apply(&self, arena: &TermArena, arg: Value) -> Result<Value, EvalError> {
        match self {
            Self::Term { env, body } => {
                let mut next_env = env.clone();
                next_env.push(arg);
                eval(arena, &next_env, *body)
            }
            Self::CoePi {
                line,
                src,
                dst,
                func,
            } => {
                let dom_line = TypeLine::PiDom(line.clone());
                let arg_at_src = coe_line(arena, &dom_line, *dst, *src, arg.clone())?;
                let applied = apply(arena, func, arg_at_src)?;
                let cod_line = TypeLine::PiCod {
                    line: line.clone(),
                    dst: *dst,
                    arg: Arc::new(arg),
                };
                coe_line(arena, &cod_line, *src, *dst, applied)
            }
            Self::HComPi {
                codomain,
                src,
                dst,
                branches,
                cap,
            } => {
                let res_ty = codomain.apply(arena, arg.clone())?;
                let arg_arc = Arc::new(arg.clone());
                let app_branches = branches
                    .iter()
                    .map(|(cof, tube)| {
                        (
                            cof.clone(),
                            Self::AppArg {
                                tube: Box::new(tube.clone()),
                                arg: Arc::clone(&arg_arc),
                            },
                        )
                    })
                    .collect();
                let app_cap = apply(arena, cap, arg)?;
                hcom_val(arena, &res_ty, *src, *dst, app_branches, app_cap)
            }
            Self::AppArg { tube, arg: fixed } => {
                let func_val = tube.apply(arena, arg)?;
                apply(arena, &func_val, (**fixed).clone())
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct DoubleClosure {
    env: Env,
    body: TermId,
}

impl DoubleClosure {
    #[must_use]
    pub const fn new(env: Env, body: TermId) -> Self {
        Self { env, body }
    }

    pub fn apply2(
        &self,
        arena: &TermArena,
        first: Value,
        second: Value,
    ) -> Result<Value, EvalError> {
        let mut next = self.env.clone();
        next.push(first);
        next.push(second);
        eval(arena, &next, self.body)
    }
}

#[derive(Debug, Clone)]
pub struct MultiClosure {
    env: Env,
    body: TermId,
}

impl MultiClosure {
    #[must_use]
    pub const fn new(env: Env, body: TermId) -> Self {
        Self { env, body }
    }

    pub fn apply_many(&self, arena: &TermArena, args: &[Value]) -> Result<Value, EvalError> {
        let mut next = self.env.clone();
        next.extend(args.iter().cloned());
        eval(arena, &next, self.body)
    }
}

#[derive(Debug, Clone)]
pub enum Neutral {
    Var(DeBruijnLevel),
    App {
        func: Arc<Self>,
        arg: Value,
    },
    Fst(Arc<Self>),
    Snd(Arc<Self>),
    PApp {
        path: Arc<Self>,
        left: Arc<Value>,
        right: Arc<Value>,
        dim: Dim,
    },
    Coe {
        line: Box<TypeLine>,
        src: Dim,
        dst: Dim,
        term: Arc<Value>,
    },
    HCom {
        ty: Arc<Value>,
        src: Dim,
        dst: Dim,
        branches: Vec<(Cof, Closure)>,
        cap: Arc<Value>,
    },
    UnitElim {
        motive: Closure,
        on_unit: Arc<Value>,
        scrut: Arc<Self>,
    },
    VoidElim {
        motive: Closure,
        scrut: Arc<Self>,
    },
    BoolElim {
        motive: Closure,
        on_true: Arc<Value>,
        on_false: Arc<Value>,
        scrut: Arc<Self>,
    },
    NatElim {
        motive: Closure,
        base: Arc<Value>,
        step: DoubleClosure,
        scrut: Arc<Self>,
    },
    DataElim {
        id: InductiveId,
        params: Vec<Value>,
        motive: Closure,
        branches: Vec<MultiClosure>,
        scrut: Arc<Self>,
    },
}

#[derive(Debug, Clone)]
pub enum Value {
    Universe(Level),
    Pi {
        mult: Multiplicity,
        domain: Arc<Self>,
        codomain: Closure,
    },
    Lam {
        mult: Multiplicity,
        body: Closure,
    },
    Sigma {
        mult: Multiplicity,
        first: Arc<Self>,
        second: Closure,
    },
    Pair {
        first: Arc<Self>,
        second: Arc<Self>,
    },
    Interval,
    Dim(Dim),
    Path {
        family: Closure,
        left: Arc<Self>,
        right: Arc<Self>,
    },
    PLam(Closure),
    Unit,
    Tt,
    Void,
    Bool,
    True,
    False,
    Nat,
    Zero,
    Succ(Arc<Self>),
    Data {
        id: InductiveId,
        params: Vec<Self>,
    },
    Ctor {
        id: InductiveId,
        ctor: u32,
        params: Vec<Self>,
        args: Vec<Self>,
    },
    Neutral(Arc<Neutral>),
}

impl Value {
    #[must_use]
    pub fn var(level: DeBruijnLevel) -> Self {
        Self::Neutral(Arc::new(Neutral::Var(level)))
    }

    #[must_use]
    pub const fn dim_var(level: u32) -> Self {
        Self::Dim(Dim::Var(DimVar(level)))
    }
}

pub fn eval(arena: &TermArena, env: &[Value], id: TermId) -> Result<Value, EvalError> {
    let term = arena.get(id).ok_or(EvalError::InvalidTermId(id))?;
    match term {
        Term::Universe(level) => Ok(Value::Universe(level.clone())),
        Term::Var(index) => {
            let idx = index.0 as usize;
            if idx >= env.len() {
                return Err(EvalError::UnboundIndex {
                    index: *index,
                    env_len: env.len(),
                });
            }
            Ok(env[env.len() - 1 - idx].clone())
        }
        Term::Pi {
            mult,
            domain,
            codomain,
        } => {
            let dom_val = eval(arena, env, *domain)?;
            Ok(Value::Pi {
                mult: *mult,
                domain: Arc::new(dom_val),
                codomain: Closure::new(env.to_vec(), *codomain),
            })
        }
        Term::Lam { mult, body } => Ok(Value::Lam {
            mult: *mult,
            body: Closure::new(env.to_vec(), *body),
        }),
        Term::App { func, arg } => {
            let func_val = eval(arena, env, *func)?;
            let arg_val = eval(arena, env, *arg)?;
            apply(arena, &func_val, arg_val)
        }
        Term::Sigma {
            mult,
            first,
            second,
        } => {
            let first_val = eval(arena, env, *first)?;
            Ok(Value::Sigma {
                mult: *mult,
                first: Arc::new(first_val),
                second: Closure::new(env.to_vec(), *second),
            })
        }
        Term::Pair { first, second } => {
            let first_val = eval(arena, env, *first)?;
            let second_val = eval(arena, env, *second)?;
            Ok(Value::Pair {
                first: Arc::new(first_val),
                second: Arc::new(second_val),
            })
        }
        Term::Fst(pair) => {
            let pair_val = eval(arena, env, *pair)?;
            Ok(proj_fst(&pair_val))
        }
        Term::Snd(pair) => {
            let pair_val = eval(arena, env, *pair)?;
            Ok(proj_snd(&pair_val))
        }
        Term::Ann { term, .. } => eval(arena, env, *term),
        Term::Interval => Ok(Value::Interval),
        Term::DimZero => Ok(Value::Dim(Dim::Zero)),
        Term::DimOne => Ok(Value::Dim(Dim::One)),
        Term::PLam(body) => Ok(Value::PLam(Closure::new(env.to_vec(), *body))),
        Term::PApp {
            path,
            left,
            right,
            dim,
        } => eval_papp(arena, env, *path, *left, *right, *dim),
        Term::Coe {
            line,
            src,
            dst,
            term,
        } => eval_coe(arena, env, *line, *src, *dst, *term),
        Term::HCom {
            ty,
            src,
            dst,
            branches,
            cap,
        } => eval_hcom(arena, env, *ty, *src, *dst, branches, *cap),
        other => eval_inductive(arena, env, id, other),
    }
}

fn eval_inductive(
    arena: &TermArena,
    env: &[Value],
    id: TermId,
    term: &Term,
) -> Result<Value, EvalError> {
    match term {
        Term::Path {
            family,
            left,
            right,
        } => {
            let left_val = eval(arena, env, *left)?;
            let right_val = eval(arena, env, *right)?;
            Ok(Value::Path {
                family: Closure::new(env.to_vec(), *family),
                left: Arc::new(left_val),
                right: Arc::new(right_val),
            })
        }
        Term::Unit => Ok(Value::Unit),
        Term::Tt => Ok(Value::Tt),
        Term::UnitElim {
            motive,
            on_unit,
            scrut,
        } => {
            let scrut_val = eval(arena, env, *scrut)?;
            let on_unit_val = eval(arena, env, *on_unit)?;
            match scrut_val {
                Value::Neutral(neutral) => Ok(Value::Neutral(Arc::new(Neutral::UnitElim {
                    motive: Closure::new(env.to_vec(), *motive),
                    on_unit: Arc::new(on_unit_val),
                    scrut: neutral,
                }))),
                _ => Ok(on_unit_val),
            }
        }
        Term::Void => Ok(Value::Void),
        Term::VoidElim { motive, scrut } => {
            let scrut_val = eval(arena, env, *scrut)?;
            match scrut_val {
                Value::Neutral(neutral) => Ok(Value::Neutral(Arc::new(Neutral::VoidElim {
                    motive: Closure::new(env.to_vec(), *motive),
                    scrut: neutral,
                }))),
                other => Ok(other),
            }
        }
        Term::Bool => Ok(Value::Bool),
        Term::True => Ok(Value::True),
        Term::False => Ok(Value::False),
        Term::BoolElim {
            motive,
            on_true,
            on_false,
            scrut,
        } => {
            let scrut_val = eval(arena, env, *scrut)?;
            match scrut_val {
                Value::True => eval(arena, env, *on_true),
                Value::False => eval(arena, env, *on_false),
                Value::Neutral(neutral) => {
                    let true_val = eval(arena, env, *on_true)?;
                    let false_val = eval(arena, env, *on_false)?;
                    Ok(Value::Neutral(Arc::new(Neutral::BoolElim {
                        motive: Closure::new(env.to_vec(), *motive),
                        on_true: Arc::new(true_val),
                        on_false: Arc::new(false_val),
                        scrut: neutral,
                    })))
                }
                other => Ok(other),
            }
        }
        Term::Nat => Ok(Value::Nat),
        Term::Zero => Ok(Value::Zero),
        Term::Succ(pred) => Ok(Value::Succ(Arc::new(eval(arena, env, *pred)?))),
        Term::NatElim {
            motive,
            base,
            step,
            scrut,
        } => {
            let scrut_val = eval(arena, env, *scrut)?;
            let base_val = eval(arena, env, *base)?;
            let motive_cl = Closure::new(env.to_vec(), *motive);
            let step_cl = DoubleClosure::new(env.to_vec(), *step);
            eval_nat_elim(arena, &motive_cl, &base_val, &step_cl, scrut_val)
        }
        Term::Data { .. } | Term::Ctor { .. } | Term::DataElim { .. } => {
            eval_data_term(arena, env, id, term)
        }
        _ => Err(EvalError::InvalidTermId(id)),
    }
}

fn eval_data_term(
    arena: &TermArena,
    env: &[Value],
    id: TermId,
    term: &Term,
) -> Result<Value, EvalError> {
    match term {
        Term::Data { id: did, params } => {
            let mut param_vals = Vec::with_capacity(params.len());
            for &p in params {
                param_vals.push(eval(arena, env, p)?);
            }
            Ok(Value::Data {
                id: *did,
                params: param_vals,
            })
        }
        Term::Ctor {
            id: did,
            ctor,
            params,
            args,
        } => {
            let mut param_vals = Vec::with_capacity(params.len());
            for &p in params {
                param_vals.push(eval(arena, env, p)?);
            }
            let mut arg_vals = Vec::with_capacity(args.len());
            for &a in args {
                arg_vals.push(eval(arena, env, a)?);
            }
            Ok(Value::Ctor {
                id: *did,
                ctor: *ctor,
                params: param_vals,
                args: arg_vals,
            })
        }
        Term::DataElim {
            id: did,
            params,
            motive,
            branches,
            scrut,
        } => {
            let mut param_vals = Vec::with_capacity(params.len());
            for &p in params {
                param_vals.push(eval(arena, env, p)?);
            }
            let motive_cl = Closure::new(env.to_vec(), *motive);
            let branch_cls: Vec<MultiClosure> = branches
                .iter()
                .map(|&b| MultiClosure::new(env.to_vec(), b))
                .collect();
            let scrut_val = eval(arena, env, *scrut)?;
            eval_data_elim(arena, *did, &param_vals, &motive_cl, &branch_cls, scrut_val)
        }
        _ => Err(EvalError::InvalidTermId(id)),
    }
}

fn eval_data_elim(
    arena: &TermArena,
    id: InductiveId,
    params: &[Value],
    motive: &Closure,
    branches: &[MultiClosure],
    scrut: Value,
) -> Result<Value, EvalError> {
    match scrut {
        Value::Ctor {
            id: c_id,
            ctor,
            args,
            ..
        } if c_id == id => {
            let Some(decl) = arena.get_inductive(id) else {
                return Ok(Value::Ctor {
                    id: c_id,
                    ctor,
                    params: params.to_vec(),
                    args,
                });
            };
            let Some(ctor_decl) = decl.ctors.get(ctor as usize) else {
                return Ok(Value::Ctor {
                    id: c_id,
                    ctor,
                    params: params.to_vec(),
                    args,
                });
            };
            let Some(branch) = branches.get(ctor as usize) else {
                return Ok(Value::Ctor {
                    id: c_id,
                    ctor,
                    params: params.to_vec(),
                    args,
                });
            };
            let mut full_args = Vec::with_capacity(ctor_decl.branch_arity());
            full_args.extend(args.iter().cloned());
            for (arg, field) in args.iter().zip(&ctor_decl.fields) {
                if field.is_recursive {
                    let ih = eval_data_elim(arena, id, params, motive, branches, arg.clone())?;
                    full_args.push(ih);
                }
            }
            branch.apply_many(arena, &full_args)
        }
        Value::Neutral(neutral) => Ok(Value::Neutral(Arc::new(Neutral::DataElim {
            id,
            params: params.to_vec(),
            motive: motive.clone(),
            branches: branches.to_vec(),
            scrut: neutral,
        }))),
        other => Ok(other),
    }
}

fn eval_nat_elim(
    arena: &TermArena,
    motive: &Closure,
    base: &Value,
    step: &DoubleClosure,
    scrut: Value,
) -> Result<Value, EvalError> {
    match scrut {
        Value::Zero => Ok(base.clone()),
        Value::Succ(pred) => {
            let ih = eval_nat_elim(arena, motive, base, step, (*pred).clone())?;
            step.apply2(arena, (*pred).clone(), ih)
        }
        Value::Neutral(neutral) => Ok(Value::Neutral(Arc::new(Neutral::NatElim {
            motive: motive.clone(),
            base: Arc::new(base.clone()),
            step: step.clone(),
            scrut: neutral,
        }))),
        other => Ok(other),
    }
}

pub fn eval_cof(arena: &TermArena, env: &[Value], cof: &CofTerm) -> Result<Cof, EvalError> {
    match cof {
        CofTerm::Top => Ok(Cof::Top),
        CofTerm::Bot => Ok(Cof::Bot),
        CofTerm::Eq(lhs, rhs) => {
            let lval = eval(arena, env, *lhs)?;
            let rval = eval(arena, env, *rhs)?;
            match (lval, rval) {
                (Value::Dim(d1), Value::Dim(d2)) => Ok(Cof::eq(d1, d2)),
                _ => Ok(Cof::Bot),
            }
        }
        CofTerm::And(lhs, rhs) => Ok(Cof::and(
            eval_cof(arena, env, lhs)?,
            eval_cof(arena, env, rhs)?,
        )),
        CofTerm::Or(lhs, rhs) => Ok(Cof::or(
            eval_cof(arena, env, lhs)?,
            eval_cof(arena, env, rhs)?,
        )),
    }
}

fn eval_hcom(
    arena: &TermArena,
    env: &[Value],
    ty: TermId,
    src: TermId,
    dst: TermId,
    branches: &[(CofTerm, TermId)],
    cap: TermId,
) -> Result<Value, EvalError> {
    let ty_val = eval(arena, env, ty)?;
    let src_val = eval(arena, env, src)?;
    let dst_val = eval(arena, env, dst)?;
    let cap_val = eval(arena, env, cap)?;
    let mut eval_branches = Vec::with_capacity(branches.len());
    for (cof_term, tube) in branches {
        let cof = eval_cof(arena, env, cof_term)?;
        eval_branches.push((cof, Closure::new(env.to_vec(), *tube)));
    }
    match (src_val, dst_val) {
        (Value::Dim(s), Value::Dim(d)) => hcom_val(arena, &ty_val, s, d, eval_branches, cap_val),
        _ => Ok(cap_val),
    }
}

pub fn hcom_val(
    arena: &TermArena,
    ty: &Value,
    src: Dim,
    dst: Dim,
    branches: Vec<(Cof, Closure)>,
    cap: Value,
) -> Result<Value, EvalError> {
    if src == dst {
        return Ok(cap);
    }
    let mut active_branches = Vec::new();
    for (cof, tube) in branches {
        if cof == Cof::Top {
            return tube.apply(arena, Value::Dim(dst));
        }
        if cof.is_consistent() {
            active_branches.push((cof, tube));
        }
    }
    match ty {
        Value::Unit => Ok(Value::Tt),
        Value::Pi { mult, codomain, .. } => Ok(Value::Lam {
            mult: *mult,
            body: Closure::HComPi {
                codomain: Box::new(codomain.clone()),
                src,
                dst,
                branches: active_branches,
                cap: Arc::new(cap),
            },
        }),
        _ => Ok(Value::Neutral(Arc::new(Neutral::HCom {
            ty: Arc::new(ty.clone()),
            src,
            dst,
            branches: active_branches,
            cap: Arc::new(cap),
        }))),
    }
}

fn eval_papp(
    arena: &TermArena,
    env: &[Value],
    path: TermId,
    left: TermId,
    right: TermId,
    dim: TermId,
) -> Result<Value, EvalError> {
    let dim_val = eval(arena, env, dim)?;
    let left_val = eval(arena, env, left)?;
    let right_val = eval(arena, env, right)?;
    let path_val = eval(arena, env, path)?;
    papp(arena, &path_val, &left_val, &right_val, &dim_val)
}

fn eval_coe(
    arena: &TermArena,
    env: &[Value],
    line: TermId,
    src: TermId,
    dst: TermId,
    term: TermId,
) -> Result<Value, EvalError> {
    let src_val = eval(arena, env, src)?;
    let dst_val = eval(arena, env, dst)?;
    let term_val = eval(arena, env, term)?;
    let type_line = TypeLine::Closure(Closure::new(env.to_vec(), line));
    match (src_val, dst_val) {
        (Value::Dim(s), Value::Dim(d)) => coe_line(arena, &type_line, s, d, term_val),
        _ => Ok(term_val),
    }
}

pub fn coe_line(
    arena: &TermArena,
    line: &TypeLine,
    src: Dim,
    dst: Dim,
    term: Value,
) -> Result<Value, EvalError> {
    if src == dst {
        return Ok(term);
    }
    let probe = Dim::Var(DimVar(u32::MAX));
    match line.apply(arena, probe)? {
        Value::Universe(_) | Value::Unit | Value::Void | Value::Bool | Value::Nat => Ok(term),
        Value::Data { params, .. } if params.is_empty() => Ok(term),
        Value::Pi { mult, .. } => Ok(Value::Lam {
            mult,
            body: Closure::CoePi {
                line: Box::new(line.clone()),
                src,
                dst,
                func: Arc::new(term),
            },
        }),
        Value::Sigma { .. } => {
            let p0 = proj_fst(&term);
            let p1 = proj_snd(&term);
            let fst_line = TypeLine::SigmaFirst(Box::new(line.clone()));
            let c0 = coe_line(arena, &fst_line, src, dst, p0.clone())?;
            let snd_line = TypeLine::SigmaSecond {
                line: Box::new(line.clone()),
                src,
                first_at_src: Arc::new(p0),
            };
            let c1 = coe_line(arena, &snd_line, src, dst, p1)?;
            Ok(Value::Pair {
                first: Arc::new(c0),
                second: Arc::new(c1),
            })
        }
        _ => Ok(Value::Neutral(Arc::new(Neutral::Coe {
            line: Box::new(line.clone()),
            src,
            dst,
            term: Arc::new(term),
        }))),
    }
}

pub fn papp(
    arena: &TermArena,
    path: &Value,
    left: &Value,
    right: &Value,
    dim: &Value,
) -> Result<Value, EvalError> {
    match dim {
        Value::Dim(Dim::Zero) => Ok(left.clone()),
        Value::Dim(Dim::One) => Ok(right.clone()),
        Value::Dim(dim_val) => match path {
            Value::PLam(body) => body.apply(arena, Value::Dim(*dim_val)),
            Value::Neutral(neutral) => Ok(Value::Neutral(Arc::new(Neutral::PApp {
                path: Arc::clone(neutral),
                left: Arc::new(left.clone()),
                right: Arc::new(right.clone()),
                dim: *dim_val,
            }))),
            other => Ok(other.clone()),
        },
        _ => Ok(path.clone()),
    }
}

pub fn apply(arena: &TermArena, func: &Value, arg: Value) -> Result<Value, EvalError> {
    match func {
        Value::Lam { body, .. } => body.apply(arena, arg),
        Value::Neutral(neutral) => Ok(Value::Neutral(Arc::new(Neutral::App {
            func: Arc::clone(neutral),
            arg,
        }))),
        other => Ok(other.clone()),
    }
}

#[must_use]
pub fn proj_fst(value: &Value) -> Value {
    match value {
        Value::Pair { first, .. } => (**first).clone(),
        Value::Neutral(neutral) => Value::Neutral(Arc::new(Neutral::Fst(Arc::clone(neutral)))),
        other => other.clone(),
    }
}

#[must_use]
pub fn proj_snd(value: &Value) -> Value {
    match value {
        Value::Pair { second, .. } => (**second).clone(),
        Value::Neutral(neutral) => Value::Neutral(Arc::new(Neutral::Snd(Arc::clone(neutral)))),
        other => other.clone(),
    }
}

pub fn quote(arena: &mut TermArena, depth: u32, value: &Value) -> Result<TermId, EvalError> {
    match value {
        Value::Universe(level) => Ok(arena.universe(level.clone())),
        Value::Pi {
            mult,
            domain,
            codomain,
        } => {
            let dom_id = quote(arena, depth, domain)?;
            let var = Value::var(DeBruijnLevel(depth));
            let cod_val = codomain.apply(arena, var)?;
            let cod_id = quote(arena, depth + 1, &cod_val)?;
            Ok(arena.pi(*mult, dom_id, cod_id))
        }
        Value::Lam { mult, body } => {
            let var = Value::var(DeBruijnLevel(depth));
            let body_val = body.apply(arena, var)?;
            let body_id = quote(arena, depth + 1, &body_val)?;
            Ok(arena.lam(*mult, body_id))
        }
        Value::Sigma {
            mult,
            first,
            second,
        } => {
            let first_id = quote(arena, depth, first)?;
            let var = Value::var(DeBruijnLevel(depth));
            let second_val = second.apply(arena, var)?;
            let second_id = quote(arena, depth + 1, &second_val)?;
            Ok(arena.sigma(*mult, first_id, second_id))
        }
        Value::Pair { first, second } => {
            let first_id = quote(arena, depth, first)?;
            let second_id = quote(arena, depth, second)?;
            Ok(arena.pair(first_id, second_id))
        }
        Value::Interval => Ok(arena.interval()),
        Value::Dim(Dim::Zero) => Ok(arena.dim_zero()),
        Value::Dim(Dim::One) => Ok(arena.dim_one()),
        Value::Dim(Dim::Var(DimVar(lvl))) => {
            let level = DeBruijnLevel(*lvl);
            let index = level
                .to_index(depth)
                .ok_or(EvalError::InvalidLevel { level, depth })?;
            Ok(arena.var(index))
        }
        Value::Path {
            family,
            left,
            right,
        } => {
            let fam_val = family.apply(arena, Value::dim_var(depth))?;
            let fam_id = quote(arena, depth + 1, &fam_val)?;
            let left_id = quote(arena, depth, left)?;
            let right_id = quote(arena, depth, right)?;
            Ok(arena.path(fam_id, left_id, right_id))
        }
        Value::PLam(body) => {
            let body_val = body.apply(arena, Value::dim_var(depth))?;
            let body_id = quote(arena, depth + 1, &body_val)?;
            Ok(arena.plam(body_id))
        }
        Value::Unit => Ok(arena.unit()),
        Value::Tt => Ok(arena.tt()),
        Value::Void => Ok(arena.void()),
        Value::Bool => Ok(arena.bool_ty()),
        Value::True => Ok(arena.bool_true()),
        Value::False => Ok(arena.bool_false()),
        Value::Nat => Ok(arena.nat()),
        Value::Zero => Ok(arena.zero()),
        Value::Succ(pred) => {
            let pred_id = quote(arena, depth, pred)?;
            Ok(arena.succ(pred_id))
        }
        Value::Data { id, params } => {
            let mut param_ids = Vec::with_capacity(params.len());
            for p in params {
                param_ids.push(quote(arena, depth, p)?);
            }
            Ok(arena.data(*id, param_ids))
        }
        Value::Ctor {
            id,
            ctor,
            params,
            args,
        } => {
            let mut param_ids = Vec::with_capacity(params.len());
            for p in params {
                param_ids.push(quote(arena, depth, p)?);
            }
            let mut arg_ids = Vec::with_capacity(args.len());
            for a in args {
                arg_ids.push(quote(arena, depth, a)?);
            }
            Ok(arena.ctor(*id, *ctor, param_ids, arg_ids))
        }
        Value::Neutral(neutral) => quote_neutral(arena, depth, neutral),
    }
}

fn quote_neutral(
    arena: &mut TermArena,
    depth: u32,
    neutral: &Neutral,
) -> Result<TermId, EvalError> {
    match neutral {
        Neutral::Var(level) => {
            let index = level.to_index(depth).ok_or(EvalError::InvalidLevel {
                level: *level,
                depth,
            })?;
            Ok(arena.var(index))
        }
        Neutral::App { func, arg } => {
            let func_id = quote_neutral(arena, depth, func)?;
            let arg_id = quote(arena, depth, arg)?;
            Ok(arena.app(func_id, arg_id))
        }
        Neutral::Fst(pair) => {
            let pair_id = quote_neutral(arena, depth, pair)?;
            Ok(arena.fst(pair_id))
        }
        Neutral::Snd(pair) => {
            let pair_id = quote_neutral(arena, depth, pair)?;
            Ok(arena.snd(pair_id))
        }
        Neutral::PApp {
            path,
            left,
            right,
            dim,
        } => {
            let path_id = quote_neutral(arena, depth, path)?;
            let left_id = quote(arena, depth, left)?;
            let right_id = quote(arena, depth, right)?;
            let dim_id = quote(arena, depth, &Value::Dim(*dim))?;
            Ok(arena.papp(path_id, left_id, right_id, dim_id))
        }
        Neutral::Coe {
            line,
            src,
            dst,
            term,
        } => {
            let line_val = line.apply(arena, Dim::Var(DimVar(depth)))?;
            let line_id = quote(arena, depth + 1, &line_val)?;
            let src_id = quote(arena, depth, &Value::Dim(*src))?;
            let dst_id = quote(arena, depth, &Value::Dim(*dst))?;
            let term_id = quote(arena, depth, term)?;
            Ok(arena.coe(line_id, src_id, dst_id, term_id))
        }
        Neutral::HCom {
            ty,
            src,
            dst,
            branches,
            cap,
        } => {
            let ty_id = quote(arena, depth, ty)?;
            let src_id = quote(arena, depth, &Value::Dim(*src))?;
            let dst_id = quote(arena, depth, &Value::Dim(*dst))?;
            let mut quoted_branches = Vec::with_capacity(branches.len());
            for (cof, tube) in branches {
                let cof_term = quote_cof(arena, depth, cof)?;
                let tube_val = tube.apply(arena, Value::dim_var(depth))?;
                let tube_id = quote(arena, depth + 1, &tube_val)?;
                quoted_branches.push((cof_term, tube_id));
            }
            let cap_id = quote(arena, depth, cap)?;
            Ok(arena.hcom(ty_id, src_id, dst_id, quoted_branches, cap_id))
        }
        other => quote_neutral_inductive(arena, depth, other),
    }
}

fn quote_neutral_inductive(
    arena: &mut TermArena,
    depth: u32,
    neutral: &Neutral,
) -> Result<TermId, EvalError> {
    match neutral {
        Neutral::UnitElim {
            motive,
            on_unit,
            scrut,
        } => {
            let m_val = motive.apply(arena, Value::var(DeBruijnLevel(depth)))?;
            let m_id = quote(arena, depth + 1, &m_val)?;
            let on_unit_id = quote(arena, depth, on_unit)?;
            let scrut_id = quote_neutral(arena, depth, scrut)?;
            Ok(arena.unit_elim(m_id, on_unit_id, scrut_id))
        }
        Neutral::VoidElim { motive, scrut } => {
            let m_val = motive.apply(arena, Value::var(DeBruijnLevel(depth)))?;
            let m_id = quote(arena, depth + 1, &m_val)?;
            let scrut_id = quote_neutral(arena, depth, scrut)?;
            Ok(arena.void_elim(m_id, scrut_id))
        }
        Neutral::BoolElim {
            motive,
            on_true,
            on_false,
            scrut,
        } => {
            let m_val = motive.apply(arena, Value::var(DeBruijnLevel(depth)))?;
            let m_id = quote(arena, depth + 1, &m_val)?;
            let true_id = quote(arena, depth, on_true)?;
            let false_id = quote(arena, depth, on_false)?;
            let scrut_id = quote_neutral(arena, depth, scrut)?;
            Ok(arena.bool_elim(m_id, true_id, false_id, scrut_id))
        }
        Neutral::NatElim {
            motive,
            base,
            step,
            scrut,
        } => {
            let m_val = motive.apply(arena, Value::var(DeBruijnLevel(depth)))?;
            let m_id = quote(arena, depth + 1, &m_val)?;
            let base_id = quote(arena, depth, base)?;
            let k_var = Value::var(DeBruijnLevel(depth));
            let ih_var = Value::var(DeBruijnLevel(depth + 1));
            let step_val = step.apply2(arena, k_var, ih_var)?;
            let step_id = quote(arena, depth + 2, &step_val)?;
            let scrut_id = quote_neutral(arena, depth, scrut)?;
            Ok(arena.nat_elim(m_id, base_id, step_id, scrut_id))
        }
        Neutral::DataElim {
            id,
            params,
            motive,
            branches,
            scrut,
        } => quote_data_elim(arena, depth, *id, params, motive, branches, scrut),
        _ => Ok(arena.tt()),
    }
}

fn quote_data_elim(
    arena: &mut TermArena,
    depth: u32,
    id: InductiveId,
    params: &[Value],
    motive: &Closure,
    branches: &[MultiClosure],
    scrut: &Neutral,
) -> Result<TermId, EvalError> {
    let mut param_ids = Vec::with_capacity(params.len());
    for p in params {
        param_ids.push(quote(arena, depth, p)?);
    }
    let m_val = motive.apply(arena, Value::var(DeBruijnLevel(depth)))?;
    let m_id = quote(arena, depth + 1, &m_val)?;
    let arities: Vec<u32> = arena.get_inductive(id).map_or_else(Vec::new, |decl| {
        decl.ctors
            .iter()
            .map(|c| u32::try_from(c.branch_arity()).unwrap_or(0))
            .collect()
    });
    let mut branch_ids = Vec::with_capacity(branches.len());
    for (branch, arity) in branches.iter().zip(arities) {
        let mut vars = Vec::with_capacity(arity as usize);
        for offset in 0..arity {
            vars.push(Value::var(DeBruijnLevel(depth + offset)));
        }
        let b_val = branch.apply_many(arena, &vars)?;
        branch_ids.push(quote(arena, depth + arity, &b_val)?);
    }
    let scrut_id = quote_neutral(arena, depth, scrut)?;
    Ok(arena.data_elim(id, param_ids, m_id, branch_ids, scrut_id))
}

fn quote_cof(arena: &mut TermArena, depth: u32, cof: &Cof) -> Result<CofTerm, EvalError> {
    match cof {
        Cof::Top => Ok(CofTerm::Top),
        Cof::Bot => Ok(CofTerm::Bot),
        Cof::Eq(lhs, rhs) => {
            let l_id = quote(arena, depth, &Value::Dim(*lhs))?;
            let r_id = quote(arena, depth, &Value::Dim(*rhs))?;
            Ok(CofTerm::Eq(l_id, r_id))
        }
        Cof::And(lhs, rhs) => Ok(CofTerm::And(
            Box::new(quote_cof(arena, depth, lhs)?),
            Box::new(quote_cof(arena, depth, rhs)?),
        )),
        Cof::Or(lhs, rhs) => Ok(CofTerm::Or(
            Box::new(quote_cof(arena, depth, lhs)?),
            Box::new(quote_cof(arena, depth, rhs)?),
        )),
    }
}

fn conv_closures(
    arena: &TermArena,
    depth: u32,
    arg: Value,
    lhs: &Closure,
    rhs: &Closure,
) -> Result<bool, EvalError> {
    let v1 = lhs.apply(arena, arg.clone())?;
    let v2 = rhs.apply(arena, arg)?;
    conv(arena, depth + 1, &v1, &v2)
}

pub fn conv(arena: &TermArena, depth: u32, lhs: &Value, rhs: &Value) -> Result<bool, EvalError> {
    match (lhs, rhs) {
        (Value::Universe(l1), Value::Universe(l2)) => Ok(l1 == l2),
        (
            Value::Pi {
                mult: m1,
                domain: d1,
                codomain: c1,
            },
            Value::Pi {
                mult: m2,
                domain: d2,
                codomain: c2,
            },
        ) => {
            if m1 != m2 || !conv(arena, depth, d1, d2)? {
                return Ok(false);
            }
            conv_closures(arena, depth, Value::var(DeBruijnLevel(depth)), c1, c2)
        }
        (Value::Lam { mult: m1, body: b1 }, Value::Lam { mult: m2, body: b2 }) => {
            if m1 != m2 {
                return Ok(false);
            }
            conv_closures(arena, depth, Value::var(DeBruijnLevel(depth)), b1, b2)
        }
        (Value::Lam { body, .. }, other @ Value::Neutral(_))
        | (other @ Value::Neutral(_), Value::Lam { body, .. }) => {
            let var = Value::var(DeBruijnLevel(depth));
            let v_lam = body.apply(arena, var.clone())?;
            let v_other = apply(arena, other, var)?;
            conv(arena, depth + 1, &v_lam, &v_other)
        }
        (
            Value::Sigma {
                mult: m1,
                first: f1,
                second: s1,
            },
            Value::Sigma {
                mult: m2,
                first: f2,
                second: s2,
            },
        ) => {
            if m1 != m2 || !conv(arena, depth, f1, f2)? {
                return Ok(false);
            }
            conv_closures(arena, depth, Value::var(DeBruijnLevel(depth)), s1, s2)
        }
        (
            Value::Pair {
                first: f1,
                second: s1,
            },
            Value::Pair {
                first: f2,
                second: s2,
            },
        ) => Ok(conv(arena, depth, f1, f2)? && conv(arena, depth, s1, s2)?),
        (Value::Pair { first, second }, other @ Value::Neutral(_))
        | (other @ Value::Neutral(_), Value::Pair { first, second }) => {
            Ok(conv(arena, depth, first, &proj_fst(other))?
                && conv(arena, depth, second, &proj_snd(other))?)
        }
        (Value::Interval, Value::Interval)
        | (Value::Unit, Value::Unit)
        | (Value::Tt, Value::Tt)
        | (Value::Void, Value::Void)
        | (Value::Bool, Value::Bool)
        | (Value::True, Value::True)
        | (Value::False, Value::False)
        | (Value::Nat, Value::Nat)
        | (Value::Zero, Value::Zero) => Ok(true),
        (Value::Dim(d1), Value::Dim(d2)) => Ok(d1 == d2),
        (
            Value::Path {
                family: f1,
                left: l1,
                right: r1,
            },
            Value::Path {
                family: f2,
                left: l2,
                right: r2,
            },
        ) => {
            if !conv(arena, depth, l1, l2)? || !conv(arena, depth, r1, r2)? {
                return Ok(false);
            }
            conv_closures(arena, depth, Value::dim_var(depth), f1, f2)
        }
        (Value::PLam(b1), Value::PLam(b2)) => {
            conv_closures(arena, depth, Value::dim_var(depth), b1, b2)
        }
        (Value::Succ(p1), Value::Succ(p2)) => conv(arena, depth, p1, p2),
        (Value::Neutral(n1), Value::Neutral(n2)) => conv_neutral(arena, depth, n1, n2),
        (l @ (Value::Data { .. } | Value::Ctor { .. }), r) => conv_data_value(arena, depth, l, r),
        _ => Ok(false),
    }
}

fn conv_data_value(
    arena: &TermArena,
    depth: u32,
    lhs: &Value,
    rhs: &Value,
) -> Result<bool, EvalError> {
    match (lhs, rhs) {
        (Value::Data { id: i1, params: p1 }, Value::Data { id: i2, params: p2 }) => {
            Ok(i1 == i2 && conv_slice(arena, depth, p1, p2)?)
        }
        (
            Value::Ctor {
                id: i1,
                ctor: c1,
                params: p1,
                args: a1,
            },
            Value::Ctor {
                id: i2,
                ctor: c2,
                params: p2,
                args: a2,
            },
        ) => Ok(i1 == i2
            && c1 == c2
            && conv_slice(arena, depth, p1, p2)?
            && conv_slice(arena, depth, a1, a2)?),
        _ => Ok(false),
    }
}

fn conv_slice(
    arena: &TermArena,
    depth: u32,
    lhs: &[Value],
    rhs: &[Value],
) -> Result<bool, EvalError> {
    if lhs.len() != rhs.len() {
        return Ok(false);
    }
    for (l, r) in lhs.iter().zip(rhs) {
        if !conv(arena, depth, l, r)? {
            return Ok(false);
        }
    }
    Ok(true)
}

fn conv_neutral(
    arena: &TermArena,
    depth: u32,
    lhs: &Neutral,
    rhs: &Neutral,
) -> Result<bool, EvalError> {
    match (lhs, rhs) {
        (Neutral::Var(l1), Neutral::Var(l2)) => Ok(l1 == l2),
        (Neutral::App { func: f1, arg: a1 }, Neutral::App { func: f2, arg: a2 }) => {
            Ok(conv_neutral(arena, depth, f1, f2)? && conv(arena, depth, a1, a2)?)
        }
        (Neutral::Fst(p1), Neutral::Fst(p2)) | (Neutral::Snd(p1), Neutral::Snd(p2)) => {
            conv_neutral(arena, depth, p1, p2)
        }
        (
            Neutral::PApp {
                path: p1, dim: d1, ..
            },
            Neutral::PApp {
                path: p2, dim: d2, ..
            },
        ) => Ok(d1 == d2 && conv_neutral(arena, depth, p1, p2)?),
        (
            Neutral::Coe {
                line: l1,
                src: s1,
                dst: d1,
                term: t1,
            },
            Neutral::Coe {
                line: l2,
                src: s2,
                dst: d2,
                term: t2,
            },
        ) => {
            if s1 != s2 || d1 != d2 || !conv(arena, depth, t1, t2)? {
                return Ok(false);
            }
            let dim = Dim::Var(DimVar(depth));
            let v1 = l1.apply(arena, dim)?;
            let v2 = l2.apply(arena, dim)?;
            conv(arena, depth + 1, &v1, &v2)
        }
        (
            Neutral::HCom {
                ty: ty1,
                src: s1,
                dst: d1,
                branches: b1,
                cap: c1,
            },
            Neutral::HCom {
                ty: ty2,
                src: s2,
                dst: d2,
                branches: b2,
                cap: c2,
            },
        ) => {
            if s1 != s2
                || d1 != d2
                || b1.len() != b2.len()
                || !conv(arena, depth, ty1, ty2)?
                || !conv(arena, depth, c1, c2)?
            {
                return Ok(false);
            }
            for ((cof1, tube1), (cof2, tube2)) in b1.iter().zip(b2) {
                if !cof1.equivalent(cof2)
                    || !conv_closures(arena, depth, Value::dim_var(depth), tube1, tube2)?
                {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        other => conv_neutral_inductive(arena, depth, other.0, other.1),
    }
}

fn conv_neutral_inductive(
    arena: &TermArena,
    depth: u32,
    lhs: &Neutral,
    rhs: &Neutral,
) -> Result<bool, EvalError> {
    match (lhs, rhs) {
        (
            Neutral::UnitElim {
                motive: m1,
                on_unit: u1,
                scrut: s1,
            },
            Neutral::UnitElim {
                motive: m2,
                on_unit: u2,
                scrut: s2,
            },
        ) => Ok(conv_neutral(arena, depth, s1, s2)?
            && conv(arena, depth, u1, u2)?
            && conv_closures(arena, depth, Value::var(DeBruijnLevel(depth)), m1, m2)?),
        (
            Neutral::VoidElim {
                motive: m1,
                scrut: s1,
            },
            Neutral::VoidElim {
                motive: m2,
                scrut: s2,
            },
        ) => Ok(conv_neutral(arena, depth, s1, s2)?
            && conv_closures(arena, depth, Value::var(DeBruijnLevel(depth)), m1, m2)?),
        (
            Neutral::BoolElim {
                motive: m1,
                on_true: t1,
                on_false: f1,
                scrut: s1,
            },
            Neutral::BoolElim {
                motive: m2,
                on_true: t2,
                on_false: f2,
                scrut: s2,
            },
        ) => Ok(conv_neutral(arena, depth, s1, s2)?
            && conv(arena, depth, t1, t2)?
            && conv(arena, depth, f1, f2)?
            && conv_closures(arena, depth, Value::var(DeBruijnLevel(depth)), m1, m2)?),
        (
            Neutral::NatElim {
                motive: m1,
                base: b1,
                step: st1,
                scrut: s1,
            },
            Neutral::NatElim {
                motive: m2,
                base: b2,
                step: st2,
                scrut: s2,
            },
        ) => {
            if !conv_neutral(arena, depth, s1, s2)?
                || !conv(arena, depth, b1, b2)?
                || !conv_closures(arena, depth, Value::var(DeBruijnLevel(depth)), m1, m2)?
            {
                return Ok(false);
            }
            let k_var = Value::var(DeBruijnLevel(depth));
            let ih_var = Value::var(DeBruijnLevel(depth + 1));
            let v1 = st1.apply2(arena, k_var.clone(), ih_var.clone())?;
            let v2 = st2.apply2(arena, k_var, ih_var)?;
            conv(arena, depth + 2, &v1, &v2)
        }
        (
            Neutral::DataElim {
                id: i1,
                params: p1,
                motive: m1,
                branches: b1,
                scrut: s1,
            },
            Neutral::DataElim {
                id: i2,
                params: p2,
                motive: m2,
                branches: b2,
                scrut: s2,
            },
        ) => conv_data_elim(arena, depth, (*i1, p1, m1, b1, s1), (*i2, p2, m2, b2, s2)),
        _ => Ok(false),
    }
}

type DataElimParts<'a> = (
    InductiveId,
    &'a [Value],
    &'a Closure,
    &'a [MultiClosure],
    &'a Neutral,
);

fn conv_data_elim(
    arena: &TermArena,
    depth: u32,
    lhs: DataElimParts<'_>,
    rhs: DataElimParts<'_>,
) -> Result<bool, EvalError> {
    let (i1, p1, m1, b1, s1) = lhs;
    let (i2, p2, m2, b2, s2) = rhs;
    if i1 != i2
        || b1.len() != b2.len()
        || !conv_neutral(arena, depth, s1, s2)?
        || !conv_slice(arena, depth, p1, p2)?
        || !conv_closures(arena, depth, Value::var(DeBruijnLevel(depth)), m1, m2)?
    {
        return Ok(false);
    }
    let arities: Vec<u32> = arena.get_inductive(i1).map_or_else(Vec::new, |decl| {
        decl.ctors
            .iter()
            .map(|c| u32::try_from(c.branch_arity()).unwrap_or(0))
            .collect()
    });
    for ((br1, br2), arity) in b1.iter().zip(b2).zip(arities) {
        let mut vars = Vec::with_capacity(arity as usize);
        for offset in 0..arity {
            vars.push(Value::var(DeBruijnLevel(depth + offset)));
        }
        let v1 = br1.apply_many(arena, &vars)?;
        let v2 = br2.apply_many(arena, &vars)?;
        if !conv(arena, depth + arity, &v1, &v2)? {
            return Ok(false);
        }
    }
    Ok(true)
}

pub fn subtype(arena: &TermArena, depth: u32, sub: &Value, sup: &Value) -> Result<bool, EvalError> {
    match (sub, sup) {
        (Value::Universe(l1), Value::Universe(l2)) => Ok(l1.leq(l2)),
        (
            Value::Pi {
                mult: m1,
                domain: d1,
                codomain: c1,
            },
            Value::Pi {
                mult: m2,
                domain: d2,
                codomain: c2,
            },
        ) => {
            if m1 != m2 || !conv(arena, depth, d1, d2)? {
                return Ok(false);
            }
            let var = Value::var(DeBruijnLevel(depth));
            let v1 = c1.apply(arena, var.clone())?;
            let v2 = c2.apply(arena, var)?;
            subtype(arena, depth + 1, &v1, &v2)
        }
        (
            Value::Sigma {
                mult: m1,
                first: f1,
                second: s1,
            },
            Value::Sigma {
                mult: m2,
                first: f2,
                second: s2,
            },
        ) => {
            if m1 != m2 || !subtype(arena, depth, f1, f2)? {
                return Ok(false);
            }
            let var = Value::var(DeBruijnLevel(depth));
            let v1 = s1.apply(arena, var.clone())?;
            let v2 = s2.apply(arena, var)?;
            subtype(arena, depth + 1, &v1, &v2)
        }
        _ => conv(arena, depth, sub, sup),
    }
}

#[cfg(test)]
mod tests {
    use super::{EvalError, Value, conv, eval, proj_fst, proj_snd, quote, subtype};
    use crate::level::Level;
    use crate::multiplicity::Multiplicity;
    use crate::term::{DeBruijnLevel, Index, TermArena};

    const fn assert_send_sync<T: Send + Sync>() {}

    #[test]
    fn value_is_send_and_sync() {
        assert_send_sync::<Value>();
    }

    #[test]
    fn beta_reduces_functions_and_pairs() {
        let mut arena = TermArena::new();
        let x0 = arena.var(Index(0));
        let u0 = arena.universe(Level::zero());
        let u1 = arena.universe(Level::constant(1));
        let id = arena.lam(Multiplicity::One, x0);
        let applied = arena.app(id, u0);

        let val = eval(&arena, &[], applied);
        assert!(val.is_ok());
        if let Ok(v) = val {
            let quoted = quote(&mut arena, 0, &v);
            assert_eq!(quoted, Ok(u0));
        }

        let pair = arena.pair(u0, u1);
        let fst = arena.fst(pair);
        let snd = arena.snd(pair);
        let ann = arena.ann(fst, u1);
        assert_eq!(
            eval(&arena, &[], ann).and_then(|v| quote(&mut arena, 0, &v)),
            Ok(u0)
        );
        assert_eq!(
            eval(&arena, &[], snd).and_then(|v| quote(&mut arena, 0, &v)),
            Ok(u1)
        );
    }

    #[test]
    fn normalizes_open_neutrals_and_eta_equivalence() {
        let mut arena = TermArena::new();
        let x0 = arena.var(Index(0));
        let x1 = arena.var(Index(1));

        let body = arena.app(x1, x0);
        let eta_lam = arena.lam(Multiplicity::One, body);
        let f_var = Value::var(DeBruijnLevel(0));
        let env = vec![f_var.clone()];

        let eta_val = eval(&arena, &env, eta_lam);
        assert!(eta_val.is_ok());
        if let Ok(v) = eta_val {
            assert_eq!(conv(&arena, 1, &v, &f_var), Ok(true));
            assert_eq!(conv(&arena, 1, &f_var, &v), Ok(true));
            let quoted = quote(&mut arena, 1, &v);
            assert_eq!(quoted, Ok(eta_lam));
        }

        let p_fst = arena.fst(x0);
        let p_snd = arena.snd(x0);
        let eta_pair = arena.pair(p_fst, p_snd);
        let pair_val = eval(&arena, &env, eta_pair);
        assert!(pair_val.is_ok());
        if let Ok(v) = pair_val {
            assert_eq!(conv(&arena, 1, &v, &f_var), Ok(true));
            assert_eq!(conv(&arena, 1, &f_var, &v), Ok(true));
            let quoted = quote(&mut arena, 1, &v);
            assert_eq!(quoted, Ok(eta_pair));
        }
    }

    #[test]
    fn checks_conversion_and_cumulative_subtyping() {
        let mut arena = TermArena::new();
        let u0 = arena.universe(Level::zero());
        let u1 = arena.universe(Level::constant(1));
        let x0 = arena.var(Index(0));

        let pi0 = arena.pi(Multiplicity::One, u0, u0);
        let pi1 = arena.pi(Multiplicity::One, u0, u1);
        let pi_many = arena.pi(Multiplicity::Many, u0, u0);

        let v_pi0 = eval(&arena, &[], pi0);
        let v_pi1 = eval(&arena, &[], pi1);
        let v_pi_many = eval(&arena, &[], pi_many);
        assert!(v_pi0.is_ok() && v_pi1.is_ok() && v_pi_many.is_ok());
        if let (Ok(a), Ok(b), Ok(c)) = (v_pi0, v_pi1, v_pi_many) {
            assert_eq!(conv(&arena, 0, &a, &a), Ok(true));
            assert_eq!(conv(&arena, 0, &a, &b), Ok(false));
            assert_eq!(conv(&arena, 0, &a, &c), Ok(false));
            assert_eq!(subtype(&arena, 0, &a, &b), Ok(true));
            assert_eq!(subtype(&arena, 0, &b, &a), Ok(false));
            assert_eq!(subtype(&arena, 0, &a, &c), Ok(false));
            assert_eq!(quote(&mut arena, 0, &a), Ok(pi0));
        }

        let sig0 = arena.sigma(Multiplicity::One, u0, u0);
        let sig1 = arena.sigma(Multiplicity::One, u1, u1);
        let sig_many = arena.sigma(Multiplicity::Many, u0, u0);
        let v_sig0 = eval(&arena, &[], sig0);
        let v_sig1 = eval(&arena, &[], sig1);
        let v_sig_many = eval(&arena, &[], sig_many);
        if let (Ok(a), Ok(b), Ok(c)) = (v_sig0, v_sig1, v_sig_many) {
            assert_eq!(conv(&arena, 0, &a, &a), Ok(true));
            assert_eq!(conv(&arena, 0, &a, &c), Ok(false));
            assert_eq!(subtype(&arena, 0, &a, &b), Ok(true));
            assert_eq!(subtype(&arena, 0, &b, &a), Ok(false));
            assert_eq!(subtype(&arena, 0, &a, &c), Ok(false));
            assert_eq!(quote(&mut arena, 0, &a), Ok(sig0));
        }

        let lam_one = arena.lam(Multiplicity::One, x0);
        let lam_many = arena.lam(Multiplicity::Many, x0);
        if let (Ok(v1), Ok(v2)) = (eval(&arena, &[], lam_one), eval(&arena, &[], lam_many)) {
            assert_eq!(conv(&arena, 0, &v1, &v1), Ok(true));
            assert_eq!(conv(&arena, 0, &v1, &v2), Ok(false));
            assert_eq!(
                conv(&arena, 0, &v1, &Value::Universe(Level::zero())),
                Ok(false)
            );
        }

        let pair_a = arena.pair(u0, u0);
        let pair_b = arena.pair(u0, u1);
        if let (Ok(p1), Ok(p2)) = (eval(&arena, &[], pair_a), eval(&arena, &[], pair_b)) {
            assert_eq!(conv(&arena, 0, &p1, &p1), Ok(true));
            assert_eq!(conv(&arena, 0, &p1, &p2), Ok(false));
        }
    }

    #[test]
    fn distinguishes_neutrals_and_reports_eval_errors() {
        let mut arena = TermArena::new();
        let x0 = arena.var(Index(0));
        let u0 = arena.universe(Level::zero());
        let env = vec![Value::var(DeBruijnLevel(0)), Value::var(DeBruijnLevel(1))];

        let app0 = arena.app(x0, u0);
        let fst0 = arena.fst(x0);
        let snd0 = arena.snd(x0);
        if let (Ok(va), Ok(vf), Ok(vs)) = (
            eval(&arena, &env, app0),
            eval(&arena, &env, fst0),
            eval(&arena, &env, snd0),
        ) {
            assert_eq!(conv(&arena, 2, &va, &va), Ok(true));
            assert_eq!(conv(&arena, 2, &vf, &vf), Ok(true));
            assert_eq!(conv(&arena, 2, &vs, &vs), Ok(true));
            assert_eq!(conv(&arena, 2, &vf, &vs), Ok(false));
            assert_eq!(conv(&arena, 2, &va, &vf), Ok(false));
            assert_eq!(subtype(&arena, 2, &va, &va), Ok(true));
        }

        let unbound = eval(&arena, &[], x0);
        assert_eq!(
            unbound.as_ref().err(),
            Some(&EvalError::UnboundIndex {
                index: Index(0),
                env_len: 0,
            })
        );
        if let Err(err) = unbound {
            assert!(err.to_string().contains("unbound variable #0"));
        }

        let bad_level = quote(&mut arena, 0, &Value::var(DeBruijnLevel(0)));
        assert_eq!(
            bad_level,
            Err(EvalError::InvalidLevel {
                level: DeBruijnLevel(0),
                depth: 0,
            })
        );
        if let Err(err) = bad_level {
            assert!(err.to_string().contains("invalid level @0"));
        }

        let u_val = Value::Universe(Level::zero());
        assert_eq!(conv(&arena, 0, &proj_fst(&u_val), &u_val), Ok(true));
        assert_eq!(conv(&arena, 0, &proj_snd(&u_val), &u_val), Ok(true));

        let invalid_err = EvalError::InvalidTermId(u0);
        assert!(invalid_err.to_string().contains("invalid term id"));
    }

    #[test]
    fn distinguishes_nested_binders_and_partial_matches() {
        let mut arena = TermArena::new();
        let u0 = arena.universe(Level::zero());
        let u1 = arena.universe(Level::constant(1));
        let v0 = arena.var(Index(0));
        let v1 = arena.var(Index(1));
        let v2 = arena.var(Index(2));

        let first_pi_body = arena.pi(Multiplicity::One, u0, v1);
        let pi_a = arena.pi(Multiplicity::One, u0, first_pi_body);
        let second_pi_body = arena.pi(Multiplicity::One, u0, v0);
        let pi_b = arena.pi(Multiplicity::One, u0, second_pi_body);
        if let (Ok(va), Ok(vb)) = (eval(&arena, &[], pi_a), eval(&arena, &[], pi_b)) {
            assert_eq!(quote(&mut arena, 0, &va), Ok(pi_a));
            assert_eq!(conv(&arena, 0, &va, &vb), Ok(false));
            assert_eq!(subtype(&arena, 0, &va, &vb), Ok(false));
        }

        let first_sig_body = arena.sigma(Multiplicity::One, u0, v1);
        let sig_a = arena.sigma(Multiplicity::One, u0, first_sig_body);
        let second_sig_body = arena.sigma(Multiplicity::One, u0, v0);
        let sig_b = arena.sigma(Multiplicity::One, u0, second_sig_body);
        if let (Ok(va), Ok(vb)) = (eval(&arena, &[], sig_a), eval(&arena, &[], sig_b)) {
            assert_eq!(quote(&mut arena, 0, &va), Ok(sig_a));
            assert_eq!(conv(&arena, 0, &va, &vb), Ok(false));
            assert_eq!(subtype(&arena, 0, &va, &vb), Ok(false));
        }

        let first_lam_body = arena.lam(Multiplicity::One, v1);
        let lam_a = arena.lam(Multiplicity::One, first_lam_body);
        let second_lam_body = arena.lam(Multiplicity::One, v0);
        let lam_b = arena.lam(Multiplicity::One, second_lam_body);
        if let (Ok(va), Ok(vb)) = (eval(&arena, &[], lam_a), eval(&arena, &[], lam_b)) {
            assert_eq!(conv(&arena, 0, &va, &vb), Ok(false));
        }

        let f_var = Value::var(DeBruijnLevel(0));
        let g_var = Value::var(DeBruijnLevel(1));
        let env2 = vec![f_var.clone(), g_var];
        let v3 = arena.var(Index(3));
        let f_x = arena.app(v3, v1);
        let f_x_y = arena.app(f_x, v0);
        let eta2_inner = arena.lam(Multiplicity::One, f_x_y);
        let eta2 = arena.lam(Multiplicity::One, eta2_inner);
        let f_y = arena.app(v3, v0);
        let f_y_x = arena.app(f_y, v1);
        let swapped_inner = arena.lam(Multiplicity::One, f_y_x);
        let swapped = arena.lam(Multiplicity::One, swapped_inner);
        let f_x_g = arena.app(f_x, v2);
        let captured_g_inner = arena.lam(Multiplicity::One, f_x_g);
        let captured_g = arena.lam(Multiplicity::One, captured_g_inner);
        if let (Ok(v_eta), Ok(v_swap), Ok(v_cap)) = (
            eval(&arena, &env2, eta2),
            eval(&arena, &env2, swapped),
            eval(&arena, &env2, captured_g),
        ) {
            assert_eq!(conv(&arena, 2, &v_eta, &f_var), Ok(true));
            assert_eq!(conv(&arena, 2, &v_swap, &f_var), Ok(false));
            assert_eq!(conv(&arena, 2, &v_cap, &f_var), Ok(false));
        }

        let fst_f = arena.fst(v1);
        let snd_f = arena.snd(v1);
        let bad_pair_snd = arena.pair(fst_f, u0);
        let bad_pair_fst = arena.pair(u0, snd_f);
        if let (Ok(p_bad_snd), Ok(p_bad_fst)) = (
            eval(&arena, &env2, bad_pair_snd),
            eval(&arena, &env2, bad_pair_fst),
        ) {
            assert_eq!(conv(&arena, 2, &p_bad_snd, &f_var), Ok(false));
            assert_eq!(conv(&arena, 2, &p_bad_fst, &f_var), Ok(false));
        }

        let f_u0 = arena.app(v1, u0);
        let f_u1 = arena.app(v1, u1);
        let g_u0 = arena.app(v0, u0);
        if let (Ok(vf0), Ok(vf1), Ok(vg0)) = (
            eval(&arena, &env2, f_u0),
            eval(&arena, &env2, f_u1),
            eval(&arena, &env2, g_u0),
        ) {
            assert_eq!(conv(&arena, 2, &vf0, &vf1), Ok(false));
            assert_eq!(conv(&arena, 2, &vf0, &vg0), Ok(false));
        }
    }

    #[test]
    fn evaluates_and_quotes_cubical_path_reductions() {
        let mut arena = TermArena::new();
        let u0 = arena.universe(Level::zero());
        let u1 = arena.universe(Level::constant(1));
        let d0 = arena.dim_zero();
        let d1 = arena.dim_one();
        let interval = arena.interval();
        let v0 = arena.var(Index(0));
        let v1 = arena.var(Index(1));
        let v2 = arena.var(Index(2));
        let v3 = arena.var(Index(3));

        let env = vec![
            Value::var(DeBruijnLevel(0)),
            Value::var(DeBruijnLevel(1)),
            Value::dim_var(2),
            Value::dim_var(3),
        ];

        let p_at_0 = arena.papp(v3, u0, u1, d0);
        let p_at_1 = arena.papp(v3, u0, u1, d1);
        assert_eq!(
            eval(&arena, &env, p_at_0).and_then(|v| quote(&mut arena, 4, &v)),
            Ok(u0)
        );
        assert_eq!(
            eval(&arena, &env, p_at_1).and_then(|v| quote(&mut arena, 4, &v)),
            Ok(u1)
        );

        let plam_const = arena.plam(u0);
        let beta_papp = arena.papp(plam_const, u0, u0, v1);
        assert_eq!(
            eval(&arena, &env, beta_papp).and_then(|v| quote(&mut arena, 4, &v)),
            Ok(u0)
        );

        let p_at_i = arena.papp(v3, u0, u1, v1);
        let p_at_j = arena.papp(v3, u0, u1, v0);
        let q_at_i = arena.papp(v2, u0, u1, v1);
        if let (Ok(vpi), Ok(vpj), Ok(vqi)) = (
            eval(&arena, &env, p_at_i),
            eval(&arena, &env, p_at_j),
            eval(&arena, &env, q_at_i),
        ) {
            assert_eq!(quote(&mut arena, 4, &vpi), Ok(p_at_i));
            assert_eq!(conv(&arena, 4, &vpi, &vpi), Ok(true));
            assert_eq!(conv(&arena, 4, &vpi, &vpj), Ok(false));
            assert_eq!(conv(&arena, 4, &vpi, &vqi), Ok(false));
        }

        assert_eq!(
            eval(&arena, &[], interval).and_then(|v| quote(&mut arena, 0, &v)),
            Ok(interval)
        );
        assert_eq!(
            eval(&arena, &[], d0).and_then(|v| quote(&mut arena, 0, &v)),
            Ok(d0)
        );
        assert_eq!(
            eval(&arena, &[], d1).and_then(|v| quote(&mut arena, 0, &v)),
            Ok(d1)
        );
    }

    #[test]
    fn converts_nested_cubical_paths() {
        let mut arena = TermArena::new();
        let u0 = arena.universe(Level::zero());
        let u1 = arena.universe(Level::constant(1));
        let d0 = arena.dim_zero();
        let v0 = arena.var(Index(0));
        let v1 = arena.var(Index(1));

        let path_a = arena.path(u0, u0, u0);
        let path_b = arena.path(u0, u0, u1);
        let path_c = arena.path(u0, u1, u0);
        if let (Ok(va), Ok(vb), Ok(vc)) = (
            eval(&arena, &[], path_a),
            eval(&arena, &[], path_b),
            eval(&arena, &[], path_c),
        ) {
            assert_eq!(quote(&mut arena, 0, &va), Ok(path_a));
            assert_eq!(conv(&arena, 0, &va, &va), Ok(true));
            assert_eq!(conv(&arena, 0, &va, &vb), Ok(false));
            assert_eq!(conv(&arena, 0, &va, &vc), Ok(false));
        }

        let inner_plam_a = arena.plam(v1);
        let nested_plam_a = arena.plam(inner_plam_a);
        let inner_plam_b = arena.plam(v0);
        let nested_plam_b = arena.plam(inner_plam_b);
        if let (Ok(va), Ok(vb)) = (
            eval(&arena, &[], nested_plam_a),
            eval(&arena, &[], nested_plam_b),
        ) {
            assert_eq!(quote(&mut arena, 0, &va), Ok(nested_plam_a));
            assert_eq!(conv(&arena, 0, &va, &va), Ok(true));
            assert_eq!(conv(&arena, 0, &va, &vb), Ok(false));
        }

        let nested_path_inner_a = arena.path(v1, d0, d0);
        let nested_path_a = arena.path(nested_path_inner_a, d0, d0);
        let nested_path_inner_b = arena.path(v0, d0, d0);
        let nested_path_b = arena.path(nested_path_inner_b, d0, d0);
        if let (Ok(va), Ok(vb)) = (
            eval(&arena, &[], nested_path_a),
            eval(&arena, &[], nested_path_b),
        ) {
            assert_eq!(quote(&mut arena, 0, &va), Ok(nested_path_a));
            assert_eq!(conv(&arena, 0, &va, &vb), Ok(false));
        }

        assert_eq!(
            conv(&arena, 0, &Value::Interval, &Value::Interval),
            Ok(true)
        );
        assert_eq!(
            conv(
                &arena,
                0,
                &Value::Dim(crate::cubical::Dim::Zero),
                &Value::Dim(crate::cubical::Dim::One),
            ),
            Ok(false)
        );
    }

    #[test]
    fn computes_and_quotes_cartesian_coercion() {
        let mut arena = TermArena::new();
        let u0 = arena.universe(Level::zero());
        let u1 = arena.universe(Level::constant(1));
        let d0 = arena.dim_zero();
        let d1 = arena.dim_one();
        let v0 = arena.var(Index(0));
        let v1 = arena.var(Index(1));
        let v2 = arena.var(Index(2));

        let env = vec![
            Value::var(DeBruijnLevel(0)),
            Value::var(DeBruijnLevel(1)),
            Value::var(DeBruijnLevel(2)),
        ];

        let deg = arena.coe(v1, d0, d0, v0);
        assert_eq!(
            eval(&arena, &env, deg).and_then(|v| quote(&mut arena, 3, &v)),
            Ok(v0)
        );

        let coe_univ = arena.coe(u1, d0, d1, u0);
        assert_eq!(
            eval(&arena, &[], coe_univ).and_then(|v| quote(&mut arena, 0, &v)),
            Ok(u0)
        );

        let pi_line = arena.pi(Multiplicity::One, u1, u1);
        let id_fn = arena.lam(Multiplicity::One, v0);
        let coe_pi = arena.coe(pi_line, d0, d1, id_fn);
        let coe_pi_app = arena.app(coe_pi, u0);
        assert_eq!(
            eval(&arena, &[], coe_pi_app).and_then(|v| quote(&mut arena, 0, &v)),
            Ok(u0)
        );

        let sig_line = arena.sigma(Multiplicity::One, u1, u1);
        let pair_val = arena.pair(u0, u0);
        let coe_sig = arena.coe(sig_line, d0, d1, pair_val);
        assert_eq!(
            eval(&arena, &[], coe_sig).and_then(|v| quote(&mut arena, 0, &v)),
            Ok(pair_val)
        );

        let line_a = arena.app(v2, v0);
        let line_b = arena.app(v1, v0);
        let i_var_env = vec![
            Value::var(DeBruijnLevel(0)),
            Value::var(DeBruijnLevel(1)),
            Value::dim_var(2),
        ];
        let stuck_a = arena.coe(line_a, d0, d1, v0);
        let stuck_b = arena.coe(line_a, d1, d0, v0);
        let stuck_same_src = arena.coe(line_a, d0, v0, v1);
        let stuck_same_src_d1 = arena.coe(line_a, d0, d1, v1);
        let stuck_c = arena.coe(line_a, d0, d1, v1);
        let stuck_d = arena.coe(line_b, d0, d1, v0);
        let line_lam_a = arena.lam(Multiplicity::One, v1);
        let line_lam_b = arena.lam(Multiplicity::One, v0);
        let stuck_lam_a = arena.coe(line_lam_a, d0, d1, v1);
        let stuck_lam_b = arena.coe(line_lam_b, d0, d1, v1);
        if let (Ok(va), Ok(vb), Ok(vc), Ok(vd)) = (
            eval(&arena, &env, stuck_a),
            eval(&arena, &env, stuck_b),
            eval(&arena, &env, stuck_c),
            eval(&arena, &env, stuck_d),
        ) {
            assert_eq!(quote(&mut arena, 3, &va), Ok(stuck_a));
            assert_eq!(conv(&arena, 3, &va, &va), Ok(true));
            assert_eq!(conv(&arena, 3, &va, &vb), Ok(false));
            assert_eq!(conv(&arena, 3, &va, &vc), Ok(false));
            assert_eq!(conv(&arena, 3, &va, &vd), Ok(false));
        }
        if let (Ok(vs1), Ok(vs2)) = (
            eval(&arena, &i_var_env, stuck_same_src),
            eval(&arena, &i_var_env, stuck_same_src_d1),
        ) {
            assert_eq!(conv(&arena, 3, &vs1, &vs2), Ok(false));
        }
        if let (Ok(vl1), Ok(vl2)) = (
            eval(&arena, &i_var_env, stuck_lam_a),
            eval(&arena, &i_var_env, stuck_lam_b),
        ) {
            assert_eq!(conv(&arena, 3, &vl1, &vl2), Ok(false));
        }
    }

    #[test]
    fn computes_and_quotes_homogeneous_composition() {
        let mut arena = TermArena::new();
        let u0 = arena.universe(Level::zero());
        let u1 = arena.universe(Level::constant(1));
        let d0 = arena.dim_zero();
        let d1 = arena.dim_one();
        let v0 = arena.var(Index(0));
        let v1 = arena.var(Index(1));
        let v2 = arena.var(Index(2));

        let env = vec![
            Value::var(DeBruijnLevel(0)),
            Value::var(DeBruijnLevel(1)),
            Value::dim_var(2),
        ];

        let deg = arena.hcom(v2, d0, d0, vec![], v1);
        assert_eq!(
            eval(&arena, &env, deg).and_then(|v| quote(&mut arena, 3, &v)),
            Ok(v1)
        );

        let top_branch = arena.hcom(u1, d0, d1, vec![(crate::term::CofTerm::Top, u0)], u1);
        assert_eq!(
            eval(&arena, &[], top_branch).and_then(|v| quote(&mut arena, 0, &v)),
            Ok(u0)
        );

        let pi_ty = arena.pi(Multiplicity::One, u1, u1);
        let id_fn = arena.lam(Multiplicity::One, v0);
        let pi_hcom = arena.hcom(
            pi_ty,
            d0,
            d1,
            vec![(crate::term::CofTerm::Eq(v0, d0), id_fn)],
            id_fn,
        );
        let pi_hcom_app = arena.app(pi_hcom, u0);
        let expected_pi_app =
            arena.hcom(u1, d0, d1, vec![(crate::term::CofTerm::Eq(d0, v0), u0)], u0);
        assert_eq!(
            eval(&arena, &env, pi_hcom_app).and_then(|v| quote(&mut arena, 3, &v)),
            Ok(expected_pi_app)
        );

        let face_i0 = crate::term::CofTerm::Eq(v0, d0);
        let face_i1 = crate::term::CofTerm::Eq(v0, d1);
        let face_or = crate::term::CofTerm::Or(
            Box::new(face_i0.clone()),
            Box::new(crate::term::CofTerm::And(
                Box::new(face_i1.clone()),
                Box::new(crate::term::CofTerm::Top),
            )),
        );
        let tube_j = arena.app(v2, v0);
        let stuck_hcom_a = arena.hcom(
            v2,
            d0,
            d1,
            vec![(face_or, tube_j), (crate::term::CofTerm::Bot, v2)],
            v1,
        );
        let stuck_hcom_b = arena.hcom(v2, d0, d1, vec![(face_i0.clone(), tube_j)], v1);
        let stuck_hcom_c = arena.hcom(v2, d1, d0, vec![(face_i1, tube_j)], v1);
        let stuck_hcom_d = arena.hcom(v2, d0, d1, vec![], v1);
        let stuck_hcom_diff_dst = arena.hcom(v2, d0, v0, vec![(face_i0.clone(), tube_j)], v1);
        let stuck_hcom_diff_ty = arena.hcom(v1, d0, d1, vec![(face_i0.clone(), tube_j)], v1);
        let stuck_hcom_diff_cap = arena.hcom(v2, d0, d1, vec![(face_i0, tube_j)], v2);
        if let (Ok(va), Ok(vb), Ok(vc), Ok(vd), Ok(ve), Ok(vf), Ok(vg)) = (
            eval(&arena, &env, stuck_hcom_a),
            eval(&arena, &env, stuck_hcom_b),
            eval(&arena, &env, stuck_hcom_c),
            eval(&arena, &env, stuck_hcom_d),
            eval(&arena, &env, stuck_hcom_diff_dst),
            eval(&arena, &env, stuck_hcom_diff_ty),
            eval(&arena, &env, stuck_hcom_diff_cap),
        ) {
            let quoted_b = quote(&mut arena, 3, &vb);
            assert!(quoted_b.is_ok());
            if let Ok(qb) = quoted_b {
                assert!(arena.format_term(qb).contains("(#2 #0)"));
            }
            assert_eq!(conv(&arena, 3, &va, &va), Ok(true));
            assert_eq!(conv(&arena, 3, &va, &vb), Ok(false));
            assert_eq!(conv(&arena, 3, &va, &vc), Ok(false));
            assert_eq!(conv(&arena, 3, &va, &vd), Ok(false));
            assert_eq!(conv(&arena, 3, &vb, &ve), Ok(false));
            assert_eq!(conv(&arena, 3, &vb, &vf), Ok(false));
            assert_eq!(conv(&arena, 3, &vb, &vg), Ok(false));
        }
    }

    #[test]
    fn distinguishes_nested_coe_line_depths() {
        let mut arena = TermArena::new();
        let d0 = arena.dim_zero();
        let d1 = arena.dim_one();
        let v0 = arena.var(Index(0));
        let v1 = arena.var(Index(1));
        let v2 = arena.var(Index(2));
        let v3 = arena.var(Index(3));
        let env2 = vec![Value::var(DeBruijnLevel(0)), Value::dim_var(1)];
        let fam_inner = arena.papp(v3, d0, d0, v0);
        let fam_mid = arena.papp(v3, d0, d0, v1);
        let fam_outer = arena.papp(v3, d0, d0, v2);
        let line_inner = arena.path(fam_inner, d0, d0);
        let line_mid = arena.path(fam_mid, d0, d0);
        let line_outer = arena.path(fam_outer, d0, d0);
        let coe_inner = arena.coe(line_inner, d0, d1, v1);
        let coe_mid = arena.coe(line_mid, d0, d1, v1);
        let coe_outer = arena.coe(line_outer, d0, d1, v1);
        if let (Ok(val_inner), Ok(val_mid), Ok(val_outer)) = (
            eval(&arena, &env2, coe_inner),
            eval(&arena, &env2, coe_mid),
            eval(&arena, &env2, coe_outer),
        ) {
            assert_eq!(conv(&arena, 2, &val_inner, &val_inner), Ok(true));
            assert_eq!(conv(&arena, 2, &val_inner, &val_mid), Ok(false));
            assert_eq!(conv(&arena, 2, &val_inner, &val_outer), Ok(false));
        }
    }

    #[test]
    fn evaluates_quotes_and_converts_inductive_types_and_discrete_kan() {
        let mut arena = TermArena::new();
        let unit = arena.unit();
        let tt = arena.tt();
        let void = arena.void();
        let bool_ty = arena.bool_ty();
        let b_true = arena.bool_true();
        let b_false = arena.bool_false();
        let nat = arena.nat();
        let zero = arena.zero();
        let one = arena.succ(zero);
        let two = arena.succ(one);
        let three = arena.succ(two);
        let d0 = arena.dim_zero();
        let d1 = arena.dim_one();
        let v0 = arena.var(Index(0));
        let v1 = arena.var(Index(1));

        let succ_v0 = arena.succ(v0);
        let succ_v1 = arena.succ(v1);
        let add_two_one = arena.nat_elim(nat, one, succ_v0, two);
        assert_eq!(
            eval(&arena, &[], add_two_one).and_then(|v| quote(&mut arena, 0, &v)),
            Ok(three)
        );

        let bool_t = arena.bool_elim(bool_ty, b_false, b_true, b_true);
        let bool_f = arena.bool_elim(bool_ty, b_false, b_true, b_false);
        assert_eq!(
            eval(&arena, &[], bool_t).and_then(|v| quote(&mut arena, 0, &v)),
            Ok(b_false)
        );
        assert_eq!(
            eval(&arena, &[], bool_f).and_then(|v| quote(&mut arena, 0, &v)),
            Ok(b_true)
        );

        let unit_r = arena.unit_elim(bool_ty, b_true, tt);
        assert_eq!(
            eval(&arena, &[], unit_r).and_then(|v| quote(&mut arena, 0, &v)),
            Ok(b_true)
        );

        for (ty, val) in [(unit, tt), (bool_ty, b_true), (nat, two), (void, v0)] {
            let env = vec![Value::var(DeBruijnLevel(0))];
            let coerced = arena.coe(ty, d0, d1, val);
            assert_eq!(
                eval(&arena, &env, coerced).and_then(|v| quote(&mut arena, 1, &v)),
                Ok(val)
            );
        }

        let unit_hcom = arena.hcom(unit, d0, d1, vec![], tt);
        assert_eq!(
            eval(&arena, &[], unit_hcom).and_then(|v| quote(&mut arena, 0, &v)),
            Ok(tt)
        );

        let env = vec![Value::var(DeBruijnLevel(0))];
        let n_unit = arena.unit_elim(bool_ty, b_true, v0);
        let n_void = arena.void_elim(bool_ty, v0);
        let n_bool = arena.bool_elim(bool_ty, b_false, b_true, v0);
        let n_nat_a = arena.nat_elim(nat, zero, succ_v0, v0);
        let n_nat_b = arena.nat_elim(nat, zero, succ_v1, v0);
        for term in [n_unit, n_void, n_bool, n_nat_a] {
            let val = eval(&arena, &env, term);
            assert!(val.is_ok());
            if let Ok(v) = val {
                assert_eq!(quote(&mut arena, 1, &v), Ok(term));
                assert_eq!(conv(&arena, 1, &v, &v), Ok(true));
            }
        }
        if let (Ok(va), Ok(vb)) = (eval(&arena, &env, n_nat_a), eval(&arena, &env, n_nat_b)) {
            assert_eq!(conv(&arena, 1, &va, &vb), Ok(false));
        }
    }

    #[test]
    fn quotes_and_compares_inductive_neutrals_with_dependent_motives() {
        let mut arena = TermArena::new();
        let unit = arena.unit();
        let b_true = arena.bool_true();
        let b_false = arena.bool_false();
        let nat = arena.nat();
        let zero = arena.zero();
        let one = arena.succ(zero);
        let v0 = arena.var(Index(0));
        let v1 = arena.var(Index(1));
        let v2 = arena.var(Index(2));
        let v3 = arena.var(Index(3));

        // Depth 3 environment: level 0 = P (Var(2)), level 1 = x (Var(1)), level 2 = y (Var(0))
        let env3 = vec![
            Value::var(DeBruijnLevel(0)),
            Value::var(DeBruijnLevel(1)),
            Value::var(DeBruijnLevel(2)),
        ];
        // Under 1 motive binder (depth 4): P is Var(3), motive arg is Var(0).
        let dep_motive = arena.app(v3, v0);
        let alt_motive = arena.app(v3, v1);

        let u_a = arena.unit_elim(dep_motive, b_true, v0);
        let u_diff_s = arena.unit_elim(dep_motive, b_true, v1);
        let u_diff_b = arena.unit_elim(dep_motive, b_false, v0);
        let u_diff_m = arena.unit_elim(alt_motive, b_true, v0);

        let vd_a = arena.void_elim(dep_motive, v0);
        let vd_diff_s = arena.void_elim(dep_motive, v1);
        let vd_diff_m = arena.void_elim(alt_motive, v0);

        let b_a = arena.bool_elim(dep_motive, b_true, b_false, v0);
        let b_diff_s = arena.bool_elim(dep_motive, b_true, b_false, v1);
        let b_diff_t = arena.bool_elim(dep_motive, b_false, b_false, v0);
        let b_diff_f = arena.bool_elim(dep_motive, b_true, b_true, v0);
        let b_diff_m = arena.bool_elim(alt_motive, b_true, b_false, v0);

        // Under 2 NatElim step binders (depth 5): ih = Var(0), k = Var(1), y = Var(2)
        let n_a = arena.nat_elim(dep_motive, zero, v0, v0);
        let n_diff_s = arena.nat_elim(dep_motive, zero, v0, v1);
        let n_diff_base = arena.nat_elim(dep_motive, one, v0, v0);
        let n_diff_m = arena.nat_elim(alt_motive, zero, v0, v0);
        let n_diff_step_outer = arena.nat_elim(dep_motive, zero, v2, v0);

        for term in [u_a, vd_a, b_a, n_a] {
            let val = eval(&arena, &env3, term);
            assert!(val.is_ok());
            if let Ok(v) = val {
                assert_eq!(quote(&mut arena, 3, &v), Ok(term));
                assert_eq!(conv(&arena, 3, &v, &v), Ok(true));
            }
        }

        for (lhs, rhs) in [
            (u_a, u_diff_s),
            (u_a, u_diff_b),
            (u_a, u_diff_m),
            (vd_a, vd_diff_s),
            (vd_a, vd_diff_m),
            (b_a, b_diff_s),
            (b_a, b_diff_t),
            (b_a, b_diff_f),
            (b_a, b_diff_m),
            (n_a, n_diff_s),
            (n_a, n_diff_base),
            (n_a, n_diff_m),
            (n_a, n_diff_step_outer),
            (u_a, vd_a),
        ] {
            if let (Ok(vl), Ok(vr)) = (eval(&arena, &env3, lhs), eval(&arena, &env3, rhs)) {
                assert_eq!(conv(&arena, 3, &vl, &vr), Ok(false));
            }
        }

        // At depth = 1: step binders are k = level 1, ih = level 2; nested Lam binds level 3 (vs 1*2 = 2).
        let env1 = vec![Value::var(DeBruijnLevel(0))];
        let lam_id = arena.lam(Multiplicity::One, v0);
        let lam_acc = arena.lam(Multiplicity::One, v1);
        let step_lam_a = arena.nat_elim(nat, unit, lam_id, v0);
        let step_lam_b = arena.nat_elim(nat, unit, lam_acc, v0);
        if let (Ok(va), Ok(vb)) = (
            eval(&arena, &env1, step_lam_a),
            eval(&arena, &env1, step_lam_b),
        ) {
            assert_eq!(conv(&arena, 1, &va, &vb), Ok(false));
        }
    }

    #[test]
    fn evaluates_coerces_and_converts_data_edge_cases() {
        use super::{Closure, TypeLine, coe_line};
        use crate::cubical::Dim;
        use crate::inductive::{
            CtorDecl, FieldDecl, InductiveDecl, InductiveId, ParamDecl, check_and_define_inductive,
        };

        let mut arena = TermArena::new();
        let u0 = arena.universe(Level::constant(0));
        let nat = arena.nat();
        let bool_ty = arena.bool_ty();
        let zero = arena.zero();
        let v0 = arena.var(Index(0));
        let v1 = arena.var(Index(1));

        let opt_id = check_and_define_inductive(
            &mut arena,
            InductiveDecl {
                params: vec![ParamDecl {
                    mult: Multiplicity::Zero,
                    ty: u0,
                }],
                level: Level::constant(0),
                ctors: vec![
                    CtorDecl { fields: Vec::new() },
                    CtorDecl {
                        fields: vec![FieldDecl {
                            mult: Multiplicity::One,
                            ty: v0,
                            is_recursive: false,
                        }],
                    },
                ],
            },
        );
        let self_list = arena.data(InductiveId(1), vec![v1]);
        let list_id = check_and_define_inductive(
            &mut arena,
            InductiveDecl {
                params: vec![ParamDecl {
                    mult: Multiplicity::Zero,
                    ty: u0,
                }],
                level: Level::constant(0),
                ctors: vec![
                    CtorDecl { fields: Vec::new() },
                    CtorDecl {
                        fields: vec![
                            FieldDecl {
                                mult: Multiplicity::One,
                                ty: v0,
                                is_recursive: false,
                            },
                            FieldDecl {
                                mult: Multiplicity::One,
                                ty: self_list,
                                is_recursive: false,
                            },
                        ],
                    },
                ],
            },
        );
        assert!(opt_id.is_ok() && list_id.is_ok());
        let (Ok(opt_id), Ok(list_id)) = (opt_id, list_id) else {
            return;
        };

        // eval_data_elim with mismatched constructor inductive id must not reduce.
        let nil_nat = arena.ctor(list_id, 0, vec![nat], Vec::new());
        let mis_elim = arena.data_elim(opt_id, vec![nat], nat, vec![zero, v0], nil_nat);
        assert!(matches!(
            eval(&arena, &[], mis_elim),
            Ok(Value::Ctor { id, .. }) if id == list_id
        ));

        // coe_line on parameterized Data must remain neutral.
        let opt_nat = arena.data(opt_id, vec![nat]);
        let line = TypeLine::Closure(Closure::new(Vec::new(), opt_nat));
        let coerced = coe_line(&arena, &line, Dim::Zero, Dim::One, Value::Zero);
        assert!(matches!(coerced, Ok(Value::Neutral(_))));

        // conv_data_value: same id + diff params, and diff id + same params.
        let opt_bool = arena.data(opt_id, vec![bool_ty]);
        let list_nat = arena.data(list_id, vec![nat]);
        if let (Ok(v_on), Ok(v_ob), Ok(v_ln)) = (
            eval(&arena, &[], opt_nat),
            eval(&arena, &[], opt_bool),
            eval(&arena, &[], list_nat),
        ) {
            assert_eq!(conv(&arena, 0, &v_on, &v_ob), Ok(false));
            assert_eq!(conv(&arena, 0, &v_on, &v_ln), Ok(false));
        }

        // Different inductive id with equal branch count (2 vs 2) must not convert.
        let env1 = vec![Value::var(DeBruijnLevel(0))];
        let opt_e = arena.data_elim(opt_id, vec![nat], nat, vec![zero, zero], v0);
        let list_e = arena.data_elim(list_id, vec![nat], nat, vec![zero, zero], v0);
        if let (Ok(vo), Ok(vl)) = (eval(&arena, &env1, opt_e), eval(&arena, &env1, list_e)) {
            assert_eq!(conv(&arena, 1, &vo, &vl), Ok(false));
        }
    }

    #[test]
    fn quotes_and_converts_multi_binder_data_elim_at_depths() {
        use crate::inductive::{
            CtorDecl, FieldDecl, InductiveDecl, InductiveId, ParamDecl, check_and_define_inductive,
        };

        let mut arena = TermArena::new();
        let u0 = arena.universe(Level::constant(0));
        let nat = arena.nat();
        let zero = arena.zero();
        let v0 = arena.var(Index(0));
        let v1 = arena.var(Index(1));
        let v2 = arena.var(Index(2));
        let v3 = arena.var(Index(3));

        let self_list = arena.data(InductiveId(0), vec![v1]);
        let list_id = check_and_define_inductive(
            &mut arena,
            InductiveDecl {
                params: vec![ParamDecl {
                    mult: Multiplicity::Zero,
                    ty: u0,
                }],
                level: Level::constant(0),
                ctors: vec![
                    CtorDecl { fields: Vec::new() },
                    CtorDecl {
                        fields: vec![
                            FieldDecl {
                                mult: Multiplicity::One,
                                ty: v0,
                                is_recursive: false,
                            },
                            FieldDecl {
                                mult: Multiplicity::One,
                                ty: self_list,
                                is_recursive: false,
                            },
                        ],
                    },
                ],
            },
        );
        assert!(list_id.is_ok());
        let Ok(list_id) = list_id else {
            return;
        };

        // Quote multi-binder Cons branch at depth 3.
        let env3 = vec![
            Value::var(DeBruijnLevel(0)),
            Value::var(DeBruijnLevel(1)),
            Value::var(DeBruijnLevel(2)),
        ];
        let list_elim_3 = arena.data_elim(list_id, vec![nat], nat, vec![zero, v0], v0);
        if let Ok(vl3) = eval(&arena, &env3, list_elim_3) {
            assert_eq!(quote(&mut arena, 3, &vl3), Ok(list_elim_3));
        }

        // Depth 1: Cons binds levels 1 (head=v2), 2 (tail=v1), 3 (ih=v0); env0 is level 0 (v3).
        let env1 = vec![Value::var(DeBruijnLevel(0))];
        let lam_v0 = arena.lam(Multiplicity::One, v0);
        let lam_v1 = arena.lam(Multiplicity::One, v1);
        let le_head = arena.data_elim(list_id, vec![nat], nat, vec![zero, v2], v0);
        let le_env0 = arena.data_elim(list_id, vec![nat], nat, vec![zero, v3], v0);
        let le_lam0 = arena.data_elim(list_id, vec![nat], nat, vec![zero, lam_v0], v0);
        let le_lam1 = arena.data_elim(list_id, vec![nat], nat, vec![zero, lam_v1], v0);
        if let (Ok(a), Ok(b), Ok(c), Ok(d)) = (
            eval(&arena, &env1, le_head),
            eval(&arena, &env1, le_env0),
            eval(&arena, &env1, le_lam0),
            eval(&arena, &env1, le_lam1),
        ) {
            assert_eq!(conv(&arena, 1, &a, &b), Ok(false));
            assert_eq!(conv(&arena, 1, &c, &d), Ok(false));
        }

        // Depth 2: Cons binds levels 2 (head=v2), 3 (tail=v1), 4 (ih=v0); env1 is level 1 (v3).
        let env2 = vec![Value::var(DeBruijnLevel(0)), Value::var(DeBruijnLevel(1))];
        let le_tail = arena.data_elim(list_id, vec![nat], nat, vec![zero, v1], v0);
        let le_env1 = arena.data_elim(list_id, vec![nat], nat, vec![zero, v3], v0);
        if let (Ok(a), Ok(b)) = (eval(&arena, &env2, le_tail), eval(&arena, &env2, le_env1)) {
            assert_eq!(conv(&arena, 2, &a, &b), Ok(false));
        }
    }
}
