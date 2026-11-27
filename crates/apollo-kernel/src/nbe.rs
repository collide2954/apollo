use std::fmt;
use std::sync::Arc;

use crate::cubical::{Cof, Dim, DimVar};
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
        Value::Universe(_) => Ok(term),
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
    }
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
        (Value::Interval, Value::Interval) => Ok(true),
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
        (Value::Neutral(n1), Value::Neutral(n2)) => conv_neutral(arena, depth, n1, n2),
        _ => Ok(false),
    }
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
        _ => Ok(false),
    }
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
}
