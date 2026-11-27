use std::fmt;
use std::sync::Arc;

use crate::level::Level;
use crate::multiplicity::Multiplicity;
use crate::term::{DeBruijnLevel, Index, Term, TermArena, TermId};

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
pub struct Closure {
    env: Env,
    body: TermId,
}

impl Closure {
    #[must_use]
    pub const fn new(env: Env, body: TermId) -> Self {
        Self { env, body }
    }

    pub fn apply(&self, arena: &TermArena, arg: Value) -> Result<Value, EvalError> {
        let mut next_env = self.env.clone();
        next_env.push(arg);
        eval(arena, &next_env, self.body)
    }
}

#[derive(Debug, Clone)]
pub enum Neutral {
    Var(DeBruijnLevel),
    App { func: Arc<Self>, arg: Value },
    Fst(Arc<Self>),
    Snd(Arc<Self>),
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
    Neutral(Arc<Neutral>),
}

impl Value {
    #[must_use]
    pub fn var(level: DeBruijnLevel) -> Self {
        Self::Neutral(Arc::new(Neutral::Var(level)))
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
    }
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
            let var = Value::var(DeBruijnLevel(depth));
            let v1 = c1.apply(arena, var.clone())?;
            let v2 = c2.apply(arena, var)?;
            conv(arena, depth + 1, &v1, &v2)
        }
        (Value::Lam { mult: m1, body: b1 }, Value::Lam { mult: m2, body: b2 }) => {
            if m1 != m2 {
                return Ok(false);
            }
            let var = Value::var(DeBruijnLevel(depth));
            let v1 = b1.apply(arena, var.clone())?;
            let v2 = b2.apply(arena, var)?;
            conv(arena, depth + 1, &v1, &v2)
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
            let var = Value::var(DeBruijnLevel(depth));
            let v1 = s1.apply(arena, var.clone())?;
            let v2 = s2.apply(arena, var)?;
            conv(arena, depth + 1, &v1, &v2)
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
}
