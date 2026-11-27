use std::cmp::Ordering;
use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LevelVar(pub u32);

impl fmt::Display for LevelVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "u{}", self.0)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Level {
    constant: u32,
    vars: Vec<(LevelVar, u32)>,
}

impl Level {
    #[must_use]
    pub const fn zero() -> Self {
        Self::constant(0)
    }

    #[must_use]
    pub const fn constant(value: u32) -> Self {
        Self {
            constant: value,
            vars: Vec::new(),
        }
    }

    #[must_use]
    pub fn var(var: LevelVar) -> Self {
        Self::var_plus(var, 0)
    }

    #[must_use]
    pub fn var_plus(var: LevelVar, offset: u32) -> Self {
        Self {
            constant: offset,
            vars: vec![(var, offset)],
        }
    }

    #[must_use]
    pub const fn is_zero(&self) -> bool {
        self.constant == 0 && self.vars.is_empty()
    }

    #[must_use]
    pub const fn constant_part(&self) -> u32 {
        self.constant
    }

    #[must_use]
    pub fn vars(&self) -> &[(LevelVar, u32)] {
        &self.vars
    }

    #[must_use]
    pub fn succ(&self) -> Self {
        self.add_offset(1)
    }

    #[must_use]
    pub fn add_offset(&self, offset: u32) -> Self {
        if offset == 0 {
            return self.clone();
        }
        Self {
            constant: self.constant.saturating_add(offset),
            vars: self
                .vars
                .iter()
                .map(|&(var, k)| (var, k.saturating_add(offset)))
                .collect(),
        }
    }

    #[must_use]
    pub fn max(&self, other: &Self) -> Self {
        let mut vars = Vec::with_capacity(self.vars.len() + other.vars.len());
        let mut i = 0;
        let mut j = 0;
        while i < self.vars.len() && j < other.vars.len() {
            let (lv, lk) = self.vars[i];
            let (rv, rk) = other.vars[j];
            match lv.cmp(&rv) {
                Ordering::Less => {
                    vars.push((lv, lk));
                    i += 1;
                }
                Ordering::Greater => {
                    vars.push((rv, rk));
                    j += 1;
                }
                Ordering::Equal => {
                    vars.push((lv, lk.max(rk)));
                    i += 1;
                    j += 1;
                }
            }
        }
        vars.extend_from_slice(&self.vars[i..]);
        vars.extend_from_slice(&other.vars[j..]);
        Self {
            constant: self.constant.max(other.constant),
            vars,
        }
    }

    #[must_use]
    pub fn leq(&self, other: &Self) -> bool {
        if self.constant > other.constant {
            return false;
        }
        let mut j = 0;
        for &(var, offset) in &self.vars {
            while j < other.vars.len() && other.vars[j].0 < var {
                j += 1;
            }
            if j >= other.vars.len() || other.vars[j].0 != var || offset > other.vars[j].1 {
                return false;
            }
        }
        true
    }

    #[must_use]
    pub fn subst(&self, env: &[Self]) -> Self {
        let mut result = Self::constant(self.constant);
        for &(var, offset) in &self.vars {
            let term = env.get(var.0 as usize).map_or_else(
                || Self::var_plus(var, offset),
                |replacement| replacement.add_offset(offset),
            );
            result = result.max(&term);
        }
        result
    }

    #[must_use]
    pub fn eval<F>(&self, valuation: F) -> u32
    where
        F: Fn(LevelVar) -> u32,
    {
        let mut acc = self.constant;
        for &(var, offset) in &self.vars {
            acc = acc.max(valuation(var).saturating_add(offset));
        }
        acc
    }
}

impl fmt::Display for Level {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.vars.is_empty() {
            return write!(f, "{}", self.constant);
        }

        let max_var_offset = self.vars.iter().map(|&(_, k)| k).max().unwrap_or(0);
        let include_const = self.constant > max_var_offset;
        let term_count = self.vars.len() + usize::from(include_const);

        if term_count == 1 {
            let (var, offset) = self.vars[0];
            return format_var_term(f, var, offset);
        }

        f.write_str("max(")?;
        let mut need_comma = include_const;
        if include_const {
            write!(f, "{}", self.constant)?;
        }
        for &(var, offset) in &self.vars {
            if need_comma {
                f.write_str(", ")?;
            }
            format_var_term(f, var, offset)?;
            need_comma = true;
        }
        f.write_str(")")
    }
}

fn format_var_term(f: &mut fmt::Formatter<'_>, var: LevelVar, offset: u32) -> fmt::Result {
    if offset == 0 {
        write!(f, "{var}")
    } else {
        write!(f, "{var} + {offset}")
    }
}

#[cfg(test)]
mod tests {
    use super::{Level, LevelVar};

    fn sample_levels() -> Vec<Level> {
        let u0 = Level::var(LevelVar(0));
        let u1 = Level::var(LevelVar(1));
        let u2 = Level::var(LevelVar(2));
        vec![
            Level::zero(),
            Level::constant(1),
            Level::constant(3),
            u0.clone(),
            u0.succ(),
            u1.clone(),
            u1.add_offset(2),
            u0.max(&u1),
            u0.succ().max(&u1),
            u1.max(&u2).max(&Level::constant(2)),
            u0.max(&u1).max(&u2),
        ]
    }

    #[test]
    fn satisfies_semilattice_and_succ_laws() {
        let levels = sample_levels();
        for a in &levels {
            assert_eq!(a.max(&Level::zero()), *a);
            assert_eq!(Level::zero().max(a), *a);
            assert_eq!(a.max(a), *a);
            assert_eq!(a.add_offset(0), *a);
            assert!(a.leq(&a.succ()));
            assert!(!a.succ().leq(a));

            for b in &levels {
                assert_eq!(a.max(b), b.max(a));
                assert_eq!(a.max(b).succ(), a.succ().max(&b.succ()));
                assert!(a.leq(&a.max(b)));
                assert!(b.leq(&a.max(b)));

                for c in &levels {
                    assert_eq!(a.max(b).max(c), a.max(&b.max(c)));
                }
            }
        }
    }

    #[test]
    fn canonical_leq_and_eq_match_semantic_valuations() {
        let levels = sample_levels();
        for a in &levels {
            for b in &levels {
                let mut is_lower_bound = true;
                let mut is_same_value = true;
                for v0 in 0..=4 {
                    for v1 in 0..=4 {
                        for v2 in 0..=4 {
                            let val = |v: LevelVar| match v.0 {
                                0 => v0,
                                1 => v1,
                                _ => v2,
                            };
                            let lhs = a.eval(val);
                            let rhs = b.eval(val);
                            if lhs > rhs {
                                is_lower_bound = false;
                            }
                            if lhs != rhs {
                                is_same_value = false;
                            }
                        }
                    }
                }
                assert_eq!(a.leq(b), is_lower_bound, "leq mismatch for {a} <= {b}");
                assert_eq!(a == b, is_same_value, "eq mismatch for {a} == {b}");
            }
        }
    }

    #[test]
    fn substitution_agrees_with_evaluation() {
        let env = vec![
            Level::var(LevelVar(1)).succ(),
            Level::constant(2).max(&Level::var(LevelVar(2))),
        ];
        for level in sample_levels() {
            let substituted = level.subst(&env);
            for v0 in 0..=3 {
                for v1 in 0..=3 {
                    for v2 in 0..=3 {
                        let val = |v: LevelVar| match v.0 {
                            0 => v0,
                            1 => v1,
                            _ => v2,
                        };
                        let lhs = substituted.eval(val);
                        let rhs = level.eval(|v| {
                            env.get(v.0 as usize)
                                .map_or_else(|| val(v), |replacement| replacement.eval(val))
                        });
                        assert_eq!(lhs, rhs);
                    }
                }
            }
        }
    }

    #[test]
    fn inspects_and_formats_levels() {
        let zero = Level::zero();
        assert!(zero.is_zero());
        assert_eq!(zero.constant_part(), 0);
        assert_eq!(zero.vars(), &[]);
        assert_eq!(zero.to_string(), "0");

        let one = Level::constant(1);
        assert!(!one.is_zero());
        assert_eq!(one.constant_part(), 1);
        assert_eq!(one.to_string(), "1");

        let u0 = Level::var(LevelVar(0));
        assert!(!u0.is_zero());
        assert_eq!(u0.vars(), &[(LevelVar(0), 0)]);
        assert_eq!(u0.to_string(), "u0");

        let u0_succ = u0.succ();
        assert_eq!(u0_succ.constant_part(), 1);
        assert_eq!(u0_succ.to_string(), "u0 + 1");

        let merged = u0.max(&Level::var_plus(LevelVar(1), 1));
        assert_eq!(merged.to_string(), "max(u0, u1 + 1)");

        let with_const = Level::constant(3).max(&u0);
        assert_eq!(with_const.to_string(), "max(3, u0)");
    }
}
