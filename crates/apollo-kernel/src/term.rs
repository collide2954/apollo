use std::collections::HashMap;
use std::fmt;

use crate::level::Level;
use crate::multiplicity::Multiplicity;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Index(pub u32);

impl fmt::Display for Index {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#{}", self.0)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DeBruijnLevel(pub u32);

impl DeBruijnLevel {
    #[must_use]
    pub const fn to_index(self, depth: u32) -> Option<Index> {
        if self.0 < depth {
            Some(Index(depth - 1 - self.0))
        } else {
            None
        }
    }
}

impl fmt::Display for DeBruijnLevel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "@{}", self.0)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TermId(u32);

impl TermId {
    #[must_use]
    pub const fn raw(self) -> u32 {
        self.0
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Term {
    Universe(Level),
    Var(Index),
    Pi {
        mult: Multiplicity,
        domain: TermId,
        codomain: TermId,
    },
    Lam {
        mult: Multiplicity,
        body: TermId,
    },
    App {
        func: TermId,
        arg: TermId,
    },
    Sigma {
        mult: Multiplicity,
        first: TermId,
        second: TermId,
    },
    Pair {
        first: TermId,
        second: TermId,
    },
    Fst(TermId),
    Snd(TermId),
    Ann {
        term: TermId,
        ty: TermId,
    },
    Interval,
    DimZero,
    DimOne,
    Path {
        family: TermId,
        left: TermId,
        right: TermId,
    },
    PLam(TermId),
    PApp {
        path: TermId,
        left: TermId,
        right: TermId,
        dim: TermId,
    },
}

#[derive(Debug, Clone, Default)]
pub struct TermArena {
    nodes: Vec<Term>,
    intern: HashMap<Term, TermId>,
}

impl TermArena {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    #[must_use]
    pub const fn len(&self) -> usize {
        self.nodes.len()
    }

    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    #[must_use]
    pub fn get(&self, id: TermId) -> Option<&Term> {
        self.nodes.get(id.0 as usize)
    }

    #[must_use]
    pub fn intern(&mut self, term: Term) -> TermId {
        if let Some(&existing) = self.intern.get(&term) {
            return existing;
        }
        let raw = u32::try_from(self.nodes.len()).unwrap_or(u32::MAX);
        let id = TermId(raw);
        self.nodes.push(term.clone());
        self.intern.insert(term, id);
        id
    }

    #[must_use]
    pub fn universe(&mut self, level: Level) -> TermId {
        self.intern(Term::Universe(level))
    }

    #[must_use]
    pub fn var(&mut self, index: Index) -> TermId {
        self.intern(Term::Var(index))
    }

    #[must_use]
    pub fn pi(&mut self, mult: Multiplicity, domain: TermId, codomain: TermId) -> TermId {
        self.intern(Term::Pi {
            mult,
            domain,
            codomain,
        })
    }

    #[must_use]
    pub fn lam(&mut self, mult: Multiplicity, body: TermId) -> TermId {
        self.intern(Term::Lam { mult, body })
    }

    #[must_use]
    pub fn app(&mut self, func: TermId, arg: TermId) -> TermId {
        self.intern(Term::App { func, arg })
    }

    #[must_use]
    pub fn sigma(&mut self, mult: Multiplicity, first: TermId, second: TermId) -> TermId {
        self.intern(Term::Sigma {
            mult,
            first,
            second,
        })
    }

    #[must_use]
    pub fn pair(&mut self, first: TermId, second: TermId) -> TermId {
        self.intern(Term::Pair { first, second })
    }

    #[must_use]
    pub fn fst(&mut self, pair: TermId) -> TermId {
        self.intern(Term::Fst(pair))
    }

    #[must_use]
    pub fn snd(&mut self, pair: TermId) -> TermId {
        self.intern(Term::Snd(pair))
    }

    #[must_use]
    pub fn ann(&mut self, term: TermId, ty: TermId) -> TermId {
        self.intern(Term::Ann { term, ty })
    }

    #[must_use]
    pub fn interval(&mut self) -> TermId {
        self.intern(Term::Interval)
    }

    #[must_use]
    pub fn dim_zero(&mut self) -> TermId {
        self.intern(Term::DimZero)
    }

    #[must_use]
    pub fn dim_one(&mut self) -> TermId {
        self.intern(Term::DimOne)
    }

    #[must_use]
    pub fn path(&mut self, family: TermId, left: TermId, right: TermId) -> TermId {
        self.intern(Term::Path {
            family,
            left,
            right,
        })
    }

    #[must_use]
    pub fn plam(&mut self, body: TermId) -> TermId {
        self.intern(Term::PLam(body))
    }

    #[must_use]
    pub fn papp(&mut self, path: TermId, left: TermId, right: TermId, dim: TermId) -> TermId {
        self.intern(Term::PApp {
            path,
            left,
            right,
            dim,
        })
    }

    #[must_use]
    pub fn format_term(&self, id: TermId) -> String {
        let Some(term) = self.get(id) else {
            return format!("<invalid:{}>", id.raw());
        };
        match term {
            Term::Universe(level) => format!("Type {level}"),
            Term::Var(index) => index.to_string(),
            Term::Pi {
                mult,
                domain,
                codomain,
            } => format!(
                "({mult} : {}) -> {}",
                self.format_term(*domain),
                self.format_term(*codomain)
            ),
            Term::Lam { mult, body } => format!("\\{mult} => {}", self.format_term(*body)),
            Term::App { func, arg } => {
                format!("({} {})", self.format_term(*func), self.format_term(*arg))
            }
            Term::Sigma {
                mult,
                first,
                second,
            } => format!(
                "Sigma({mult} : {}, {})",
                self.format_term(*first),
                self.format_term(*second)
            ),
            Term::Pair { first, second } => {
                format!(
                    "({}, {})",
                    self.format_term(*first),
                    self.format_term(*second)
                )
            }
            Term::Fst(pair) => format!("{}.0", self.format_term(*pair)),
            Term::Snd(pair) => format!("{}.1", self.format_term(*pair)),
            Term::Ann { term, ty } => {
                format!("({} : {})", self.format_term(*term), self.format_term(*ty))
            }
            Term::Interval => "I".to_owned(),
            Term::DimZero => "0".to_owned(),
            Term::DimOne => "1".to_owned(),
            Term::Path {
                family,
                left,
                right,
            } => format!(
                "Path({}, {}, {})",
                self.format_term(*family),
                self.format_term(*left),
                self.format_term(*right)
            ),
            Term::PLam(body) => format!("<i> {}", self.format_term(*body)),
            Term::PApp { path, dim, .. } => {
                format!("({} @ {})", self.format_term(*path), self.format_term(*dim))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{DeBruijnLevel, Index, Term, TermArena, TermId};
    use crate::level::Level;
    use crate::multiplicity::Multiplicity;

    #[test]
    fn converts_debruijn_levels_to_indices() {
        assert_eq!(DeBruijnLevel(0).to_index(0), None);
        assert_eq!(DeBruijnLevel(0).to_index(1), Some(Index(0)));
        assert_eq!(DeBruijnLevel(0).to_index(3), Some(Index(2)));
        assert_eq!(DeBruijnLevel(2).to_index(3), Some(Index(0)));
        assert_eq!(DeBruijnLevel(3).to_index(3), None);
        assert_eq!(Index(2).to_string(), "#2");
        assert_eq!(DeBruijnLevel(4).to_string(), "@4");
    }

    #[test]
    fn hash_conses_identical_terms_with_structural_sharing() {
        let mut arena = TermArena::new();
        assert!(arena.is_empty());
        assert_eq!(arena.len(), 0);

        let type0_a = arena.universe(Level::zero());
        let type0_b = arena.universe(Level::zero());
        assert_eq!(type0_a, type0_b);
        assert_eq!(type0_a.raw(), 0);
        assert!(!arena.is_empty());
        assert_eq!(arena.len(), 1);

        let v0 = arena.var(Index(0));
        let id_a = arena.lam(Multiplicity::One, v0);
        let id_b = arena.lam(Multiplicity::One, v0);
        let id_many = arena.lam(Multiplicity::Many, v0);
        assert_eq!(id_a, id_b);
        assert_ne!(id_a, id_many);
        assert_eq!(arena.get(v0), Some(&Term::Var(Index(0))));
        assert_eq!(arena.get(TermId(999)), None);
    }

    #[test]
    fn formats_all_term_forms() {
        let mut arena = TermArena::new();
        let u0 = arena.universe(Level::zero());
        let x = arena.var(Index(0));
        let pi = arena.pi(Multiplicity::One, u0, x);
        let lam = arena.lam(Multiplicity::Many, x);
        let app = arena.app(lam, x);
        let sigma = arena.sigma(Multiplicity::One, u0, x);
        let pair = arena.pair(x, u0);
        let fst = arena.fst(pair);
        let snd = arena.snd(pair);
        let ann = arena.ann(x, u0);
        let interval = arena.interval();
        let d0 = arena.dim_zero();
        let d1 = arena.dim_one();
        let path = arena.path(u0, x, x);
        let plam = arena.plam(x);
        let papp = arena.papp(plam, x, x, d0);

        assert_eq!(arena.format_term(u0), "Type 0");
        assert_eq!(arena.format_term(pi), "(1 : Type 0) -> #0");
        assert_eq!(arena.format_term(lam), "\\ω => #0");
        assert_eq!(arena.format_term(app), "(\\ω => #0 #0)");
        assert_eq!(arena.format_term(sigma), "Sigma(1 : Type 0, #0)");
        assert_eq!(arena.format_term(pair), "(#0, Type 0)");
        assert_eq!(arena.format_term(fst), "(#0, Type 0).0");
        assert_eq!(arena.format_term(snd), "(#0, Type 0).1");
        assert_eq!(arena.format_term(ann), "(#0 : Type 0)");
        assert_eq!(arena.format_term(interval), "I");
        assert_eq!(arena.format_term(d0), "0");
        assert_eq!(arena.format_term(d1), "1");
        assert_eq!(arena.format_term(path), "Path(Type 0, #0, #0)");
        assert_eq!(arena.format_term(plam), "<i> #0");
        assert_eq!(arena.format_term(papp), "(<i> #0 @ 0)");
        assert_eq!(arena.format_term(TermId(999)), "<invalid:999>");
    }
}
