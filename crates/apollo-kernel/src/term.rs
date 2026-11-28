use std::collections::HashMap;
use std::fmt;

use crate::inductive::{InductiveDecl, InductiveId};
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
pub enum CofTerm {
    Top,
    Bot,
    Eq(TermId, TermId),
    And(Box<Self>, Box<Self>),
    Or(Box<Self>, Box<Self>),
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
    Coe {
        line: TermId,
        src: TermId,
        dst: TermId,
        term: TermId,
    },
    HCom {
        ty: TermId,
        src: TermId,
        dst: TermId,
        branches: Vec<(CofTerm, TermId)>,
        cap: TermId,
    },
    VType {
        dim: TermId,
        ty0: TermId,
        ty1: TermId,
        equiv: TermId,
    },
    VIn {
        dim: TermId,
        left: TermId,
        right: TermId,
    },
    VProj {
        dim: TermId,
        ty0: TermId,
        ty1: TermId,
        equiv: TermId,
        term: TermId,
    },
    Unit,
    Tt,
    UnitElim {
        motive: TermId,
        on_unit: TermId,
        scrut: TermId,
    },
    Void,
    VoidElim {
        motive: TermId,
        scrut: TermId,
    },
    Bool,
    True,
    False,
    BoolElim {
        motive: TermId,
        on_true: TermId,
        on_false: TermId,
        scrut: TermId,
    },
    Nat,
    Zero,
    Succ(TermId),
    NatElim {
        motive: TermId,
        base: TermId,
        step: TermId,
        scrut: TermId,
    },
    Data {
        id: InductiveId,
        params: Vec<TermId>,
    },
    Ctor {
        id: InductiveId,
        ctor: u32,
        params: Vec<TermId>,
        args: Vec<TermId>,
    },
    DataElim {
        id: InductiveId,
        params: Vec<TermId>,
        motive: TermId,
        branches: Vec<TermId>,
        scrut: TermId,
    },
}

#[derive(Debug, Clone, Default)]
pub struct TermArena {
    nodes: Vec<Term>,
    intern: HashMap<Term, TermId>,
    inductives: Vec<InductiveDecl>,
}

impl TermArena {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    #[must_use]
    pub fn next_inductive_id(&self) -> InductiveId {
        let raw = u32::try_from(self.inductives.len()).unwrap_or(u32::MAX);
        InductiveId(raw)
    }

    #[must_use]
    pub fn get_inductive(&self, id: InductiveId) -> Option<&InductiveDecl> {
        self.inductives.get(id.raw() as usize)
    }

    #[must_use]
    pub const fn inductive_count(&self) -> usize {
        self.inductives.len()
    }

    pub(crate) fn push_inductive_raw(&mut self, decl: InductiveDecl) {
        self.inductives.push(decl);
    }

    pub(crate) fn set_inductive_raw(&mut self, id: InductiveId, decl: InductiveDecl) {
        if let Some(slot) = self.inductives.get_mut(id.raw() as usize) {
            *slot = decl;
        }
    }

    pub(crate) fn pop_inductive_raw(&mut self) {
        let _ = self.inductives.pop();
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
    pub fn coe(&mut self, line: TermId, src: TermId, dst: TermId, term: TermId) -> TermId {
        self.intern(Term::Coe {
            line,
            src,
            dst,
            term,
        })
    }

    #[must_use]
    pub fn hcom(
        &mut self,
        ty: TermId,
        src: TermId,
        dst: TermId,
        branches: Vec<(CofTerm, TermId)>,
        cap: TermId,
    ) -> TermId {
        self.intern(Term::HCom {
            ty,
            src,
            dst,
            branches,
            cap,
        })
    }

    #[must_use]
    pub fn unit(&mut self) -> TermId {
        self.intern(Term::Unit)
    }

    #[must_use]
    pub fn tt(&mut self) -> TermId {
        self.intern(Term::Tt)
    }

    #[must_use]
    pub fn unit_elim(&mut self, motive: TermId, on_unit: TermId, scrut: TermId) -> TermId {
        self.intern(Term::UnitElim {
            motive,
            on_unit,
            scrut,
        })
    }

    #[must_use]
    pub fn void(&mut self) -> TermId {
        self.intern(Term::Void)
    }

    #[must_use]
    pub fn void_elim(&mut self, motive: TermId, scrut: TermId) -> TermId {
        self.intern(Term::VoidElim { motive, scrut })
    }

    #[must_use]
    pub fn bool_ty(&mut self) -> TermId {
        self.intern(Term::Bool)
    }

    #[must_use]
    pub fn bool_true(&mut self) -> TermId {
        self.intern(Term::True)
    }

    #[must_use]
    pub fn bool_false(&mut self) -> TermId {
        self.intern(Term::False)
    }

    #[must_use]
    pub fn bool_elim(
        &mut self,
        motive: TermId,
        on_true: TermId,
        on_false: TermId,
        scrut: TermId,
    ) -> TermId {
        self.intern(Term::BoolElim {
            motive,
            on_true,
            on_false,
            scrut,
        })
    }

    #[must_use]
    pub fn nat(&mut self) -> TermId {
        self.intern(Term::Nat)
    }

    #[must_use]
    pub fn zero(&mut self) -> TermId {
        self.intern(Term::Zero)
    }

    #[must_use]
    pub fn succ(&mut self, pred: TermId) -> TermId {
        self.intern(Term::Succ(pred))
    }

    #[must_use]
    pub fn nat_elim(
        &mut self,
        motive: TermId,
        base: TermId,
        step: TermId,
        scrut: TermId,
    ) -> TermId {
        self.intern(Term::NatElim {
            motive,
            base,
            step,
            scrut,
        })
    }

    #[must_use]
    pub fn v_type(&mut self, dim: TermId, ty0: TermId, ty1: TermId, equiv: TermId) -> TermId {
        self.intern(Term::VType {
            dim,
            ty0,
            ty1,
            equiv,
        })
    }

    #[must_use]
    pub fn v_in(&mut self, dim: TermId, left: TermId, right: TermId) -> TermId {
        self.intern(Term::VIn { dim, left, right })
    }

    #[must_use]
    pub fn v_proj(
        &mut self,
        dim: TermId,
        ty0: TermId,
        ty1: TermId,
        equiv: TermId,
        term: TermId,
    ) -> TermId {
        self.intern(Term::VProj {
            dim,
            ty0,
            ty1,
            equiv,
            term,
        })
    }

    #[must_use]
    pub fn data(&mut self, id: InductiveId, params: Vec<TermId>) -> TermId {
        self.intern(Term::Data { id, params })
    }

    #[must_use]
    pub fn ctor(
        &mut self,
        id: InductiveId,
        ctor: u32,
        params: Vec<TermId>,
        args: Vec<TermId>,
    ) -> TermId {
        self.intern(Term::Ctor {
            id,
            ctor,
            params,
            args,
        })
    }

    #[must_use]
    pub fn data_elim(
        &mut self,
        id: InductiveId,
        params: Vec<TermId>,
        motive: TermId,
        branches: Vec<TermId>,
        scrut: TermId,
    ) -> TermId {
        self.intern(Term::DataElim {
            id,
            params,
            motive,
            branches,
            scrut,
        })
    }

    #[must_use]
    pub fn format_cof(&self, cof: &CofTerm) -> String {
        match cof {
            CofTerm::Top => "⊤".to_owned(),
            CofTerm::Bot => "⊥".to_owned(),
            CofTerm::Eq(lhs, rhs) => {
                format!("({} = {})", self.format_term(*lhs), self.format_term(*rhs))
            }
            CofTerm::And(lhs, rhs) => {
                format!("({} ∧ {})", self.format_cof(lhs), self.format_cof(rhs))
            }
            CofTerm::Or(lhs, rhs) => {
                format!("({} ∨ {})", self.format_cof(lhs), self.format_cof(rhs))
            }
        }
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
            Term::Coe {
                line,
                src,
                dst,
                term,
            } => format!(
                "coe({}, {} -> {}, {})",
                self.format_term(*line),
                self.format_term(*src),
                self.format_term(*dst),
                self.format_term(*term)
            ),
            Term::HCom {
                ty,
                src,
                dst,
                branches,
                cap,
            } => {
                let rendered: Vec<String> = branches
                    .iter()
                    .map(|(cof, tube)| {
                        format!("{} => {}", self.format_cof(cof), self.format_term(*tube))
                    })
                    .collect();
                format!(
                    "hcom({}, {} -> {}, [{}], {})",
                    self.format_term(*ty),
                    self.format_term(*src),
                    self.format_term(*dst),
                    rendered.join(", "),
                    self.format_term(*cap)
                )
            }
            Term::VType { .. } | Term::VIn { .. } | Term::VProj { .. } => self.format_vtype(term),
            other => self.format_inductive(other),
        }
    }

    fn format_vtype(&self, term: &Term) -> String {
        match term {
            Term::VType {
                dim,
                ty0,
                ty1,
                equiv,
            } => format!(
                "V({}, {}, {}, {})",
                self.format_term(*dim),
                self.format_term(*ty0),
                self.format_term(*ty1),
                self.format_term(*equiv)
            ),
            Term::VIn { dim, left, right } => format!(
                "vin({}, {}, {})",
                self.format_term(*dim),
                self.format_term(*left),
                self.format_term(*right)
            ),
            Term::VProj {
                dim,
                ty0,
                ty1,
                equiv,
                term,
            } => format!(
                "vproj({}, {}, {}, {}, {})",
                self.format_term(*dim),
                self.format_term(*ty0),
                self.format_term(*ty1),
                self.format_term(*equiv),
                self.format_term(*term)
            ),
            _ => String::new(),
        }
    }

    fn format_inductive(&self, term: &Term) -> String {
        match term {
            Term::Unit => "Unit".to_owned(),
            Term::Tt => "()".to_owned(),
            Term::UnitElim {
                motive,
                on_unit,
                scrut,
            } => format!(
                "unit_elim({}, {}, {})",
                self.format_term(*motive),
                self.format_term(*on_unit),
                self.format_term(*scrut)
            ),
            Term::Void => "Void".to_owned(),
            Term::VoidElim { motive, scrut } => format!(
                "void_elim({}, {})",
                self.format_term(*motive),
                self.format_term(*scrut)
            ),
            Term::Bool => "Bool".to_owned(),
            Term::True => "true".to_owned(),
            Term::False => "false".to_owned(),
            Term::BoolElim {
                motive,
                on_true,
                on_false,
                scrut,
            } => format!(
                "bool_elim({}, {}, {}, {})",
                self.format_term(*motive),
                self.format_term(*on_true),
                self.format_term(*on_false),
                self.format_term(*scrut)
            ),
            Term::Nat => "Nat".to_owned(),
            Term::Zero => "zero".to_owned(),
            Term::Succ(pred) => format!("succ({})", self.format_term(*pred)),
            Term::NatElim {
                motive,
                base,
                step,
                scrut,
            } => format!(
                "nat_elim({}, {}, {}, {})",
                self.format_term(*motive),
                self.format_term(*base),
                self.format_term(*step),
                self.format_term(*scrut)
            ),
            Term::Data { id, params } => {
                let ps: Vec<String> = params.iter().map(|p| self.format_term(*p)).collect();
                format!("{id}({})", ps.join(", "))
            }
            Term::Ctor {
                id,
                ctor,
                params,
                args,
            } => {
                let ps: Vec<String> = params.iter().map(|p| self.format_term(*p)).collect();
                let as_: Vec<String> = args.iter().map(|a| self.format_term(*a)).collect();
                format!("{id}::c{ctor}[{}]({})", ps.join(", "), as_.join(", "))
            }
            Term::DataElim {
                id,
                motive,
                branches,
                scrut,
                ..
            } => {
                let bs: Vec<String> = branches.iter().map(|b| self.format_term(*b)).collect();
                format!(
                    "data_elim({id}, {}, [{}], {})",
                    self.format_term(*motive),
                    bs.join(", "),
                    self.format_term(*scrut)
                )
            }
            _ => String::new(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{CofTerm, DeBruijnLevel, Index, Term, TermArena, TermId};
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
        let coe = arena.coe(u0, d0, d1, x);
        let cof = CofTerm::Or(
            Box::new(CofTerm::And(
                Box::new(CofTerm::Top),
                Box::new(CofTerm::Eq(d0, d1)),
            )),
            Box::new(CofTerm::Bot),
        );
        let hcom = arena.hcom(u0, d0, d1, vec![(cof, x)], x);

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
        assert_eq!(arena.format_term(coe), "coe(Type 0, 0 -> 1, #0)");
        assert_eq!(
            arena.format_term(hcom),
            "hcom(Type 0, 0 -> 1, [((⊤ ∧ (0 = 1)) ∨ ⊥) => #0], #0)"
        );
        assert_eq!(arena.format_term(TermId(999)), "<invalid:999>");

        let unit = arena.unit();
        let tt = arena.tt();
        let unit_elim = arena.unit_elim(u0, tt, tt);
        let void = arena.void();
        let void_elim = arena.void_elim(u0, x);
        let bool_ty = arena.bool_ty();
        let b_true = arena.bool_true();
        let b_false = arena.bool_false();
        let bool_elim = arena.bool_elim(u0, b_true, b_false, b_true);
        let nat = arena.nat();
        let zero = arena.zero();
        let one = arena.succ(zero);
        let nat_elim = arena.nat_elim(u0, zero, one, one);
        assert_eq!(arena.format_term(unit), "Unit");
        assert_eq!(arena.format_term(tt), "()");
        assert_eq!(arena.format_term(unit_elim), "unit_elim(Type 0, (), ())");
        assert_eq!(arena.format_term(void), "Void");
        assert_eq!(arena.format_term(void_elim), "void_elim(Type 0, #0)");
        assert_eq!(arena.format_term(bool_ty), "Bool");
        assert_eq!(arena.format_term(b_true), "true");
        assert_eq!(arena.format_term(b_false), "false");
        assert_eq!(
            arena.format_term(bool_elim),
            "bool_elim(Type 0, true, false, true)"
        );
        assert_eq!(arena.format_term(nat), "Nat");
        assert_eq!(arena.format_term(zero), "zero");
        assert_eq!(arena.format_term(one), "succ(zero)");
        assert_eq!(
            arena.format_term(nat_elim),
            "nat_elim(Type 0, zero, succ(zero), succ(zero))"
        );
    }
}
