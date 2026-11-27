use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DimVar(pub u32);

impl fmt::Display for DimVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "i{}", self.0)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Dim {
    Zero,
    One,
    Var(DimVar),
}

impl Dim {
    #[must_use]
    pub const fn is_zero(self) -> bool {
        matches!(self, Self::Zero)
    }

    #[must_use]
    pub const fn is_one(self) -> bool {
        matches!(self, Self::One)
    }

    #[must_use]
    pub const fn is_endpoint(self) -> bool {
        matches!(self, Self::Zero | Self::One)
    }

    #[must_use]
    pub const fn subst(self, target: DimVar, replacement: Self) -> Self {
        match self {
            Self::Var(var) if var.0 == target.0 => replacement,
            other => other,
        }
    }
}

impl fmt::Display for Dim {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Zero => f.write_str("0"),
            Self::One => f.write_str("1"),
            Self::Var(var) => write!(f, "{var}"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Cof {
    Top,
    Bot,
    Eq(Dim, Dim),
    And(Box<Self>, Box<Self>),
    Or(Box<Self>, Box<Self>),
}

impl Cof {
    #[must_use]
    pub fn eq(lhs: Dim, rhs: Dim) -> Self {
        match lhs.cmp(&rhs) {
            Ordering::Equal => Self::Top,
            Ordering::Less | Ordering::Greater if lhs.is_endpoint() && rhs.is_endpoint() => {
                Self::Bot
            }
            Ordering::Less => Self::Eq(lhs, rhs),
            Ordering::Greater => Self::Eq(rhs, lhs),
        }
    }

    #[must_use]
    pub fn and(lhs: Self, rhs: Self) -> Self {
        match (lhs, rhs) {
            (Self::Bot, _) | (_, Self::Bot) => Self::Bot,
            (Self::Top, other) | (other, Self::Top) => other,
            (left, right) if left == right => left,
            (left, right) => Self::And(Box::new(left), Box::new(right)),
        }
    }

    #[must_use]
    pub fn or(lhs: Self, rhs: Self) -> Self {
        match (lhs, rhs) {
            (Self::Top, _) | (_, Self::Top) => Self::Top,
            (Self::Bot, other) | (other, Self::Bot) => other,
            (left, right) if left == right => left,
            (left, right) => Self::Or(Box::new(left), Box::new(right)),
        }
    }

    #[must_use]
    pub fn boundary(dim: Dim) -> Self {
        Self::or(Self::eq(dim, Dim::Zero), Self::eq(dim, Dim::One))
    }

    #[must_use]
    pub fn subst(&self, target: DimVar, replacement: Dim) -> Self {
        match self {
            Self::Top => Self::Top,
            Self::Bot => Self::Bot,
            Self::Eq(lhs, rhs) => Self::eq(
                lhs.subst(target, replacement),
                rhs.subst(target, replacement),
            ),
            Self::And(lhs, rhs) => Self::and(
                lhs.subst(target, replacement),
                rhs.subst(target, replacement),
            ),
            Self::Or(lhs, rhs) => Self::or(
                lhs.subst(target, replacement),
                rhs.subst(target, replacement),
            ),
        }
    }

    #[must_use]
    pub fn faces(&self) -> Vec<Face> {
        let mut results = Vec::new();
        collect_faces(self, Face::new(), &mut results);
        results
    }

    #[must_use]
    pub fn is_consistent(&self) -> bool {
        !self.faces().is_empty()
    }

    #[must_use]
    pub fn entails(&self, conclusion: &Self) -> bool {
        self.faces().iter().all(|face| face.satisfies(conclusion))
    }

    #[must_use]
    pub fn equivalent(&self, other: &Self) -> bool {
        self.entails(other) && other.entails(self)
    }
}

impl fmt::Display for Cof {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Top => f.write_str("⊤"),
            Self::Bot => f.write_str("⊥"),
            Self::Eq(lhs, rhs) => write!(f, "({lhs} = {rhs})"),
            Self::And(lhs, rhs) => write!(f, "({lhs} ∧ {rhs})"),
            Self::Or(lhs, rhs) => write!(f, "({lhs} ∨ {rhs})"),
        }
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Face {
    parent: BTreeMap<Dim, Dim>,
}

impl Face {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            parent: BTreeMap::new(),
        }
    }

    #[must_use]
    pub fn canonical_dim(&self, mut dim: Dim) -> Dim {
        while let Some(&next) = self.parent.get(&dim) {
            if next == dim {
                break;
            }
            dim = next;
        }
        dim
    }

    #[must_use]
    pub fn equiv(&self, lhs: Dim, rhs: Dim) -> bool {
        self.canonical_dim(lhs) == self.canonical_dim(rhs)
    }

    #[must_use]
    pub fn equate(&self, lhs: Dim, rhs: Dim) -> Option<Self> {
        let r_lhs = self.canonical_dim(lhs);
        let r_rhs = self.canonical_dim(rhs);
        let (root, child) = match r_lhs.cmp(&r_rhs) {
            Ordering::Equal => return Some(self.clone()),
            Ordering::Less | Ordering::Greater if r_lhs.is_endpoint() && r_rhs.is_endpoint() => {
                return None;
            }
            Ordering::Less => (r_lhs, r_rhs),
            Ordering::Greater => (r_rhs, r_lhs),
        };
        let mut next = self.clone();
        next.parent.insert(child, root);
        Some(next)
    }

    #[must_use]
    pub fn satisfies(&self, cof: &Cof) -> bool {
        match cof {
            Cof::Top => true,
            Cof::Bot => false,
            Cof::Eq(lhs, rhs) => self.equiv(*lhs, *rhs),
            Cof::And(lhs, rhs) => self.satisfies(lhs) && self.satisfies(rhs),
            Cof::Or(lhs, rhs) => self.satisfies(lhs) || self.satisfies(rhs),
        }
    }
}

fn collect_faces(cof: &Cof, current: Face, out: &mut Vec<Face>) {
    match cof {
        Cof::Top => out.push(current),
        Cof::Bot => {}
        Cof::Eq(lhs, rhs) => {
            if let Some(next) = current.equate(*lhs, *rhs) {
                out.push(next);
            }
        }
        Cof::And(lhs, rhs) => {
            let mut left_faces = Vec::new();
            collect_faces(lhs, current, &mut left_faces);
            for face in left_faces {
                collect_faces(rhs, face, out);
            }
        }
        Cof::Or(lhs, rhs) => {
            collect_faces(lhs, current.clone(), out);
            collect_faces(rhs, current, out);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Cof, Dim, DimVar, Face};

    #[test]
    fn dim_predicates_substitution_and_formatting() {
        let i0 = Dim::Var(DimVar(0));
        let i1 = Dim::Var(DimVar(1));

        assert!(Dim::Zero.is_zero());
        assert!(!Dim::Zero.is_one());
        assert!(Dim::Zero.is_endpoint());

        assert!(Dim::One.is_one());
        assert!(!Dim::One.is_zero());
        assert!(Dim::One.is_endpoint());

        assert!(!i0.is_zero());
        assert!(!i0.is_one());
        assert!(!i0.is_endpoint());

        assert_eq!(i0.subst(DimVar(0), Dim::One), Dim::One);
        assert_eq!(i1.subst(DimVar(0), Dim::One), i1);
        assert_eq!(Dim::Zero.subst(DimVar(0), Dim::One), Dim::Zero);

        assert_eq!(Dim::Zero.to_string(), "0");
        assert_eq!(Dim::One.to_string(), "1");
        assert_eq!(i0.to_string(), "i0");
        assert_eq!(DimVar(2).to_string(), "i2");
    }

    #[test]
    fn cof_smart_constructors_and_boundary_simplify() {
        let i0 = Dim::Var(DimVar(0));
        let i1 = Dim::Var(DimVar(1));

        assert_eq!(Cof::eq(i0, i0), Cof::Top);
        assert_eq!(Cof::eq(Dim::Zero, Dim::One), Cof::Bot);
        assert_eq!(Cof::eq(Dim::One, Dim::Zero), Cof::Bot);
        assert_eq!(Cof::eq(i1, i0), Cof::Eq(i0, i1));
        assert_eq!(Cof::eq(i0, Dim::Zero), Cof::Eq(Dim::Zero, i0));

        assert_eq!(Cof::boundary(Dim::Zero), Cof::Top);
        assert_eq!(Cof::boundary(Dim::One), Cof::Top);
        let bd = Cof::boundary(i0);
        assert_eq!(bd.to_string(), "((0 = i0) ∨ (1 = i0))");

        assert_eq!(Cof::and(Cof::Bot, bd.clone()), Cof::Bot);
        assert_eq!(Cof::and(bd.clone(), Cof::Bot), Cof::Bot);
        assert_eq!(Cof::and(Cof::Top, bd.clone()), bd);
        assert_eq!(Cof::and(bd.clone(), Cof::Top), bd);
        assert_eq!(Cof::and(bd.clone(), bd.clone()), bd);

        assert_eq!(Cof::or(Cof::Top, bd.clone()), Cof::Top);
        assert_eq!(Cof::or(bd.clone(), Cof::Top), Cof::Top);
        assert_eq!(Cof::or(Cof::Bot, bd.clone()), bd);
        assert_eq!(Cof::or(bd.clone(), Cof::Bot), bd);
        assert_eq!(Cof::or(bd.clone(), bd.clone()), bd);

        assert_eq!(Cof::Top.to_string(), "⊤");
        assert_eq!(Cof::Bot.to_string(), "⊥");
        assert_eq!(
            Cof::and(Cof::eq(i0, Dim::Zero), Cof::eq(i1, Dim::One)).to_string(),
            "((0 = i0) ∧ (1 = i1))"
        );
    }

    #[test]
    fn cof_substitution_simplifies_formulas() {
        let i0 = Dim::Var(DimVar(0));
        let i1 = Dim::Var(DimVar(1));
        let diag = Cof::eq(i0, i1);
        let both = Cof::and(diag, Cof::eq(i1, Dim::Zero));

        assert_eq!(Cof::Top.subst(DimVar(0), Dim::Zero), Cof::Top);
        assert_eq!(Cof::Bot.subst(DimVar(0), Dim::Zero), Cof::Bot);
        assert_eq!(both.subst(DimVar(0), Dim::Zero), Cof::eq(i1, Dim::Zero));
        assert!(!both.subst(DimVar(0), Dim::One).is_consistent());

        let bd = Cof::boundary(i0);
        assert_eq!(bd.subst(DimVar(0), Dim::Zero), Cof::Top);
        assert_eq!(bd.subst(DimVar(0), Dim::One), Cof::Top);
        assert_eq!(bd.subst(DimVar(1), Dim::Zero), bd);
    }

    #[test]
    fn face_and_cofibration_entailment_decides_cartesian_cube_logic() {
        let i0 = Dim::Var(DimVar(0));
        let i1 = Dim::Var(DimVar(1));
        let i2 = Dim::Var(DimVar(2));

        assert!(Cof::Top.is_consistent());
        assert!(!Cof::Bot.is_consistent());
        assert!(Cof::Bot.entails(&Cof::eq(i0, Dim::Zero)));
        assert!(!Cof::Top.entails(&Cof::Bot));
        assert!(!Cof::Top.entails(&Cof::boundary(i0)));

        let trans = Cof::and(Cof::eq(i0, i1), Cof::eq(i1, i2));
        assert!(trans.entails(&Cof::eq(i0, i2)));
        assert!(!trans.entails(&Cof::eq(i0, Dim::Zero)));

        let chain_contradiction = Cof::and(
            Cof::and(Cof::eq(i0, Dim::Zero), Cof::eq(i0, i1)),
            Cof::eq(i1, Dim::One),
        );
        assert!(!chain_contradiction.is_consistent());
        assert!(chain_contradiction.entails(&Cof::Bot));

        let corners_on_diag = Cof::or(
            Cof::and(Cof::eq(i0, Dim::Zero), Cof::eq(i1, Dim::Zero)),
            Cof::and(Cof::eq(i0, Dim::One), Cof::eq(i1, Dim::One)),
        );
        assert!(corners_on_diag.entails(&Cof::eq(i0, i1)));
        assert!(!Cof::eq(i0, i1).entails(&corners_on_diag));

        let lhs = Cof::and(
            Cof::eq(i0, i1),
            Cof::or(Cof::eq(i1, Dim::Zero), Cof::eq(i1, Dim::One)),
        );
        let rhs = Cof::or(
            Cof::and(Cof::eq(i0, i1), Cof::eq(i1, Dim::Zero)),
            Cof::and(Cof::eq(i0, i1), Cof::eq(i1, Dim::One)),
        );
        assert!(lhs.equivalent(&rhs));
        assert!(lhs.entails(&Cof::boundary(i0)));
        assert!(!lhs.equivalent(&Cof::boundary(i0)));

        let face = Face::new()
            .equate(i1, i0)
            .and_then(|f| f.equate(i0, Dim::Zero));
        assert!(face.is_some());
        if let Some(f) = face {
            assert_eq!(f.canonical_dim(i1), Dim::Zero);
            assert!(f.equiv(i1, Dim::Zero));
            assert!(f.satisfies(&Cof::and(Cof::eq(i0, i1), Cof::boundary(i1))));
            assert!(!f.satisfies(&Cof::and(Cof::eq(i0, i1), Cof::eq(i1, Dim::One))));
            assert_eq!(f.equate(i1, Dim::One), None);
            assert_eq!(f.equate(i1, i0), Some(f));
        }
    }
}
