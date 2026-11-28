use apollo_kernel::{Index, TermArena, TermId};

#[must_use]
pub const fn version() -> &'static str {
    env!("CARGO_PKG_VERSION")
}

#[must_use]
pub fn add_term(arena: &mut TermArena, lhs: TermId, rhs: TermId) -> TermId {
    let motive = arena.nat();
    let ih = arena.var(Index(0));
    let step = arena.succ(ih);
    arena.nat_elim(motive, rhs, step, lhs)
}

#[cfg(test)]
mod tests {
    use apollo_kernel::{Index, Term, TermArena};

    use super::{add_term, version};

    #[test]
    fn reports_package_version() {
        assert_eq!(version(), env!("CARGO_PKG_VERSION"));
    }

    #[test]
    fn builds_canonical_addition_as_recursion_on_left_operand() {
        let mut arena = TermArena::new();
        let a = arena.var(Index(1));
        let b = arena.var(Index(0));
        let sum = add_term(&mut arena, a, b);
        let nat = arena.nat();
        let ih = arena.var(Index(0));
        let step = arena.succ(ih);
        assert_eq!(
            arena.get(sum),
            Some(&Term::NatElim {
                motive: nat,
                base: b,
                step,
                scrut: a,
            })
        );
    }
}
