use apollo_kernel::{Index, Term, TermArena, TermId};

fn is_add(arena: &TermArena, term: TermId) -> Option<(TermId, TermId)> {
    let Some(Term::NatElim {
        motive,
        base,
        step,
        scrut,
    }) = arena.get(term)
    else {
        return None;
    };
    let step_is_succ_ih = matches!(
        arena.get(*step),
        Some(Term::Succ(inner)) if arena.get(*inner) == Some(&Term::Var(Index(0)))
    );
    (arena.get(*motive) == Some(&Term::Nat) && step_is_succ_ih).then_some((*scrut, *base))
}

fn name_of(names: &[String], index: u32) -> String {
    names
        .len()
        .checked_sub(1 + index as usize)
        .and_then(|pos| names.get(pos))
        .cloned()
        .unwrap_or_else(|| format!("#{index}"))
}

fn rename(text: &str, names: &[String]) -> String {
    let mut out = String::with_capacity(text.len());
    let mut chars = text.chars().peekable();
    while let Some(ch) = chars.next() {
        if ch != '#' {
            out.push(ch);
            continue;
        }
        let mut digits = String::new();
        while let Some(d) = chars.next_if(char::is_ascii_digit) {
            digits.push(d);
        }
        match digits.parse::<u32>() {
            Ok(index) => out.push_str(&name_of(names, index)),
            Err(_) => out.push('#'),
        }
    }
    out
}

#[must_use]
pub fn render(arena: &TermArena, term: TermId, names: &[String]) -> String {
    if let Some((lhs, rhs)) = is_add(arena, term) {
        let right = render(arena, rhs, names);
        let right = if is_add(arena, rhs).is_some() {
            format!("({right})")
        } else {
            right
        };
        return format!("{} + {right}", render(arena, lhs, names));
    }
    match arena.get(term) {
        Some(Term::Succ(pred)) => format!("succ({})", render(arena, *pred, names)),
        Some(Term::App { .. }) => {
            let mut head = term;
            let mut args = Vec::new();
            while let Some(Term::App { func, arg }) = arena.get(head) {
                args.push(render(arena, *arg, names));
                head = *func;
            }
            args.reverse();
            format!("{}({})", render(arena, head, names), args.join(", "))
        }
        _ => rename(&arena.format_term(term), names),
    }
}

#[cfg(test)]
mod tests {
    use apollo_kernel::{Index, TermArena};

    use super::render;
    use crate::add_term;

    #[test]
    fn renders_sums_numerals_applications_and_names() {
        let mut arena = TermArena::new();
        let names = vec!["f".to_owned(), "a".to_owned(), "b".to_owned()];
        let f = arena.var(Index(2));
        let a = arena.var(Index(1));
        let b = arena.var(Index(0));
        let zero = arena.zero();
        let one = arena.succ(zero);
        let b_one = add_term(&mut arena, b, one);
        let sum = add_term(&mut arena, a, b_one);
        assert_eq!(render(&arena, sum, &names), "a + (b + succ(zero))");
        let left = add_term(&mut arena, a, b);
        let left_nested = add_term(&mut arena, left, b);
        assert_eq!(render(&arena, left_nested, &names), "a + b + b");

        let fa = arena.app(f, a);
        let fab = arena.app(fa, b);
        assert_eq!(render(&arena, fab, &names), "f(a, b)");
        let succ_fa = arena.succ(fa);
        assert_eq!(render(&arena, succ_fa, &names), "succ(f(a))");

        let outer = arena.var(Index(5));
        assert_eq!(render(&arena, outer, &names), "#5");
        let pair = arena.pair(a, outer);
        assert_eq!(render(&arena, pair, &names), "(a, #5)");
        let first = arena.fst(b);
        assert_eq!(render(&arena, first, &names), "b.0");

        let nat = arena.nat();
        let v0 = arena.var(Index(0));
        let not_succ = arena.nat_elim(nat, b, v0, a);
        assert!(render(&arena, not_succ, &names).starts_with("nat_elim("));
        let unit = arena.unit();
        let one_again = arena.succ(zero);
        let other_motive = arena.nat_elim(unit, b, one_again, a);
        assert!(render(&arena, other_motive, &names).starts_with("nat_elim("));
        let succ_var1 = arena.var(Index(1));
        let succ_other = arena.succ(succ_var1);
        let wrong_ih = arena.nat_elim(nat, b, succ_other, a);
        assert!(render(&arena, wrong_ih, &names).starts_with("nat_elim("));
    }
}
