use std::cmp::Ordering;

use apollo_kernel::{DeBruijnLevel, EvalError, Neutral, TermArena, TermId, Value};

use crate::AutoError;
use crate::lemmas::{NatLemmas, add_val, cong_add, cong_succ, succ_val};
use crate::proof::{Equation, refl, sym, trans};

#[derive(Debug, Clone)]
pub enum Shape {
    Zero,
    Succ(Value),
    Add(Value, Value),
    Atom,
}

#[must_use]
pub fn shape(arena: &TermArena, depth: u32, value: &Value) -> Shape {
    match value {
        Value::Zero => Shape::Zero,
        Value::Succ(pred) => Shape::Succ((**pred).clone()),
        Value::Neutral(neutral) => match &**neutral {
            Neutral::NatElim {
                motive,
                base,
                step,
                scrut,
            } if is_add(arena, depth, motive, step) => {
                Shape::Add(Value::Neutral(scrut.clone()), (**base).clone())
            }
            _ => Shape::Atom,
        },
        _ => Shape::Atom,
    }
}

fn is_add(
    arena: &TermArena,
    depth: u32,
    motive: &apollo_kernel::Closure,
    step: &apollo_kernel::DoubleClosure,
) -> bool {
    let motive_is_nat = matches!(
        motive.apply(arena, Value::var(DeBruijnLevel(depth))),
        Ok(Value::Nat)
    );
    let ih_level = DeBruijnLevel(depth + 1);
    let step_is_succ_ih = matches!(
        step.apply2(arena, Value::var(DeBruijnLevel(depth)), Value::var(ih_level)),
        Ok(Value::Succ(inner))
            if matches!(&*inner, Value::Neutral(n) if matches!(**n, Neutral::Var(l) if l == ih_level))
    );
    motive_is_nat && step_is_succ_ih
}

#[derive(Debug, Clone)]
pub struct Atom {
    pub key: TermId,
    pub value: Value,
}

#[derive(Debug, Clone)]
pub struct NormalForm {
    pub atoms: Vec<Atom>,
    pub constant: u32,
}

pub type AtomRep<'a> =
    &'a mut dyn FnMut(&mut TermArena, &Value) -> Result<(Atom, Equation), AutoError>;

#[derive(Debug, Clone, Copy)]
pub struct Normalizer<'a> {
    pub lemmas: &'a NatLemmas,
    pub depth: u32,
}

fn numeral(constant: u32) -> Value {
    (0..constant).fold(Value::Zero, |acc, _| succ_val(&acc))
}

pub fn canon(arena: &mut TermArena, atoms: &[Atom], constant: u32) -> Result<Value, EvalError> {
    let mut acc = numeral(constant);
    for atom in atoms.iter().rev() {
        acc = add_val(arena, &atom.value, &acc)?;
    }
    Ok(acc)
}

impl Normalizer<'_> {
    #[cfg(test)]
    pub fn plain_atom(
        &self,
        arena: &mut TermArena,
        value: &Value,
    ) -> Result<(Atom, Equation), AutoError> {
        let key = apollo_kernel::nbe::quote(arena, self.depth, value)?;
        let eq = refl(arena, Value::Nat, value.clone())?;
        Ok((
            Atom {
                key,
                value: value.clone(),
            },
            eq,
        ))
    }

    pub fn normalize(
        &self,
        arena: &mut TermArena,
        value: &Value,
        rep: AtomRep<'_>,
    ) -> Result<(NormalForm, Equation), AutoError> {
        match shape(arena, self.depth, value) {
            Shape::Zero => Ok((
                NormalForm {
                    atoms: Vec::new(),
                    constant: 0,
                },
                refl(arena, Value::Nat, Value::Zero)?,
            )),
            Shape::Succ(pred) => {
                let (nf, eq) = self.normalize(arena, &pred, rep)?;
                let lifted = cong_succ(arena, &eq)?;
                let pushed = self.push_succ(arena, &nf.atoms, nf.constant)?;
                Ok((
                    NormalForm {
                        atoms: nf.atoms,
                        constant: nf.constant + 1,
                    },
                    trans(arena, &lifted, &pushed)?,
                ))
            }
            Shape::Add(lhs, rhs) => {
                let (n1, e1) = self.normalize(arena, &lhs, rep)?;
                let (n2, e2) = self.normalize(arena, &rhs, rep)?;
                let both = cong_add(arena, &e1, &e2)?;
                let (nf, merged) = self.merge(arena, &n1, &n2)?;
                Ok((nf, trans(arena, &both, &merged)?))
            }
            Shape::Atom => {
                let (atom, to_rep) = rep(arena, value)?;
                let unit = self.lemmas.zero_r(arena, &atom.value)?;
                let padded = sym(arena, &unit)?;
                Ok((
                    NormalForm {
                        atoms: vec![atom],
                        constant: 0,
                    },
                    trans(arena, &to_rep, &padded)?,
                ))
            }
        }
    }

    fn push_succ(
        &self,
        arena: &mut TermArena,
        atoms: &[Atom],
        constant: u32,
    ) -> Result<Equation, EvalError> {
        let Some((first, rest)) = atoms.split_first() else {
            return refl(arena, Value::Nat, numeral(constant + 1));
        };
        let tail = canon(arena, rest, constant)?;
        let shift = self.lemmas.succ_r(arena, &first.value, &tail)?;
        let inward = sym(arena, &shift)?;
        let inner = self.push_succ(arena, rest, constant)?;
        let keep = refl(arena, Value::Nat, first.value.clone())?;
        let lifted = cong_add(arena, &keep, &inner)?;
        trans(arena, &inward, &lifted)
    }

    fn succ_iter(
        &self,
        arena: &mut TermArena,
        atoms: &[Atom],
        base: u32,
        times: u32,
    ) -> Result<Equation, EvalError> {
        let start = canon(arena, atoms, base)?;
        let mut eq = refl(arena, Value::Nat, start)?;
        for done in 0..times {
            let lifted = cong_succ(arena, &eq)?;
            let pushed = self.push_succ(arena, atoms, base + done)?;
            eq = trans(arena, &lifted, &pushed)?;
        }
        Ok(eq)
    }

    fn merge(
        &self,
        arena: &mut TermArena,
        lhs: &NormalForm,
        rhs: &NormalForm,
    ) -> Result<(NormalForm, Equation), EvalError> {
        let constant = lhs.constant + rhs.constant;
        let Some((first, rest)) = lhs.atoms.split_first() else {
            let eq = self.succ_iter(arena, &rhs.atoms, rhs.constant, lhs.constant)?;
            return Ok((
                NormalForm {
                    atoms: rhs.atoms.clone(),
                    constant,
                },
                eq,
            ));
        };
        let rest_nf = NormalForm {
            atoms: rest.to_vec(),
            constant: lhs.constant,
        };
        let rest_val = canon(arena, rest, lhs.constant)?;
        let rhs_val = canon(arena, &rhs.atoms, rhs.constant)?;
        let regroup = self
            .lemmas
            .assoc(arena, &first.value, &rest_val, &rhs_val)?;
        let (inner_nf, inner) = self.merge(arena, &rest_nf, rhs)?;
        let keep = refl(arena, Value::Nat, first.value.clone())?;
        let lifted = cong_add(arena, &keep, &inner)?;
        let (atoms, placed) = self.insert(arena, first, &inner_nf.atoms, constant)?;
        let step = trans(arena, &regroup, &lifted)?;
        Ok((
            NormalForm { atoms, constant },
            trans(arena, &step, &placed)?,
        ))
    }

    fn insert(
        &self,
        arena: &mut TermArena,
        atom: &Atom,
        sorted: &[Atom],
        constant: u32,
    ) -> Result<(Vec<Atom>, Equation), EvalError> {
        let Some((head, rest)) = sorted.split_first() else {
            return Self::place(arena, atom, sorted, constant);
        };
        match head.key.cmp(&atom.key) {
            Ordering::Less => {
                let tail = canon(arena, rest, constant)?;
                let swap = self
                    .lemmas
                    .left_comm(arena, &atom.value, &head.value, &tail)?;
                let (mut placed, inner) = self.insert(arena, atom, rest, constant)?;
                let keep = refl(arena, Value::Nat, head.value.clone())?;
                let lifted = cong_add(arena, &keep, &inner)?;
                placed.insert(0, head.clone());
                Ok((placed, trans(arena, &swap, &lifted)?))
            }
            Ordering::Equal | Ordering::Greater => Self::place(arena, atom, sorted, constant),
        }
    }

    fn place(
        arena: &mut TermArena,
        atom: &Atom,
        sorted: &[Atom],
        constant: u32,
    ) -> Result<(Vec<Atom>, Equation), EvalError> {
        let mut placed = vec![atom.clone()];
        placed.extend(sorted.iter().cloned());
        let here = canon(arena, &placed, constant)?;
        Ok((placed, refl(arena, Value::Nat, here)?))
    }
}

#[cfg(test)]
mod tests {
    use apollo_kernel::{Ctx, TermArena, TermId, Value};

    use super::{Normalizer, canon};
    use crate::lemmas::{NatLemmas, add_val, succ_val};
    use crate::testing::{kernel_accepts, same};

    fn sum(arena: &mut TermArena, lhs: &Value, rhs: &Value) -> Value {
        add_val(arena, lhs, rhs).unwrap_or(Value::Unit)
    }

    fn normal(
        arena: &mut TermArena,
        ctx: &mut Ctx,
        lemmas: &NatLemmas,
        value: &Value,
    ) -> Option<(Vec<TermId>, u32)> {
        let norm = Normalizer {
            lemmas,
            depth: ctx.depth(),
        };
        let (nf, eq) = norm
            .normalize(arena, value, &mut |a, v| norm.plain_atom(a, v))
            .ok()?;
        let expected = canon(arena, &nf.atoms, nf.constant).ok()?;
        let sound = same(arena, ctx, &eq.lhs, value)
            && same(arena, ctx, &eq.rhs, &expected)
            && kernel_accepts(arena, ctx, &eq);
        sound.then(|| (nf.atoms.iter().map(|a| a.key).collect(), nf.constant))
    }

    #[test]
    fn normalizes_sums_to_sorted_atoms_plus_constant_with_kernel_proofs() {
        let mut arena = TermArena::new();
        let Ok(lemmas) = NatLemmas::build(&mut arena) else {
            return;
        };
        let mut ctx = Ctx::new();
        let first = ctx.push(Value::Nat);
        let second = ctx.push(Value::Nat);
        let third = ctx.push(Value::Nat);

        assert_eq!(
            normal(&mut arena, &mut ctx, &lemmas, &Value::Zero),
            Some((Vec::new(), 0))
        );
        let plus_two = succ_val(&succ_val(&first));
        let nf = normal(&mut arena, &mut ctx, &lemmas, &plus_two);
        assert!(
            nf.as_ref()
                .is_some_and(|(atoms, k)| atoms.len() == 1 && *k == 2)
        );

        let left = sum(&mut arena, &first, &succ_val(&second));
        let right = sum(&mut arena, &third, &first);
        let mixed = sum(&mut arena, &left, &right);
        let nf = normal(&mut arena, &mut ctx, &lemmas, &mixed);
        assert!(nf.as_ref().is_some_and(|(atoms, k)| atoms.len() == 4
            && *k == 1
            && atoms.windows(2).all(|w| w[0].raw() <= w[1].raw())));

        let forward = sum(&mut arena, &first, &second);
        let backward = sum(&mut arena, &second, &first);
        let forward_nf = normal(&mut arena, &mut ctx, &lemmas, &forward);
        let backward_nf = normal(&mut arena, &mut ctx, &lemmas, &backward);
        assert!(forward_nf.is_some() && forward_nf == backward_nf);

        let swapped = sum(&mut arena, &second, &first);
        let nested = sum(&mut arena, &succ_val(&third), &swapped);
        let tail = sum(&mut arena, &second, &third);
        let flat = sum(&mut arena, &first, &succ_val(&tail));
        let nested_nf = normal(&mut arena, &mut ctx, &lemmas, &nested);
        let flat_nf = normal(&mut arena, &mut ctx, &lemmas, &flat);
        assert!(nested_nf.is_some() && nested_nf == flat_nf);
        assert_ne!(forward_nf, nested_nf);

        let one = succ_val(&Value::Zero);
        let two = succ_val(&one);
        let first_two = sum(&mut arena, &first, &two);
        let second_one = sum(&mut arena, &second, &one);
        let stuck_left = sum(&mut arena, &first_two, &second_one);
        let nf = normal(&mut arena, &mut ctx, &lemmas, &stuck_left);
        assert!(
            nf.as_ref()
                .is_some_and(|(atoms, k)| atoms.len() == 2 && *k == 3)
        );
        let three = succ_val(&two);
        let third_three = sum(&mut arena, &third, &three);
        let stuck_more = sum(&mut arena, &third_three, &second_one);
        let nf = normal(&mut arena, &mut ctx, &lemmas, &stuck_more);
        assert!(
            nf.as_ref()
                .is_some_and(|(atoms, k)| atoms.len() == 2 && *k == 4)
        );
    }
}
