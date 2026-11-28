# Proof Automation

This document describes the `auto` tactic and the `apollo-auto` crate.
The tactic finds proof terms for `Path` goals.
The kernel checks each proof term again before Apollo accepts it.
A defect in `apollo-auto` cannot make the kernel accept a false theorem.

## Usage

Write `auto` where Apollo knows the expected `Path` type.

```apollo
theorem add_comm(0 a: Nat, 0 b: Nat) -> Path(_ => Nat, a + b, b + a) {
    auto
}
```

You can use `auto` as a full theorem body, a `match` arm, or the second part of a `Sigma` pair.
The goal family must not depend on the dimension variable.

## Natural Number Addition

The `+` operator adds two `Nat` values.
The elaborator turns `a + b` into one canonical `nat_elim` term with recursion on `a`.
The kernel computes `zero + b` to `b` and `succ(a) + b` to `succ(a + b)`.
The `+` operator needs no new kernel rule.

## Decision Procedure

The tactic works in two phases.

1. Congruence closure puts the goal sides and the sides of each `Path` hypothesis into an e-graph.
2. Linear normalization rewrites each `Nat` sum to sorted atoms plus a constant.

The e-graph merges two nodes when a hypothesis or a congruence step makes them equal.
Each merge records its reason in a proof forest.
The explanation step reads the proof forest and builds a proof term from `refl`, `sym`, `trans`, and congruence.

The normalizer uses five closed lemmas.
The tactic builds each lemma by induction and the kernel checks each lemma.

- `x + zero = x`
- `x + succ(y) = succ(x + y)`
- `(x + y) + z = x + (y + z)`
- `x + y = y + x`
- `x + (y + z) = y + (x + z)`

The normalizer takes atoms modulo the congruence classes from phase 1.
Thus a hypothesis `a = b` lets `a + c` and `c + b` get the same normal form.

## Limits

The tactic proves equalities.
It does not prove inequalities or goals that need induction.
It does not cancel terms across hypotheses.
For example, it cannot prove `a = b` from `a + c = b + c`.

## Error Reports

If the tactic cannot find a proof, Apollo shows both goal sides and both normal forms.

```text
auto could not prove a + b = succ(a); normal forms are a + (b + zero) and a + succ(zero)
```
