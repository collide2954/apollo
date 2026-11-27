# Kernel Design

This document describes the architecture of `apollo-kernel`.
The kernel has zero external crate dependencies and forbids `unsafe` Rust code.

## Core Type Theory

Apollo uses Quantitative Cartesian Cubical Type Theory.
The kernel combines three layers into one small checking engine.

- **Quantitative Layer**: Every binder carries a `Multiplicity` from the rig `{Zero, One, Many}`.
- **Universe Layer**: Predicative cumulative Russell-style universes (`Type u`) use algebraic universe levels (`0`, `succ`, `max`, level variables).
- **Cubical Layer**: Interval endpoints, dimension variables, cofibrations, path types, Kan operations (`coe`, `hcom`), V-types, and Higher Inductive Types give native univalence.

## Multiplicity Rig

The kernel checks types, universe levels, interval dimensions, and cubical paths at `Zero` multiplicity.
`Zero`-multiplicity terms erase completely before Rust code generation.
`One`-multiplicity binders enforce linear usage for owned resources.
`Many`-multiplicity binders mark unrestricted runtime values.

The rig defines addition (`+`), multiplication (`*`), and a sub-usage partial order (`<=`).
`Zero` is the additive identity and multiplicative annihilator.
`One` is the multiplicative identity.
`Many` absorbs addition with `One` or `Many`.

## Term Representation

The kernel stores syntax terms in an arena with hash-consed `TermId` handles.
Syntax terms use De Bruijn indices for bound variables.
Normalization by Evaluation uses De Bruijn levels in semantic values.
Hash-consing gives constant-time structural equality checks on identical subterms.

## Vertical Slices

The kernel grows in five tested vertical slices.

1. Build the QTT multiplicity rig and universe level algebra.
2. Build the term arena, Normalization by Evaluation, and `Pi`/`Sigma`/`Type` checking.
3. Build the cubical interval, cofibrations, and path types.
4. Build Kan operations (`coe`, `hcom`) and V-types for univalence.
5. Build inductive families and Higher Inductive Types.
