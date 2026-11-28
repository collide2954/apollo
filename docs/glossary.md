# Technical Names Glossary

This document lists approved Technical Names for Apollo documentation under ASD-STE100.
Use these exact terms consistently in all documentation files.

## Core Concepts

- **Apollo**: The interactive theorem prover and verified systems language in this repository.
- **ASD-STE100**: The Simplified Technical English specification for aerospace and technical documentation.
- **Cartesian Cubical Type Theory**: A cubical type theory with interval diagonals, homogeneous composition, and coercion.
- **Quantitative Type Theory**: A dependent type theory that assigns usage multiplicities to variables.
- **Multiplicity**: A usage annotation on a binder (`Zero` for erased, `One` for linear, `Many` for unrestricted).
- **Rig**: A semiring without additive inverses that governs multiplicity addition and multiplication.
- **Universe Level**: An algebraic level expression built from zero, successor, maximum, and level variables.
- **De Bruijn Index**: A zero-based distance from a bound variable to its enclosing binder in syntax.
- **De Bruijn Level**: A zero-based position of a variable from the root of a semantic context.
- **Cofibration**: A decidable face constraint on cubical interval terms such as endpoint equality.
- **Kan Operation**: A cubical coercion (`coe`) or homogeneous composition (`hcom`) primitive.
- **V-Type**: A cubical glue type that witnesses univalence computationally.
- **Higher Inductive Type**: An inductive type with both point constructors and path constructors.
- **Normalization by Evaluation**: A method that reduces terms through a semantic domain to normal forms.
- **Proof Erasure**: The removal of `Zero`-multiplicity proof terms before code generation.
- **Proof Artifact**: A content-addressed `.aplc` file that the kernel checks independently.
- **Transactional Proof State**: An immutable in-memory proof state that supports parallel speculative branching.
- **e-graph**: A data structure that stores equivalence classes of terms for equality saturation.
- **Congruence Closure**: A procedure that merges two applications when their heads and arguments have equal classes.
- **Proof Forest**: A record of the reason for each e-graph merge that lets a tactic rebuild a proof term.
- **Normal Form**: A sorted sum of atoms plus a constant that the `auto` tactic gives to each `Nat` sum.
- **Tactic**: A procedure in the elaborator that builds a proof term for a goal.

## Architecture Terms

- **Kernel**: The trusted core in `apollo-kernel` that validates all proofs.
- **Elaborator**: The component in `apollo-elab` that converts surface syntax into core terms.
- **Query Database**: The incremental computation engine in `apollo-query`.
- **Workspace**: The Cargo multi-crate project structure for Apollo.
- **Crate**: A single Rust library or binary package in the workspace.
- **xtask**: The Rust automation package that runs local quality checks.
- **WebAssembly**: The portable binary instruction format targeted through Rust or direct code generation.
