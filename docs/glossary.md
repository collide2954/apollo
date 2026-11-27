# Technical Names Glossary

This document lists approved Technical Names for Apollo documentation under ASD-STE100.
Use these exact terms consistently in all documentation files.

## Core Concepts

- **Apollo**: The interactive theorem prover and verified systems language in this repository.
- **ASD-STE100**: The Simplified Technical English specification for aerospace and technical documentation.
- **Cartesian Cubical Type Theory**: A cubical type theory with interval diagonals, homogeneous composition, and coercion.
- **Quantitative Type Theory**: A dependent type theory that assigns usage multiplicities to variables.
- **Multiplicity**: A usage annotation on a binder (`0` for erased, `1` for linear, `omega` for unrestricted).
- **Higher Inductive Type**: An inductive type with both point constructors and path constructors.
- **Normalization by Evaluation**: A method that reduces terms through a semantic domain to normal forms.
- **Proof Erasure**: The removal of `0`-multiplicity proof terms before code generation.
- **Proof Artifact**: A content-addressed `.aplc` file that the kernel checks independently.
- **Transactional Proof State**: An immutable in-memory proof state that supports parallel speculative branching.
- **e-graph**: A data structure that stores equivalence classes of terms for equality saturation.

## Architecture Terms

- **Kernel**: The trusted core in `apollo-kernel` that validates all proofs.
- **Elaborator**: The component in `apollo-elab` that converts surface syntax into core terms.
- **Query Database**: The incremental computation engine in `apollo-query`.
- **Workspace**: The Cargo multi-crate project structure for Apollo.
- **Crate**: A single Rust library or binary package in the workspace.
- **xtask**: The Rust automation package that runs local quality checks.
- **WebAssembly**: The portable binary instruction format targeted through Rust or direct code generation.
