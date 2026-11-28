# Changelog

This file lists all major changes to Apollo.
This project uses Semantic Versioning.

## [Unreleased]

## [0.10.0] - 2026-11-27

### Added

- Add Cartesian V-types (`V`, `vin`, `vproj`) and computational univalence coercion rules in `apollo-kernel`.
- Add `V`, `vin`, and `vproj` surface syntax and elaboration in `apollo-syntax` and `apollo-elab`.
- Add univalence normalization and proof erasure in `apollo-codegen`, `examples/univalence.ap`, and the browser playground.

## [0.9.0] - 2026-11-27

### Added

- Add `apollo-wasm` crate for `wasm32-wasip1` proof checking and Rust extraction with zero external dependencies and zero `unsafe` code.
- Add the interactive browser playground, WASI preview 1 runner, preset examples, and share links to the Apollo website.
- Update GitHub Pages deployment to compile `apollo-wasm.wasm` automatically.

### Changed

- Close all user-defined ADT mutation test gaps across `apollo-syntax`, `apollo-kernel`, `apollo-elab`, and `apollo-codegen`.

## [0.8.0] - 2026-11-27

### Added

- Add user-defined inductive data types, strict positivity checks, and recursive eliminators in `apollo-kernel`.
- Add `enum` and `struct` declarations, constructor paths, struct literals, and field projections in `apollo-syntax` and `apollo-elab`.
- Add `pub enum` and `pub struct` Rust extraction with conditional `alloc::boxed::Box` recursion and erased proof fields in `apollo-codegen`.
- Add `examples/data.ap` with `Option`, `Point`, `VerifiedNat`, `List`, and `Tree` proofs and live Rust execution tests.

## [0.7.0] - 2026-11-27

### Added

- Add `Unit`, `Void`, `Bool`, and `Nat` inductive types, eliminators, and Kan rules in `apollo-kernel`.
- Add branch-aware QTT usage joins and inductive `Path` proof checking in `apollo-kernel`.
- Add `match` expressions, dependent motives, and inductive literals in `apollo-syntax` and `apollo-elab`.
- Add `Unit`, `Void`, `Bool`, and `Nat` extraction to `()`, `Infallible`, `bool`, and `u128` loops in `apollo-codegen`.
- Add `examples/arithmetic.ap` with verified arithmetic proofs and live Rust execution tests.

## [0.6.0] - 2026-11-27

### Added

- Add proof-erasing `#![no_std]` Rust code generation with automatic `Clone` inference and last-use moves in `apollo-codegen`.
- Add refinement erasure for erased `Sigma` pairs, `impl FnOnce` and `impl Fn` extraction, and Rust keyword escaping.
- Add the `apollo build <file.ap> [-o <out.rs>]` command and `examples/extractable.ap` verified by `rustc -D warnings`.

### Changed

- Expose declaration kind and parameter names on `CheckedDecl` in `apollo-elab`.
- Split GitHub Pages deployment into separate build and deploy jobs.

## [0.5.0] - 2026-11-26

### Added

- Add source spans, lexer, AST, and parser for `.ap` modules in `apollo-syntax`.
- Add surface-to-kernel elaboration with name resolution and line/column diagnostics in `apollo-elab`.
- Add the `apollo check <file.ap>` command and `examples/prelude.ap` with kernel-checked proofs.

### Changed

- Add mutation test coverage for `coe`, `hcom`, and cofibration checks in `apollo-kernel`.

## [0.4.0] - 2026-11-26

### Added

- Add Cartesian coercion (`coe`) with Kan computation rules for universes, Pi types, and Sigma types.
- Add Cartesian homogeneous composition (`hcom`) with cofibration terms, cap checks, and pairwise branch overlap checks.
- Add kernel proofs for `transport`, `subst`, `transport_refl`, path symmetry (`sym`), and path transitivity (`trans`).

## [0.3.0] - 2026-11-26

### Added

- Add the static Apollo website and GitHub Pages deployment workflow.
- Add Cartesian cubical interval dimensions, cofibrations, and face entailment to `apollo-kernel`.
- Add cubical path types, path lambdas, path application, and endpoint boundary checking to `apollo-kernel`.

## [0.2.1] - 2026-11-26

### Changed

- Replace index loops in `Level::max` and `Level::leq` with slice operations and binary search.
- Add nested binder conversion, subtyping, and erased type-level projection tests in `apollo-kernel`.

## [0.2.0] - 2026-11-26

### Added

- Add canonical universe level algebra with exact decision checks for equality and cumulativity.
- Add a hash-consed term arena with De Bruijn indices and structural sharing.
- Add a thread-safe Normalization by Evaluation engine with eta-equivalence and cumulative subtyping.
- Add a bidirectional QTT typechecker for universes, Pi types, and Sigma types.

## [0.1.1] - 2026-11-26

### Added

- Add repository metadata to all workspace crate manifests.
- Add an integration test for the `apollo` binary.
- Add `CHANGELOG.md` for release tracking.

### Changed

- Update GitHub Actions workflows to use `actions/checkout@v7`.
- Add non-empty check coverage for `UsageVec::is_empty`.

## [0.1.0] - 2026-11-26

### Added

- Create the eight-crate Cargo workspace and `xtask` runner.
- Add the ASD-STE100 documentation checker and Technical Names glossary.
- Add cross-platform GitHub Actions workflows, `cargo-deny`, `cargo-machete`, Miri, and `cargo-mutants`.
- Add the QTT `Multiplicity` rig and `UsageVec` to `apollo-kernel`.
