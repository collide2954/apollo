# Changelog

This file lists all major changes to Apollo.
This project uses Semantic Versioning.

## [Unreleased]

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
