# Changelog

This file lists all major changes to Apollo.
This project uses Semantic Versioning.

## [Unreleased]

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
