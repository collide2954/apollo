# Apollo

Apollo is an interactive theorem prover and verified systems language in Rust.
Apollo uses Quantitative Cartesian Cubical Type Theory.
Apollo compiles verified programs to clean Rust code with proof erasure.
Apollo supports macOS, Linux, and Windows.

## Design Goals

- **Trusted Kernel**: A small kernel checks proofs with zero external dependencies.
- **Quantitative Cubical Logic**: Multiplicities erase proof terms and track ownership.
- **Built-In Automation**: An internal e-graph and linear arithmetic solver constructs kernel-checked proofs.
- **Fast Proof Search**: Transactional proof states test candidate tactics in memory in parallel.
- **Incremental Builds**: A query database checks only changed modules and definitions.
- **Systems Extraction**: The compiler emits readable Rust code for native targets and WebAssembly.
- **Unified Tooling**: One command-line interface manages projects, checks, formatting, tests, and search.

## Workspace Layout

- `crates/apollo-kernel`: Checks terms, types, multiplicities, and cubical operations.
- `crates/apollo-syntax`: Lexes and parses source files into syntax trees.
- `crates/apollo-elab`: Elaborates surface syntax, unifies terms, and runs tactics.
- `crates/apollo-query`: Manages incremental and parallel compilation queries.
- `crates/apollo-auto`: Runs e-graph congruence and linear arithmetic proof automation.
- `crates/apollo-codegen`: Erases proofs and emits Rust source code.
- `crates/apollo-lsp`: Serves editor and machine-readable proof interfaces.
- `crates/apollo-cli`: Gives the `apollo` binary.
- `crates/apollo-wasm`: Compiles the checker and Rust extractor to WebAssembly with zero unsafe code.
- `xtask`: Runs cross-platform quality checks and documentation checks.

## Usage

Run the typechecker on the example prelude:

```bash
cargo run -p apollo-cli -- check examples/prelude.ap
```

Extract verified `#![no_std]` Rust code from the data type example:

```bash
cargo run -p apollo-cli -- build examples/data.ap
```

You can also build `examples/univalence.ap`, `examples/arithmetic.ap`, and `examples/extractable.ap`.

## Documentation

All project documentation obeys ASD-STE100.
Refer to `docs/glossary.md` for approved Technical Names.

## License

Apollo uses the [Apache License, Version 2.0](LICENSE).
