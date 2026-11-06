# Ril compiler development

The Rust workspace implements the source frontend. Use the pinned toolchain
with Cargo from the repository root.

```sh
cargo run --locked -- frontend --emit-hir path/to/main.ril
cargo run --locked -- frontend --library path/to/library.ril
cargo run --locked -- frontend path/to/foreign.d.ril
```

A `.ril` input defaults to an executable root. Use `--library` for a library
unit. A `.d.ril` input selects an external declaration unit. Imports resolve
relative to the source file's directory by default. Use `--module-root DIR`
when the entry is below the project root. The command returns 1 for frontend
diagnostics and 2 for invocation, I/O, or resource errors.

The frontend retains the original source, constructs a lossless CST, and
builds HIR with lexical declaration identities. It uses declaration and import
heads to decide whether an expression name takes generic arguments. HIR
retains the selected application signature and defining scopes. The parsed
files retain parameter labels and defaults alongside HIR.

The workspace also defines abstract and native target identities. Static
checking, compile-time evaluation, runtime IR, interpretation, the release
library, and Cranelift code generation are subsequent work. The
[language specification](SPEC.md) defines their behavior and the remaining
frontend conformance scope.

## Verification

```sh
cargo fmt --all --check
cargo clippy --workspace --all-targets --locked -- -D warnings
cargo test --workspace --locked
cargo run --locked -p ril-test
cargo run --locked -p ril-test -- tests/regressions/frontend/angles.ril#close-suffix-rescan
```

The corpus runner extracts each case into its own virtual source tree and
checks `front-pass` and `front-fail` against the same frontend as the driver.
Use `-- Error [EXXXX]` for an expected diagnostic code and
`--~ ERROR [EXXXX]` for a diagnostic at a specific suite line. A
`-- file: PATH hex` block supplies exact bytes.
