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

HIR records compilation-unit origins, the executable entry definition, and
foreign declaration kinds. It also assigns finite identities to written `via`
inputs and schema coordinates. Nested callable patterns have separate owners;
named references retain their declaration identity without expanding recursive
schemas. Member modes retain independent slot and access components and their
source spans. Concrete reception and storage-instance constraints belong to
the checking stage.

Declaration discovery starts with a recovery-oriented skeleton. The frontend
then follows imports from declaration-aware parses and revisits syntax when
reachable files or resolved heads change. Diagnostics from a committed angle
list stay attached to that list during recovery.

The frontend loads bundled foundational signatures and the `Numeric`,
`String`, and `Bytes` declarations from the compiler's Ril sources. Ambient
module access and explicit `use ril/...` imports share declaration identities.
The `Reflect::MemberMode` export uses the same declaration as the ambient
`MemberMode` sort.

The workspace also defines abstract and native target identities. Static
checking, compile-time evaluation, runtime IR, interpretation, the release
library, and Cranelift code generation are subsequent work. The
[language specification](SPEC.md) defines their behavior and the remaining
frontend conformance scope.

## Git commit messages

Activate the repository hook after cloning.

```sh
git config --local core.hooksPath .githooks
```

Start commit messages with an uppercase ASCII letter and omit `:` throughout
the subject and body. For example, use `Fix generic argument parsing`.

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
