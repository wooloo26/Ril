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

`SourceIndex` borrows all source definitions and syntax nodes without cloning
subtrees. Independent node IDs preserve distinct syntax layers that share a
span. HIR records their declaration, type-binding, default, and expression
scopes. `TypeTemplates` lowers primitive identities, named heads, formal and
mode binders, generic constraints, and callable contracts to references into
these tables. Computations remain explicit requests for static evaluation.
The [checking contract](CHECKING.md) fixes the required roots and recursive
instance proof policy before constraint solving is implemented.

Declaration discovery starts with a recovery-oriented skeleton. The frontend
then follows imports from declaration-aware parses and revisits syntax when
reachable files or resolved heads change. Diagnostics from a committed angle
list stay attached to that list during recovery.

The frontend loads bundled foundational signatures and the `Array`, `Map`,
`Set`, `Numeric`, `String`, and `Bytes` declarations from the compiler's Ril
sources. Ambient module access and explicit `use ril/...` imports share
declaration identities.
The `Reflect::MemberMode` export uses the same declaration as the ambient
`MemberMode` sort.

Collection algorithms and type extractors have Ril bodies. `Set<T>` has one
source-defined opaque identity whose namespace also exports `Set::from`.
The library inventory distinguishes native primitives from source bodies and
records their phase admission by resolved identity. A source-bodied dual-phase
operation still executes its source calls and loops. See the current
[collection contracts](LIBRARY.md); execution validation awaits later stages.

The workspace also defines abstract and native target identities and a
versioned [value and GC-storage layout](LAYOUT.md). Shared scalar helpers
canonicalize IEEE floating values while distinguishing ordinary comparison
from static argument identity. Static checking, compile-time evaluation,
runtime IR, interpretation, the release
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
Successful frontend cases also construct source inputs and resolved type
templates, checking that their syntax, scope, and identity links are complete.
Use `-- Error [EXXXX]` for an expected diagnostic code and
`--~ ERROR [EXXXX]` for a diagnostic at a specific suite line. A
`-- file: PATH hex` block supplies exact bytes.
