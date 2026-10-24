# Ril development

[README.md](README.md) introduces the language. [SPEC](doc/SPEC.md) and
[STD](doc/STD.md) define its rules. [AXIOMS.md](AXIOMS.md) defines the semantic
kernel invariants; [AGENTS.md](AGENTS.md) lists the project structure.

Native compilation and execution are implemented. Semantic integration and
the kernel migration remain incomplete, with failing tests and unimplemented
corpus cases. A successful build or focused check does not certify conformance.

## Build and run

Use the toolchain and components pinned in `rust-toolchain.toml`. Windows needs
the MSVC x64 linker and SDK; Linux needs the GNU x64 toolchain.
Install cargo-nextest for `cargo xtask ci`.

```text
cargo build --locked -p ril-cli -p ril-runtime
cargo run --locked -p ril-cli -- targets --json
cargo run --locked -p ril-cli -- check example.ril --explain
cargo run --locked -p ril-cli -- build example.ril --unit executable --output example
cargo run --locked -p ril-cli -- test example.ril --entry test_example
```

Check mode supports `--target pointer32` and `--target pointer64`. Native targets
are `x86_64-pc-windows-msvc` and `x86_64-unknown-linux-gnu`. Static computation uses
the selected layout. `--static-budget` overrides the language-event budget.

The CLI normally finds `ril_runtime.lib` or `libril_runtime.a` beside itself.
Override this with `--runtime-library PATH` or `RIL_RUNTIME_LIBRARY`.
Compiler and runtime must use the same runtime ABI version.

## Verification

A fresh checkout needs no saved reports, source copies or prebuilt compiler.

```text
cargo fmt --all -- --check
cargo check --locked --workspace --all-targets
cargo clippy --locked --workspace --all-targets -- -D warnings
cargo test --locked -p ril-test
cargo test --locked -p ril-compiler -p ril-syntax --no-fail-fast
cargo xtask corpus validate
cargo xtask corpus run --applicable-only
cargo xtask ci
```

`corpus validate` checks structure and specification references. `corpus run`
checks or builds and executes programs through the CLI. Use `--case CASE_ID` or
`--filter TEXT` for selection, `--compiler PATH` for a specific compiler, and
`--timeout-ms` to bound each case. Empty selection, timeout, crash, unsupported
environments and unimplemented stages never count as passes.

Full acceptance requires Windows MSVC and Linux GNU, both pointer layouts for
static semantics, and the applicable native corpus. Run the expensive ignored
concrete-graph oracle explicitly with bounded time and memory.

## Tests

Fixed Ril programs belong in `tests/`, grouped by behavior. Keep bundle paths
and case IDs stable, link positive and negative controls with `companion`, and
use existing SPEC/STD anchors. Each case has an independent compilation state.
Align signature and body `where` clauses with their function's `fn`; indent
helper declarations one level below `where`.

Modes are `check-pass`, `check-fail`, `run-pass`, `run-panic` and `run-program`.
Run-pass/run-panic select a public zero-argument `test_*` function. Run-program
specifies exit/output expectations and any arguments, environment or helpers.

Shared inputs use `--@ source` and `--@ use-source`. Virtual files may contain
Ril, declarations, helper code or binary data. Preserve exact bytes with hex
blocks or `no-final-newline` where required; existing bundles show the format.

Rust HIR, Core and fact-mutation tests load programs through `ril_test::case_source`,
`case_bytes` or `case_by_id`. Avoid duplicate fixed programs in Rust strings.
Pure Rust models, generated cases and invalid-byte inputs remain Rust tests.

## Development workflow

- Follow SPEC/STD for behavior and AXIOMS for implementation. Add positive and
  negative regressions, update affected IR/runtime consumers, and remove the
  superseded implementation in the same change.
- Semantic analysis is trusted compiler code. Check every required language rule
  and validate IR structure; do not require an independent certificate/replay
  engine. Missing required information or exhausted work cannot authorize behavior.
  Incomplete analysis remains inspectable without authorizing compilation.
- Run focused checks, then the relevant full matrix. Report the scope and any
  remaining failures. Preserve case identity, expectations and execution coverage.
- Keep source explanations beside the implementation. Commits use one descriptive
  line, without a type/scope prefix or body.

Use one Cargo target directory per host. Set `CARGO_INCREMENTAL=0` to limit
artifact growth and use `-j2` on constrained machines. Keep binaries used by an
active frozen native batch unchanged until it finishes, then delete the copies.
`target/` and `.local/` are disposable and must not supply build or test inputs.
Preserve unfinished work in Git and current gaps below; avoid unregistered drafts,
duplicate source trees and historical verification reports.

## Current work

- Semantic acceptance now belongs to the analyzer and the owned type arena's
  completion checks. The independent fact/certificate replay engines and their
  Core/native proof copies have been removed. Finish replacing remaining ingress
  witnesses and capture-time reconstruction with the common typed operations.
- Unify complete types and constraints with resolved declaration/binder identities.
  Replace erased `Ty`, syntax witnesses and repeated environment reconstruction.
  Callable interfaces retain their lexical type interpretation; signature probes
  and return contracts retain complete type graphs. Effect inputs and resume
  operands share the receiving operation. Factories retain lexical handler
  dependencies separately from invocation answer constraints. Finish routing
  generics, defaults, rows and constructors through the same typed operations.
- Complete control-flow analysis for heap access, borrowing, effects, duties,
  resources and channels. Replace unresolved generated callback inputs, retain
  actual protected answers across resume, and use finite loop/recursion summaries.
  Carry normal and abrupt result types directly, replacing block-exit/cause
  replay. Preserve conditional/rest-pattern receiving and correlated aggregates.
- Run static execution on the eligible elaborated operations used by compilation.
  Finish Const/Key argument and extent inference, selected numeric representation,
  and first-class explicit generic instantiation without AST reconstruction.
- Move remaining collection/iterator/order and resource/I/O algorithms into
  ordinary library sources in `crates/ril-stdlib/modules/`. Delete each replaced
  checker simulation, static implementation, late backend body generator and
  runtime algorithm. Keep one explicit set of necessary primitive contracts.
- Eliminate remaining language and native failures, select runtime archives by
  build/ABI identity, and complete Windows/Linux, pointer32/pointer64 and applicable
  native acceptance. Preserved corpus cases define behavior; internal proof-export
  tests change with the removed representation.

## Unicode regeneration

Use Unicode 17.0.0 UCD inputs: UnicodeData.txt, SpecialCasing.txt,
DerivedCoreProperties.txt, PropList.txt and LICENSE.txt. The generator verifies
`xtask/data/unicode-inputs.json`; refresh that manifest explicitly from trusted
versioned inputs, never by entering checksums manually.
Preserve `crates/ril-runtime/src/unicode_generated/LICENSE.txt`.

```text
cargo run --locked -p xtask --bin unicode-data -- manifest INPUT_DIRECTORY xtask/data/unicode-inputs.json
cargo run --locked -p xtask --bin unicode-data -- INPUT_DIRECTORY crates/ril-runtime/src/unicode_generated
```

Run the string/Unicode corpus after regeneration.

## Specification questions
