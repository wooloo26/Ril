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
- Validate original HIR and actual evaluation records independently. Missing
  evidence or exhausted work cannot authorize behavior. Failed analysis retains
  an uncertified `AnalysisSnapshot`; only complete validation mints `VerifiedProgram`.
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

- Complete the canonical abstract value, frozen environments, ten receiving
  boundaries and five domains. Replace remaining Span tables, erased-type
  reconstruction and legacy witnesses as their consumers migrate.
- Extend Source transport to local/generic recursive declarations. Finish migrating
  generic Source consumers to graph views paired with frozen environments; preserve
  open rows and qualified callables through inputs, returns, captures, constructors
  and containers, then remove the remaining closed-witness adapters. Replace raw
  callable annotation text with frozen declaration references so composites can
  retain contracts originating in different lexical environments. Complete mixed
  static sorts and captured/local aliases, and solve pending Source equations
  before certifying a producing context.
- Complete shared value derivations for historical heap reads, callback results
  and generated inputs to parallel workers, scope/channel bodies, iterators,
  variant/recovery callbacks, resources and foreign calls. Their unmigrated
  `EntryOrigin::Unresolved` inputs now leave inferred closure parameters
  uncertified. Iterator creation recipes do not certify individual transitions.
  Finish channel payloads, handler activations and resumption transport.
  Resolve the nine-scope channel replay
  case with finite work while preserving unknown guard/history obligations.
- Implement conditional bindings (`if let`, `while let`) and array/tuple rest
  patterns. Complete record-rest, nested closure/default
  and retained-handler transport covered by the corpus.
- Complete static extent/sort contexts, shared-constant audits and builtin source
  declarations. Keep object identity separate from each reference's declared view.
- Resolve compiler and native acceptance failures on both platforms, then expose
  symbol and capability introspection through immutable analysis snapshots.

Source transport regressions, including open row composition with fixed arrays
and callbacks, are in `tests/regressions/source-transport.ril`.
Operation and resumption Source views are in `tests/regressions/effect-source-views.ril`.

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

- Does the one-rest limit apply separately to each tuple/array/record pattern,
  or to the whole alternative? For example, is `([a, ..xs], [b, ..ys])` valid?
- Does a named array rest (`[head, ..tail]`) produce a shared read-only window
  or a new array? Specify its object/slot identity, permissions and lifetime,
  and whether a fixed input preserves the known remaining extent (`[N-k]T`).
