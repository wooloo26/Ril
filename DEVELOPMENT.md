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
  dependencies separately from invocation answer constraints. Record construction
  composes complete types from evaluated members and spreads; contextual `typeof`
  reads the declared type graph, including nested queries and field projections.
  Named Type instances travel with function values, including phantom parameters;
  callable type graphs retain their lexical interpretation inside products.
  Actual entry arguments now own their complete type graphs for named functions,
  closures, signature probes and generated inputs. Parameter receiving consumes
  those graphs directly; generated input reconstruction through call receipts,
  syntax projections and closed witnesses has been removed. Result fallback
  callbacks receive the projected error type from their actual subject.
  Symbolic array dimensions follow those owned types; physical storage keeps
  its construction and mutation history. Excluded Result paths use their own
  symbolic payload instead of borrowing the present variant's storage/duties.
  Finish routing other static sorts, defaults, rows and constructors through the
  same typed operations.
- Complete control-flow analysis for heap access, borrowing, effects, duties,
  resources and channels. Resolve generated callback inputs, use finite
  loop/recursion summaries and preserve correlated aggregates. Normal,
  abrupt and resumed answers now carry owned type graphs; block-exit/cause replay
  has been removed. Resumption requests carry no normal result; leading
  expression contexts consume the actual completion through common receiving.
  Derivation carries its input's owned type graph through copy and publication.
  Complete suspended operand cursors when earlier operands precede a resumption.
  Immutable loop closures compare finite environment summaries
  while keeping object and invocation identities. Finish mutable environment
  correlations, conditional/rest-pattern receiving and contextual
  inference across defaults, callbacks and control transfers.
- Run static execution on the eligible elaborated operations used by compilation.
  Finish Const/Key argument and extent inference, selected numeric representation,
  and callable instantiation queries. Instantiate foreign headers and defaults
  from original declarations and static choices, removing generated declaration
  ASTs. Complete nested/captured callable instance owner mappings.
- Finish the standard library migration as one bulk pass, before repairing each
  library's semantic cases. All 31 non-prelude public module interfaces and the private
  storage interface now live in `crates/ril-stdlib/modules/`. Ordinary bodies
  include collection/variant combinators, stable sorting/search and heap sifts,
  explicit iteration, binary/hex encoding, string composition, integer codecs,
  SHA-256, resource composition, parallel decomposition, time arithmetic and
  seeded random generation. The whole late Core library generator has been
  removed, along with the replaced variant/order/resource/stream checker
  simulations and native array/variant callback algorithms. Runtime ABI is 8.
  Complete the remaining ordinary bodies, including buffered streams, Unicode
  conversion/data/casing, native path composition and exact decimal float codecs.
  A bodyless declaration is not evidence that an operation is a necessary
  primitive or is implemented. Bind genuine storage/host/scheduling primitives
  to declaration identities, complete opaque representations and native data
  exchange, and delete the remaining legacy catalogs, static special cases and
  runtime algorithms. Do not keep the old library entry points as a fallback.
  Move prelude re-exports and remaining closed signature families to the same
  declarations, and keep private storage operations inaccessible to user code.
  Static availability remains a declaration property; eligible operations must
  execute these same elaborated bodies during static computation.
  Then repair complete-type receiving, callable mode/row schemes, captured
  environments, inference and finite loop/recursion summaries across the whole
  library. Source parsing and Rust checks currently pass; language and native
  acceptance remain incomplete. Preserve every corpus expectation throughout.
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

- Generic structural equality has a conditional applicability requirement. A
  declaration probe retains equality on a Type parameter without assuming that
  every possible instance supports it. Actual input types are checked by the
  same elaborated operations or substituted recursive summary at each invocation,
  including aliases and higher-order calls; callable/resource constituents still
  fail with E0327. Recursive summaries retain and compose equality input uses.
  A symbolic operand outside declaration analysis remains incomplete. This lets
  the STD generic testing helpers use ordinary equality without a privileged
  checker contract or a new source-level trait.
