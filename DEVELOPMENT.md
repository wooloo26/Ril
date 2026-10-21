# Ril development

Ril is an expression-oriented, strongly typed language with algebraic effects,
tracing garbage collection, immutable values, live views and explicit mutable
sharing. Native compilation targets x86_64 Windows MSVC and Linux GNU.

[SPEC](doc/SPEC.md) and [STD](doc/STD.md) are the normative language contracts.
This document is the implementation and contributor guide; the language overview
is in [README.md](README.md).
It describes implementation boundaries, not additional language rules.
Source-level explanations belong beside the relevant implementation.

## Development status

Native compilation, linking and execution are implemented. Semantic integration
and the architectural migration are unfinished. Work proceeds in this order:

1. Complete the semantic core and its independent evidence validation.
2. Finish missing semantics and pass the full acceptance matrix.
3. Expose semantic introspection through the analysis API.

The current implementation lives in the normal source tree. HIR occurrences,
frozen lexical/type environments, original binding PatternIds and callable row
use evidence are retained through semantic analysis and Core. Closure contracts
belong to their descriptors; bound checks enter their captured environment.
Legacy representations and validators still need migration to the complete
abstract value, ten receiving boundaries and five domains described below.

Compiler acceptance still has failing tests and unimplemented corpus cases.
The full matrix must be rerun on Windows and Linux; scoped checks do not certify
completion. The source-transport tests expose incomplete qualified record
projection and composed row forwarding. Both remain active failures.

Build output, extracted probes and temporary reports are disposable. Keep new
implementation work in the source tree and regression cases in the test suite.

## Build and run

Use the toolchain pinned in `rust-toolchain.toml` (Rust 1.99, edition 2024),
with rustfmt and Clippy. Windows needs the MSVC x64 linker and SDK.
Linux needs the GNU x64 toolchain. Install cargo-nextest for `cargo xtask ci`.

```text
cargo build --locked -p ril-cli -p ril-runtime
cargo run --locked -p ril-cli -- targets --json
cargo run --locked -p ril-cli -- check example.ril --explain
cargo run --locked -p ril-cli -- build example.ril --unit executable --output example
cargo run --locked -p ril-cli -- test example.ril --entry test_example
```

Check mode supports `--target pointer32` and `--target pointer64`.
Native builds use `x86_64-pc-windows-msvc` or `x86_64-unknown-linux-gnu`.
Static computation uses the selected layout, never the host's `usize`.
Override the static language-event budget with `--static-budget`.

The runtime static library is `ril_runtime.lib` on Windows and
`libril_runtime.a` on Linux. The CLI normally locates it beside the executable.
Use `--runtime-library PATH` or `RIL_RUNTIME_LIBRARY` for explicit selection.
Compiler and runtime builds must agree on the runtime ABI version.

Reuse one Cargo target directory per host for repeated local verification.
Set `CARGO_INCREMENTAL=0` to avoid accumulating incremental artifacts.
Use `-j2` on memory-constrained development machines.
Do not run Cargo against binaries used by a frozen native test batch.
Delete those copies when the batch finishes. `target/` and `.local/` are
disposable and are not inputs to any build or test.

To continue on another device, use the Git checkout, the pinned toolchain and
the platform linker described above. No local reports, source archives or
prebuilt compiler are required. Start with:

```text
cargo check --locked --workspace --all-targets
cargo test --locked -p ril-test
cargo xtask corpus validate
cargo test --locked -p ril-compiler -p ril-syntax --no-fail-fast
```

The last command exposes the remaining semantic failures; a successful build
does not mean that the compiler is complete. Use the focused tests and coverage
gaps below to choose the next implementation step.

For the two source-transport gaps, run
`cargo test --locked -p ril-compiler --test source_transport`.
`bounded_record_tuple_return` lacks an original frozen edge for a nested bound
projection; `composed_row_with_array_and_callback` infers inconsistent generic
arguments while forwarding the row. Their programs live in
`tests/regressions/source-transport.ril`.

## Tests

```text
cargo xtask corpus validate
cargo xtask corpus list --json
cargo xtask corpus extract tests/conformance/storage.ril::fresh-values-array --out target/example
cargo xtask corpus run --filter source --applicable-only --json
cargo xtask corpus run --compiler PATH_TO_RIL --case CASE_ID --json
cargo xtask ci
```

`validate` checks container structure and normative references.
It does not execute Ril semantics.
`run` checks or builds and executes cases through real CLI subprocesses.
`--timeout-ms` bounds each whole case.
Empty selection, timeout, crash, missing tools, unsupported environments and
unimplemented stages are never passes. OS exclusions remain explicit.

Fixed language-test sources belong under `tests/`, grouped by behavior.
Keep original bundle paths and case names stable.
Place positive controls next to their rejection cases; use `companion` links.
Every case has its own compilation state even in a shared theme file.

```ril
--@ case: empty-inner-dimension
--@ mode: check-fail
--@ spec: SPEC#complete-provenance-and-optional-annotations
-- Error [E0301]: Stored inner dimensions do not match.
--@ file: input.ril
fn example() {
    let source: [0][3]int = []
    let destination: [0][2]int = source
}
--@ end-file
--@ end-case
```

Use exact existing SPEC/STD heading anchors; validation checks them.
Modes are `check-pass`, `check-fail`, `run-pass`, `run-panic` and `run-program`.
Run-pass/run-panic select a public zero-argument `test_*` function.
Run-program declares exit/output expectations and optional arguments,
environment and helper builds. Cases can contain multiple virtual files,
including `.d.ril` declarations and provider/helper sources.

The consolidation moves compiler/CLI fixtures into these bundles.
Rust tests load cases by ID for HIR, Core and fact-mutation checks.
Do not maintain a second copy of a fixed Ril source in a Rust test.
Pure Rust models, randomized generators and invalid byte inputs remain Rust.
Migration preserves source bytes, expectations, entries and execution counts.
Grouping files must not weaken individual expectations or isolation.

Shared programs use `--@ source: NAME` / `--@ end-source`, containing the usual
virtual file blocks; each case selects one with `--@ use-source: NAME`.
Cases retain separate mode, entry, platform and diagnostic expectations.
Use `--@ file: NAME no-final-newline` for exact UTF-8 inputs without a final
newline; hex blocks retain malformed bytes or exact CRLF fixtures.
Rust tests use `ril_test::case_source`, `case_bytes` or `case_by_id` with the full ID.
The registry tests verify case identity, expectations, source reuse and migration coverage.

The expensive ignored concrete-graph oracle needs an explicit bounded run.
Its ignored status is not evidence of a passed oracle.
CI runs applicable cases on both supported platforms; their union must cover
all original IDs and new language regressions.

## Architecture

The workspace retains Rust, Rowan, Salsa, Cranelift and a tracing GC runtime.
Crates define dependency boundaries; related compiler phases remain modules.

| Package | Responsibility |
| --- | --- |
| `ril-compiler-core` | Source locations, typed identities, diagnostics and phase outcomes |
| `ril-syntax` | Lexer, recovery parser, Rowan CST and owned source AST |
| `ril-compiler` | Modules, static evaluation, semantic HIR, analysis and HIR-to-Core lowering |
| `ril-ir` | Data-only Core/native IR and retained semantic evidence |
| `ril-codegen` | Backend/linker interfaces, targets and Core-to-native lowering |
| `ril-codegen-cranelift` | Native AOT object emission |
| `ril-runtime-api` | Versioned execution, heap and ABI contracts |
| `ril-runtime` | GC, continuations, resources, scheduling and standard operations |
| `ril-text-format` | Shared scalar formatting with explicit layout/output limits |
| `ril-cli` | Commands, backend injection and provider configuration |
| `ril-test` | Bundles, extraction and expected/observed outcome contracts |
| `xtask` | Corpus execution and repository checks |

```text
source -> CST/AST -> resolution/static evaluation -> semantic HIR
                                                        |
                                        analysis + solved obligations
                                                        |
                                               VerifiedProgram
                                                        |
                                                structured Core
                                                        |
                                      native IR -> COFF/ELF -> executable
```

The compiler uses abstract code-generation interfaces, not Cranelift.
IR depends on shared core data, not frontend, query engine or runtime.
Runtime crates never depend on compiler or syntax crates.
The corpus runner is compiler-independent and communicates through the CLI.
Architecture checks include transitive production/build dependencies with
all features enabled; development dependencies are checked separately.

Compiler crates forbid unsafe code. The runtime denies it by default.
Exceptions are narrowly scoped to reviewed ABI/platform modules.
Backend representations cannot become semantic authorization.
Salsa queries own revision dependencies; filesystem I/O stays in the driver.

### Semantic core migration

The existing checker still has coupled state and source-location lookups.
Migrate one ownership boundary at a time and remove superseded implementations.
Keep structural migration and behavior corrections separately reviewable.
A completed interface is not proof of complete language conformance.

The target contracts are:

- Typed expression, statement, pattern, declaration and generic-parameter IDs
  identify HIR nodes. Spans locate source; they do not identify dynamic execution.
  Generated nodes retain their actual origin operation and generation kind.
- An immutable type/source store retains dimensions, parameter modes, generic
  identities, member restrictions and qualified rows' lexical environments.
  Ordinary types, storage identities and access permissions have distinct roles.
- A frozen typing environment owns names, substitutions, complete witnesses,
  static keys, row selections and lexical contract bindings.
  Functions and closures capture this environment at declaration/creation.
- Evaluation records identify operand occurrences and allocation epochs.
  Calls, pipelines, defaults and generated callbacks retain their real order
  and normal/interrupted completion, even when one AST executes repeatedly.
- Declaration views freeze before binding. Writes check every possible
  destination and install only its declared view. A current mutable value
  cannot redefine its declaration or restore lost authority.
- Checker orchestration delegates to type/source, heap/capability, loan,
  effect, resource/Result and control-flow domains with owned state.
  Shared work queues use explicit lattices and finite graph representations.

`Session::analyze()` is the introspection migration entry point.
Its immutable `AnalysisSnapshot` retains diagnostics and available facts for
failed or incomplete programs. `check` and `verify` retain their distinctions.
Only complete analysis plus independent validation can construct the private
`VerifiedProgram` required by normal lowering.

The first HIR migration separates pre-static source HIR from checked-input HIR.
Their IDs are local to each snapshot. Static output without a preserved source
mapping is explicitly Transformed; only generated nodes with an actual anchor
are Generated. The checker still consumes ASTs while individual consumers move
to structural child IDs. Origin metadata alone provides no semantic proof.
Controlled AST clones retain HIR IDs; syntax equality deliberately ignores them.
Unified application replay checks callee/operand/result IDs, order and contexts.
Historical values keep their allocation epoch; later views require explicit transport.
Source type graphs retain shared coordinates and explicit unknowns; binding views
reside in one immutable snapshot store rather than being rebuilt at each projection.

Independent validators read original HIR and actual evaluation records.
They may share pure normalization and relations, but cannot substitute a
producer cache, flag or self-consistent descriptor for original source proof.
Every relevant actual occurrence needs coverage, including repeated execution.
Deleting a ledger cannot remove the obligation it was intended to discharge.

### Capability and source invariants

- Slot reassignment, interior writes, closure writes and retained sharing
  are separate. Read, view and Immut restrictions never recover writes.
- Original source coordinates survive empty/nested containers, records,
  tuples, optional/Result payloads, callable views and module forwarding.
  Backing length never proves a declared fixed array type.
- Fresh shells do not imply independent reachable graphs. Deep clone preserves
  internal aliasing and cycles while isolating the copied ordinary graph.
- Formal loans are separate from captured or ambient permission roots.
  Reborrowing suspends the parent; ending a loan does not erase retention.
- Allocation recency transports retained temporaries and observations through
  actual recent-to-older transitions. Final heap state cannot rewrite history.
- Joins retain all possible origins, conditional relations and obligations.
  Unknown overlap or exhausted work cannot authorize independence.
- Result inspection, optional tags, resources, effects, termination and cleanup
  remain independent from source-type compatibility.
- Charge work before cloning, expanding DAGs or enqueueing edges.
  Implementation-work limits are separate from static language-event budgets.
- CauseId traces sources, projections, joins, calls, lost authority and failures.
  Diagnostics and future introspection queries must preserve unknown evidence.

### Native execution

Core retains structured control, instances, provenance, effects and cleanup.
Native lowering owns representation, environments, roots and calling conventions.
Suspension uses native steps, selective CPS and a trampoline.
Callers inherit the actual suspension needs of their callees.

Language panic, abort, cancellation and LIFO cleanup use explicit outcomes.
Unexpected Rust panic is separate. Cleanup preserves pending outcomes and roots.
Handles are generation-bearing 64-bit identities over nonmoving mark-sweep GC.
Precise descriptors and roots cover globals, tasks, queues and continuations.
Multi-worker collection uses safepoints.

CPU tasks and blocking host work use separate execution paths.
Waits must be wakeable or cancellable; cancelled processes are terminated/reaped.
Pure divergence has no promised time slice. Cancellation checkpoints observe
requested cancellation; they do not manufacture scheduling fairness.
Default Fiber::yield yields the logical task; user handlers follow effect rules.
Parallel result and failure ordering follows the specific STD operation.

External providers are chosen only by explicit `--bindings` manifests.
Version-1 manifests contain provider ID, executable, argument vector,
declaration-to-export bindings and optional frame limit.
Relative executables resolve against the manifest directory; no shell is used.
Declaration identities use logical module/name paths, not resolver aliases.

Provider protocol version 1 uses UTF-8 JSON frames prefixed by a little-endian
u64 byte length; the default frame limit is 64 MiB, checked before allocation.
Ready, Invoke, callback and completion messages have checked order/identities.
The typed contracts live in `ril-ir::foreign`, `ril-runtime-api::foreign` and
runtime codecs. Temporary callbacks cannot escape their invocation.
Cancellation retains roots until provider and callback work have drained.

Big integers, SHA-256 and float formatting use num-bigint, sha2 and ryu,
wrapped in Ril's rules. Unicode is pinned to 17.0.0.

## Changing behavior

1. Find the SPEC/STD rule and add adjacent positive and negative cases.
2. Extend the owning typed representation and exhaustive traversal.
3. Implement its domain transfer and required fixed-point operation.
4. Record observations where they happen, including interrupted paths.
5. Add independent validation and missing/misbound-evidence counterexamples.
6. Update Core/native/runtime consumers when execution changes.
7. Run focused checks, then the required broader matrix.

New receiving boundaries register operands, target view and origin, reusing
projection/substitution/reception operations. Do not add another span scan
or reconstruct complete schemas from erased runtime types.
Builtins need signatures and semantic/runtime contracts for effects, writes,
callbacks, resources and Result duties.

Use one write owner per module. Agree public contracts before parallel edits.
Integration owns builds and frozen native runs to avoid artifact races/caches.
Commit subjects are one descriptive line without a type/scope prefix.
Preserve unfinished work in Git commits, with remaining gaps in this guide.
Do not accumulate unregistered test drafts, copied source trees or historical
verification reports. Put regression programs in the corpus and fact-mutation
checks in the active Rust tests.

Acceptance includes fresh versus edited Sessions; renaming, wrapping, module
forwarding and helper extraction; concrete graph models; joins and permission
monotonicity; and native alias/clone/GC/suspension/cleanup/cancellation checks.
A component gate is reported with its scope. Full acceptance needs the entire
applicable matrix, including both pointer layouts for static semantics.

## Current work and coverage gaps

These are implementation gaps, not waived language requirements:

- Finish HIR, explicit environments and domain ownership migration.
  Remove old source reconstruction as each consumer moves.
- HIR arenas, shared immutable analysis snapshots, frozen captures and the active
  type/source environment are in place. Heap, obligation and termination state,
  complete source views and most validators still need domain/typed-ID migration.
  Fixed fixture files are centralized; many older inline Rust programs remain.
- Extend the supported global recursive source graphs to local/generic
  declarations, inferred callback inputs and every handler activation.
  The six focused dimension groups pass;
  broader storage coverage still causes explicit unresolved results.
- Preserve open generic/row and callable sources through arguments, returns,
  captures, constructors, annotations and containers.
- Extend canonical builtin source declarations beyond the closed Os/Path/position
  family. Remaining native and generic operations must preserve original views;
  later values or erased runtime types cannot supply missing proof.
- Finish generated I/O callback observations and operation-frame source views.
  Resumed bindings use the ordinary binding receiver; an enclosing ordinary call
  cannot supply another activation's missing observations.
- Complete generated iterator capture validation and successor-state handling.
- Resolve the preserved nine-scope channel replay-state case with finite work.
  Unknown guard/history relationships remain obligations.
- Complete outstanding static extent/sort contexts and shared-constant audits.
  Object identity and each reference's declared view remain separate.
- Complete the remaining compiler and native acceptance failures on both
  platforms, including the active source-transport regression cases.
- Implement semantic introspection queries after analysis contracts stabilize.

Semantic introspection must expose required annotations and full inferred
capability information: sources, access, sharing, loans, captures, effects,
escape/ownership duties and proof/unknown chains. Symbol formatting is a
presentation choice. Failed programs still expose available symbol information
via an uncertified snapshot. External consumers must not implement a separate
inference engine.

## Specification questions

No confirmed contradictory normative requirements are currently recorded.
Record contradictions here with exact SPEC/STD sections, a minimal example,
conservative interim behavior and the decision needed.
Do not classify implementation defects as specification conflicts.

The following specification decisions are confirmed:

- Pipelines evaluate the left operand, the selected callee, then written right
  arguments, in source order.
- Runtime expressions reading a module-level `meta let NAME` require `&{NAME}`;
  static and type-domain evaluation are exempt.
- Immutable Parallel inputs require an immutable view such as `Immut<[]f64>`.
  An ordinary read parameter can remain live and does not establish immutability.
- Unread buffered data and deferred conditions protect the receiver or explicit
  cursor identity. Conforming custom readers guard that same logical position
  before access; `File::seek` is forbidden while a pending reservation remains.

## Unicode regeneration

Preserve `crates/ril-runtime/src/unicode_generated/LICENSE.txt`.
Use UnicodeData.txt, SpecialCasing.txt, DerivedCoreProperties.txt and PropList.txt
from the versioned Unicode 17.0.0 UCD directory, plus LICENSE.txt, in an offline
input directory. The generator verifies the small generated Unicode input manifest.
Refresh that manifest explicitly from the trusted versioned input directory;
checksums are calculated by the tool, never entered by hand. Ordinary generation
only verifies the committed manifest and cannot update its own expected values.

```text
cargo run --locked -p xtask --bin unicode-data -- manifest INPUT_DIRECTORY xtask/data/unicode-inputs.json
cargo run --locked -p xtask --bin unicode-data -- INPUT_DIRECTORY crates/ril-runtime/src/unicode_generated
```

indices.bin holds little-endian u16 page numbers; pages.bin holds interned
256-scalar property pages. case.rs holds full unconditional mappings;
unicode.rs implements contextual Final_Sigma. Regeneration preserves the pinned
version and must pass the string/Unicode corpus.
