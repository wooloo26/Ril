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

Native compilation, linking and execution are implemented.
Semantic integration and the architectural migration below are unfinished.
Work proceeds in this order:

1. Preserve the implementation and its known failures.
2. Consolidate tests and documentation; refactor the semantic core.
3. Complete missing semantics and run the full acceptance matrix.
4. Implement semantic introspection queries on the analysis API.

Git history preserves the unfinished implementation before this migration.
The preserved full-matrix baseline is `axioms-v3`, before the confirmed
specification decisions below. The application/effect recorder
retains typed HIR occurrences, scope, context and immutable allocation epochs.
Storage declarations use PatternId, writes use ExprId, and protected answers
retain Resume/arm identities through Core. Source compatibility and declaration
comparison use source type graphs, including finite recursive schemas.
Shared graph queries resolve supported global transparent declarations from HIR;
storage patterns, members, copies, sharing markers and abrupt optional fallbacks
retain their original coordinates. Ambiguous legacy names remain unresolved.
The legacy tree projection and its duplicate original-child index are removed.

TypeSourceDomain now owns the active lexical/static type interpretation. Frozen
environments have opaque identities, and owned copies require budget admission.
Bindings, handlers, receiving targets and delayed handler suffixes retain their
own declaration environments. Local SourceTypeIndex views pair SourceTypeId with
FrozenEnvId; equal contents in a fresh capture cannot replace that interpretation.
Closure defaults enter their captured lexical/type environment. Parameter
preparation activations are independently tied to actual call/default receipts;
a later default cannot authorize an earlier forward parameter read.
Legacy keys and witnesses remain transitional, and the complete abstract-value,
ten-boundary and five-domain migrations are unfinished.

At that frozen baseline, on both Windows and Linux, all 143 compiler/syntax test targets report
**1,359 passed, 154 failed and 1 ignored**, repairing 15 prior failures and adding
seven tests without losing a prior case or adding a remaining failure. The raw
batch initially included an invalid synthetic test source; its local test repair
passes on both hosts, as recorded separately in the checkpoint.
For each host and each pointer layout, 902 applicable static corpus cases report
**865 passed, 2 failed and 35 not implemented**, excluding only the one case
explicitly requiring the opposite layout. There are no harness errors.
The two remaining failures are the preserved nine-scope channel timeout and the
open-row callable product. Four related native cases pass on both platforms,
including recursive binary copies and both closure-default programs.
Workspace all-target Clippy with warnings denied and formatting pass.
The separate 1,250-case concrete graph execution audit passes on both hosts under
2 GiB memory and 300-second time limits; the normal suite keeps that test ignored.

The baseline's 1,413 corpus cases structurally validate (99 bundles, 176 diagnostic codes,
840 companion links). Each host executes 1,411 applicable cases, excluding only
the two explicitly requiring the other platform. Windows reports
**1,302 passed, 19 failed, 90 not implemented**; Linux reports
**1,303 passed, 19 failed, 89 not implemented**. Neither reports a harness error.
Four old cases recover and the new case passes, with no lost case or regression
against the frozen v2 baseline. All 1,409 shared cases agree in verdict and
static diagnostics. Full compiler acceptance remains unfinished.
`target/axioms-v3-checkpoint.json` records those baseline scopes and failures;
`axioms-v3-all-tests-*-final.json`, `axioms-v3-static-pointer*-*` and
`axioms-v3-all-corpus-*` retain individual outcomes. Compiled source archives and
frozen native compiler/runtime artifacts preserve both v2 and v3 for comparison.

The preserved `spec-decisions` checkpoint implements pipeline evaluation in the confirmed
left/callee/written-argument order, including Core lowering and termination
analysis. SPEC records runtime module-level `meta let` read capabilities and the
static/type-domain exemption. Parallel examples require `Immut<[]f64>`; ordinary
read parameters remain live views. Buffered readers forbid `File::seek` while
unread bytes or deferred errors reserve the receiver or a delegated file cursor.
On each host, 71 selected corpus cases pass: 40 native unit returns, one expected
language panic, 25 diagnostic rejections and five static acceptances. All 61
selected pre-existing cases still pass, and ten new cases pass. Twenty focused
compiler integration tests pass, including both pointer layouts for the ten new
cases. Fourteen application/termination unit tests pass; runtime library tests
report 214 passed/one ignored on Windows and 217 passed/two ignored on Linux.
Workspace all-target Clippy with warnings denied, formatting and diff checks pass.
All 1,423 then-current corpus cases structurally validate (99 bundles, 176 diagnostic
codes, 847 companion links); this is separate from the selected semantic runs.
The two-platform validation scope and frozen artifacts are recorded separately in
`target/spec-decisions-checkpoint.json`; the v3 full-matrix results do not certify
that source.

The preserved `read-position` slice adds `Io::ReadPosition`, `read_position`,
`guard_read`, `guard_seek` and `read_buffered_at`. Immutable position tokens retain
their identity across copying without retaining receiver or resource authority.
Protected accesses use the same receiver/position/delegated-endpoint reservation
check. Only the nearest buffered activation supplies a read-ahead permission;
nested buffers cannot borrow an outer buffer's pending claim. Copied pending
buffers retain independent claims and may drain their own cached bytes.
One shared intrinsic type identity supplies its name, scalar source node and
target word layout to runtime semantics and static/type checking. Type quotation,
aliases, comparison and `byte_size` work on both pointer layouts; invalid type
arguments and static attempts to create runtime identities are rejected.
Module resolution, callable interfaces, Core and both native backends support it.
Conforming custom operations guard the same logical position before every cursor
access; a function signature alone does not prove external cursor behavior.
On each host, all 84 selected corpus cases pass: 44 native unit returns, five
expected language panics, 29 diagnostic rejections and six static acceptances.
All 71 preceding selected cases still pass; thirteen new cases pass. Fourteen
focused compiler integration tests and the layout unit test pass on each host,
including both layouts for the new cases. The two codegen libraries and runtime
API report 36 passing tests. The unchanged runtime artifacts retain full library
results of 218 passed/one ignored on Windows and 221 passed/two ignored on Linux.
Workspace all-target Clippy with warnings denied, formatting and diff checks pass.
The 1,436 then-current corpus cases structurally validate (99 bundles, 176 diagnostic
codes, 856 companion links); the full semantic corpus is not recertified by this
focused run. `target/read-position-checkpoint.json` records scopes, source archive
and artifact hashes. The wider semantic migration and full compiler acceptance
remain unfinished.

The current `builtin-graph` slice defines 22 closed Os, Path and read-position
operations plus four native constants in one declaration schema. Original source
graphs supply runtime type projections, public parameter labels and modes, and
result/payload views. The replaced native-operation table and special position
witness construction are removed. Stored Path results now retain their original
source view through defaults, capture, composites, mutation, joins, channels and
handler/resumption transport. The original immutable native array schema remains
dynamic: its backing length cannot certify a fixed dimension.
Builtin references are joined by HIR expression identity; generated value-test
reads retain and validate their original PatternId anchor and lexical owner.
One bounded lexical index supplies reverse coverage, independently of producer
callable tags.
Existing physical application records bind results to their HIR application and
complete caller/default/closure context; source graphs are compared structurally.
Canonical names do not override actual same-named effect declarations.
The legacy source witness remains a derived bridge; this is not the complete
canonical value, domain or boundary migration.

On each host, all 96 applicable selected corpus cases pass: 54 native unit
returns, five expected language panics, 31 diagnostic rejections and six static
acceptances. All 84 preceding selected cases remain passing, alongside eight new
cases and four applicable pre-existing native/path cases. The 94 shared cases
agree in verdicts and observed outcomes. Seventeen focused integration tests pass
within the complete run; fourteen builtin/native cases check both pointer layouts
and reach Core. Seven builtin source unit tests include adversarial evidence
deletion, schema substitution and same-source activation/result swaps.
The 146-target compiler/syntax gate reports 1,366 passed, 152 failed and one
ignored on each host after a fixture-only repair. Two failures recover relative
to the preserved v3 complete gate, with no new regression. Raw complete runs
retain 1,365 passed/153 failed/one ignored: the added pattern index exposed a test
selector that chose a binding Pattern instead of its real Expr. Only that
`cfg(test)` selector changes after native freezing; both hosts rerun all seven
builtin source tests successfully. Production code is byte-equal between the
compiled and final source archives, which remain separately identified.
Core, codegen, runtime API and runtime library gates report 256 passed/one ignored
on Windows and 259 passed/two ignored on Linux. Workspace all-target Clippy with
warnings denied, formatting and diff checks pass. All 1,444 corpus cases
structurally validate (100 bundles, 176 diagnostic codes, 858 companion links).
`target/builtin-graph-checkpoint.json` records both source identities, frozen
artifacts, raw runs, fixture replay and remaining failures. The 96-case native
selection does not certify the full semantic corpus. Complete compiler
acceptance and the wider domain/boundary migration remain unfinished.

The preserved migration checkpoint is `application-v5`: on each Windows and Linux
host, the complete 45-target source gate reports **869 passed, 30 failed and
1 ignored**. It repairs 20 failures from `identity-v5`, with no new regressions.
Of the original 43 v51 regressions, 23 remain active failures.
The additional non-tail-reference target still has seven end-to-end failures;
its separate resumption-epoch replay test passes without authorizing lowering.
This is an intermediate checkpoint, not completed refactoring.
Workspace all-target Clippy with warnings denied, formatting, corpus tooling's
27 tests and diff checks pass. The 54 application cases pass on both hosts:
34 compile and execute native programs, 19 correctly reject and one checks.
There are 99 bundles and 1,410 cases; structural validation passes.

The original corpus has 84 theme bundles and 1,067 case identities.
The focused native cases do not certify full corpus conformance.
Historical native reports cannot certify this newer compiler.

Detailed development reports remain under `target/`, including
`application-v2-case-comparison-{windows,linux}.json`,
`application-native-corpus-{windows,linux}-v5.json`, `application-v5-checkpoint.json`
and matching build/test logs. Non-tail-reference failures remain separate.
Git preserves removed design documents and implementation history.
New checkpoints identify the source revision, selected cases and platform.

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
Keep reports and minimal reproductions separate from disposable build caches.
Do not run Cargo against binaries used by a frozen native test batch.

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
Save an explicitly unfinished checkpoint when changing development phase.

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
  platforms. Four pending test drafts contain unique cases that need migration.
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
