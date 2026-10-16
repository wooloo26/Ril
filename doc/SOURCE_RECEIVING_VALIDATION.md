# Original source types at receiving boundaries

Status: confirmed implementation gap after the v30 component checkpoint.
The shared relation, source receiving hooks and call preparation are active.
The v38 shared-model gate passed seven independent relation tests and one
metadata conversion test on Windows and Linux; it predates the receiving and
call integration. The v39 integration compiles on Windows and Linux and rejects
all nine preserved before inputs with `E0301` on both static layouts. Its
positive-control and regression gates fail, so the receiving implementation is
not complete and the native gate remains pending.

The selected v39 batch has six targets: the compiler library and five Source
integration adapters. Each host reports 489 passed, 76 failed and one ignored
Rust test (library 470/70/1, integrations 19/6/0). Twenty-one failures stop at
invalid new fixtures: eleven missing declaration separators, nine lowercase
module bindings and one executable-block declaration. The remaining failures
include actual legal-program regressions, including unknown schemas,
call coverage, callable descriptors and fixed-array storage proofs. Full logs
and classifications are retained in `target/source-receiving-v39-checkpoint.json`
and `target/source-receiving-full-source-{windows,linux}-v39.log`.

The v42 focused gate compiles without warnings on both hosts. The `source_`
library filter reports 77 passed, three failed and 469 filtered; it is not a
rerun of the full library. Six Source adapters report 21 passed and five failed.
Ordinary call inputs (nine groups), receiving boundaries (four), construction
contexts (three), match contexts (two), and the projection non-authorization
regression (one) pass on both static layouts. The explicit-named adapter has
two passes and five NI failures. Ten of eleven independent call-review tests
pass; the remaining positive case needs a proof that a `panic` operand prevents
normal named body entry. Fourteen receiving/sensitivity unit tests and two
nested-source fixed-point tests pass. Exact results remain in
`target/source-receiving-v42-checkpoint.json` and its referenced logs.

The separate raw-Checker debug test initially aborts on the Rust test harness's
small stack. Re-running with the production worker's existing 16 MiB stack
reaches its assertion and still fails; it is not a semantic pass. Its retained
original input keys disprove the proposed missing-fresh-product-key explanation.
The outstanding explicit cases need genuine UID transport for return/projection
sources and complete substitution of a selected record remainder.

The v43 batch compiles on both hosts. Its same library filter remains 77/3/469;
eight Source adapters now report 27 passes and three NI failures per host.
The declaration-default adapter's three groups pass, including unused invalid
defaults, legal declaration-only literals/earlier formals and receipt deletion
mutations. Explicit-named tests improve to five passes and two NI failures.
The original full seven-entry native fixture fails its first `pointer32` Source
check at a direct generic array formal index. Neither its `pointer64` Core nor
its native-IR or execution prerequisites have passed. The raw-Checker debug test
now uses the production 16 MiB worker stack directly and reaches its assertion
without aborting; the Source assertion still fails. Evidence is retained in
`target/source-receiving-v43-checkpoint.json` and its referenced logs.

The v44 focused gate compiles without warnings on both hosts. Its `source_`
library filter reports 80 passed, two failed and 471 filtered; all eleven
independent call-review tests pass, including the real panic operand's absence
of normal body entry. Eight integration adapters report 31 passes and two NI
failures, both in explicit generic projection/return transport. All six
declaration-default groups pass on both layouts, including recency transport,
snapshot mutation and repeated evaluation. The shared relation now passes nine
model tests, with closed record remainders compared under the original budget.
The complete seven-entry fixture passes Session, Core and native-IR preparation.
These are preparation results, not native execution or a full-library rerun.

The v45 correction uses the actual scoped source identity of an instantiated
generic record result. It does not reconstruct a source from an expected type.
Both hosts compile without warnings and pass all seven explicit-named groups,
the complete native-fixture prerequisite, and three private UID/substitution
tests. The fixture checks both pointer layouts, then lowers all seven selected
entries for pointer64. The actual CLI native adapter has been activated with
the same preserved fixture bytes; execution is a separate gate. The remaining
v44 library failures concern canonical builtin callable source contracts and
resource/result structure; the full-library and corpus gates remain outstanding.

The v45 native gate then passes all seven entry jobs on each of Windows MSVC and
Linux GNU. Each host runs one adapter executable with seven Rust tests, one
distinct preserved Ril source and seven independently built native entry jobs.
Every job requires its business assertions, executed/returned-unit runtime
status and exit zero. CLI, ABI-3 runtime and adapter hashes match before and
after execution; no Cargo process runs during the frozen gate. Exact reports,
hashes and logs are referenced by `target/source-receiving-v45-checkpoint.json`.
This does not rerun the older native adapters or certify the full language.

The subsequent v46 regression reruns the entire compiler library and 32 Source
integration adapters. Both hosts terminate with exit 1 and the same results:
library 521 passed, 31 failed, one ignored; integrations 217 passed and 11 failed.
The total is 738 passed, 42 failed and one ignored across 33 executable targets.
These are real legal-program regressions and missing required negative
diagnostics, not an acceptance gate. The nine preserved dimension conflicts and
the v45 new Source adapters remain passing. Full evidence is retained in
`target/source-receiving-v46-checkpoint.json` and its two full logs.

The next audit confirms two additional wrong accepts at nominal constructor
payloads. The unchanged v45 CLIs accept a stored `[]int` with two known elements
as a `Fixed([2]int)` payload, and stored `[0][3]int` as `Fixed([0][2]int)`.
The genuine literal `Fixed([1,2])` also passes as the positive control. Both
hosts run all three exact sources under both pointer layouts: twelve checks,
exit zero, no diagnostics, no build or native execution. Compiler hashes match
before and after. Exact bytes and receipts remain under
`target/constructor-source-before-v45/` and its adjacent JSON report. This is a
confirmed implementation defect; the constructor correction and independent
replay are pending and must reject both conflicts with `E0301`.

The storage audit also confirms four wrong accepts with the same frozen v45
Windows CLI on both layouts: variable replacement, mutable record-field
replacement, array-element replacement, and `Array::push` all accept stored
`[0][3]int` where the written storage member is `[0][2]int`. Eight checks exit
zero with no diagnostics and unchanged compiler hashes. Linux has not run this
before probe. Exact sources and the report are retained under
`target/storage-source-before-v45*`; identical fixture bytes and strict `E0301`
regressions are active in `storage_source_receiving.rs`. The storage correction
is pending. Matching-schema positive controls retain the separate permission
and ordinary shape requirements.

The v47 attempt stops at Rust integration errors on both hosts and executes no
semantic case. The corrected v48 batch compiles without warnings, then executes
the entire compiler library and 37 Source adapters. Both hosts terminate with
exit 1: library 533 passed, 30 failed, one ignored; adapters 230 passed and 20
failed; aggregate 763 passed, 50 failed and one ignored across 38 targets.
Constructor receiving passes four of five groups, including strict conflicts,
valid literal/fixed controls and deletion/cross-call mutations. Its remaining
mutation fixture generates only one actual loop event, so it cannot test a
later event yet. Producing-result contexts pass four of five groups; the
optional callable's public input scope remains unresolved. The new builtin
gate passes three groups and fails its positive group because the latent
summary probe confuses heap Pivot identity with a formal parameter slot. All
three standard-array groups still need the exact-count Parallel result path's
original source mint. Storage retains its four confirmed wrong accepts and
passes its matching-schema positive group. No v48 native or full-corpus run is
claimed. Evidence is in `target/source-receiving-v48-checkpoint.json`.

The v49 full-library/38-adapter run compiles without warnings on both hosts and
terminates with the same exit 1 results: library 552 passed, 13 failed, one
ignored; adapters 245 passed and nine failed; aggregate 797 passed, 22 failed,
one ignored across 39 targets. All five ordinary-result context groups, all
three standard-array groups, all thirteen existing static-numeric context
groups, all five existing result-context groups, and all 26 channel-message
groups pass. Constructor receiving passes five groups, including the corrected
actual repeated-event mutation. Its sixth new fixture stops at reserved keyword
`next`, so no semantic result is claimed for it. The builtin positive group now
passes its four-operation open-bound source but still rejects the explicitly
annotated source because target and primitive data schemas normalize
differently. Static constant view negatives pass; the new alias positive stops
at its missing required global state annotation. A legacy static alias test
also exposes unnecessary name splitting for an identical object and identical
view. Four storage defects remain. Exact evidence is retained in
`target/source-receiving-v49-checkpoint.json`; no current native or full corpus
certificate follows from this run.

The v50 compile attempt was interrupted without a terminal compiler result.
After confirming that neither host still had a Cargo/rustc process, v51 reused
the existing caches and preserved the earlier logs. Both hosts compile without
warnings and execute the entire library plus 41 integration adapters. Each
reports 811 passed, 20 failed and one ignored across 42 executable targets
(library 561/7/1, adapters 250/13/0), exit 1. New call-root observations pass
both tests, closure-source groups pass all three, canonical builtin receiving
passes all four, static constant view tests pass all three, and constructor
receiving passes all six. Generated iterator sources pass two groups and fail
two; additional iterator cases fail independent capture/source reconstruction.
Five previously passing explicit/symbolic adapter cases regress because a
whole open formal is selected before projecting its genuine source leaf.
The four strict storage negatives still demonstrate actual wrong accepts.
`target/source-receiving-v51-checkpoint.json` and the corresponding compile and
full-source logs preserve the results. No v51 native or full-corpus pass is
claimed. Storage ledgers and subsequent repairs are work in progress.

## Frozen before evidence

The exact v30 Windows CLI, SHA-256
`038A74DD7ED1F93D3BEF7581FC315B32F34B92B2E70634DD1EFD441D12C6AE69`,
accepted nine inputs whose written source dimensions conflict:

- Stored `[]int` passed to ordinary `[2]int` and inferred generic `[2]T`.
- Stored `[0][3]int` passed to `[0][2]T`.
- A callback accepting `[3]int` passed to a callback accepting `[2]int`.
- A default returning `[]int` received by a `[2]int` parameter.
- Stored `[0][3]int` received by a `[0][2]int` binding, function return or
  typed record member.
- A callback accepting `[3]int` received by a `fn([2]int)` annotation.

These are nine actual Source checks with exit 0 and no diagnostics. Both
before/after executable hashes match. The separate explicit generic probe
still reports NI, so it is not counted among those accepted inputs. No probe
builds or executes a Ril native program. Exact bytes and outputs are retained
under `target/ordinary-call-source-before-v30-*`,
`target/ordinary-call-extra-before-v30-*` and
`target/source-receiving-boundaries-before-v30-*`, with a JSON report per batch.

SPEC's array element invariance and matching fixed dimensions provide the
requirement. This is an implementation defect, not a normative contradiction.
An empty outer array does not remove the inner type's dimension obligation.

## Boundary and common relation

Receiving currently can replace a value's complete source descriptor before
checking storage shape. The subsequent graph walk can only see actual elements;
it loses inner dimensions when the outer array is empty. A known backing count
also cannot establish a stored value's declared fixed type.

Root owns the common `sema/source_reception.rs` relation and general receiving
checks before `types::ascribe_signature` changes a descriptor. A owns actual
call/default observations, explicit named preparation and independent call
replay. The relation is shared; these paths must not develop different rules.

The pure relation checks original normalized source coordinates. It retains
array dimensions, callable modes and genuine binder identity. Array elements,
map arguments, tuples and nominal arguments remain invariant; readonly callable
parameters reverse the receiving direction and callable results preserve it.
Mutable callable parameters and mutable record fields are invariant. Existing
ordinary type, row/effect, default-interface, permission, loan, resource and
Result checks remain necessary. This source relation grants none of them.

Actual array literal AST may receive a construction context. Stored values,
clone's new shell, a final heap length, a successful type annotation or an
interned descriptor's self-consistent key cannot substitute for that AST.
Missing original source, unrelated rigid identities, opaque computations or
exhausted reconstruction budgets keep the obligation unresolved.

## Physical coordinates

Existing `CallArguments` retains the original coordinates without inventing
a callable or declaration:

```rust
supplied: BTreeMap<u32, SuppliedArgument>
// The map key is the actual parameter slot after label/position mapping.
SuppliedArgument { expression: usize, allocation_epoch: usize }
```

Mint the expression coordinate only at its real recorder emission, in the
original caller namespace. A traversal early exit supplies no token. The
independent replay joins the actual call event, unique arguments record, exact
slot, actual AST operand and complete `InvocationExpression` context. It aligns
the frozen input with body entry through the precise allocation history. Same
spelling, source span, runtime type or final binding value is insufficient.
The matching invocation-expression row also retains `argument_of(event,slot)`
only for the real root operand occurrence; auxiliary observations cannot pay
this obligation. Replay bounds an operand by its actual callee and the later
sibling/callee occurrences, including repeated loop spans.

Defaults reuse `DefaultUseId` and its original result snapshot. Add
`result_allocation_epoch: Option<usize>` at the same actual result emission;
body entry cannot be used to guess this earlier epoch. Replay checks origin,
target, parameter, caller, completion and actual entered invocation. Partial or
Never evaluation cannot become successful body entry.
The current implementation also records `result_expression: Option<usize>` at
that same root emission. This permits a declaration-only default check to use
its exact default-use context instead of searching by span or cause. The new
declaration-default producer/replay hook passed its six-group v44 gate on both
hosts. It checks actual declaration-probe default roots even when no call enters
the named body, and independently rejects missing or retargeted receipts.

Core presentation retains these coordinates and the actual default receipt.
Constructing presentation metadata provides no semantic authorization.

## Gate

First reject the nine preserved inputs with a source dimension/type diagnostic;
NI is not a completed negative language case. Add positive controls for genuine
fixed inputs, fresh literal receiving, harmless source weakening, unchanged
default interfaces and rigid caller forwarding. Add mutations of the actual
slot, expression, event, epoch, caller UID and default receipt, including joint
changes to expression and entry descriptors. Reconstruct stored Name source
from its real annotation or formal header, not mutable final binding state.

Compare both static layouts, fresh/incremental sessions, Core and real Windows
and Linux native execution separately. The older component/corpus checkpoints
do not certify this pending correction.
