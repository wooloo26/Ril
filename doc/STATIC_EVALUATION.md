# Static evaluation implementation

## Tail invocation checkpoint after v17

The frozen v17 compiler aborts on a finite meta accumulator with 1,024 recursive
calls. `target/static-tail-evaluation-before.ril` and its adjacent status/stderr
files preserve the reproduction: Windows exit -1073741571, no JSON report, and
an overflow of the `ril-static` thread stack. The v17 corpus remains unchanged;
its successful cases did not cover this input.

The evaluator now drives named and anonymous tail calls through an explicit
invocation loop. Only the selected result of a block, conditional or match, and
an explicit return operand, can hand off to that loop. Arguments evaluate once
before the handoff. Non-tail calls keep their own driver and lexical environment.
Caller return-shape contracts remain pending and apply to the final value in
reverse order; collection identity and internal aliases are not copied away.
A meta call cannot use a final lambda/builtin handoff to return a type token.
Type-function bodies isolate their own return control from meta invocation.

Both Windows and Linux pass five CLI subprocess test groups in
`crates/ril-cli/tests/static_tail_calls.rs`. These exercise finite/mutual/lambda
tail calls, explicit return and match tails, a captured callable result, actual
native cloning of a shared fixed-array graph, infinite recursion, non-tail
implementation limits, and family/type rejection. Each host also passes the 30
static evaluator unit tests and 41 existing static integration tests. Logs are
`target/static-tail-{calls,unit,regression}-*.log`; the CLI checkpoint uses the
`v4` suffix. No crash or unsupported result is counted as an accepted program.

Deep non-tail evaluation and deeply nested type/expression traversal still have
explicit implementation stack limits. These produce an incomplete result,
separate from language E0811. This checkpoint does not establish arbitrary-depth
static evaluation or the specified event-budget accounting.

## Invocation-specific lexical environments

An additional audit found that a returned local function could read a sibling's
environment from a later call to the same factory. Creating `make(7)` and then
`make(9)` incorrectly changed the first callable's result to 9; this could even
make an incorrect static assertion succeed. Local declarations now belong to an
environment arena with a distinct identity for each evaluated block entry.
Sibling and recursive declarations share that entry through arena references.
Anonymous callables retain both values and the selected declaration environments.
Calls restore both domains on exit, including type-function argument/default
evaluation and tail return-shape processing. The independent source tests are in
`crates/ril-compiler/tests/static_tail_semantics.rs`.

## Event budget contract and current integration

SPEC's static budget counts meta/type function entry, static callback entry and
loop iteration. A root has a configured positive allowance. Consuming its last
unit permits that event; the next charged event fails with E0811. Syntax visits,
literal parsing and normalization work need separate implementation limits.

`CheckOptions.static_budget` and CLI `--static-budget` now select a positive
allowance (default 100,000). A root owns its remaining events, and nested
evaluation inherits them. The separate interpreter work allowance reports an
incomplete result. Literal spelling, arithmetic and syntax/type visits do not
spend language events. Sequential array combinators charge the next-element
tests, including the final unsuccessful test, and each actual callback entry.
An early decisive predicate skips the remaining iterations.

Seven source test groups cover exact call/callback/iteration quotas, last-unit
completion, independent roots, tail-call accounting, type applications, fixed
shape publication and large bigint spelling. Two independent counter tests
check root ownership and work/event separation. CLI tests exercise configuration,
zero rejection, and native output from distinct captured declaration groups.

Type metadata must not introduce another source invocation or let one root
replenish another. The first integration audit caught repeated normalization of
an already evaluated alias in parameter/return publication. Transparent aliases
now retain normalized witnesses keyed by declaration, lexical environment and
normalized arguments; constant member traversal projects the resolved shape.
Direct type-function applications still consume their own entry events. Closed
named signatures now retain their own witnesses: global annotations are
elaborated as real roots, and a local instantiation inherits an active root.
Anonymous parameter annotations evaluate at closure creation, in that root and
environment. Parameter/return publication then consumes the normalized types.
Generic signatures and signature-local declarations retain their separate
instantiation obligations; no witness is cached without its static arguments.

After these changes, Windows and Linux each pass 32 static evaluator unit tests
and 68 integration tests in the selected static suites, including seven quota
groups and the 20 independent tail/environment/shape groups. Nineteen of the
latter exercise full Sessions; one also checks generic aliases at the static
evaluation boundary and explicitly retains the later unsupported Session result.
The logs are `target/static-budget-{unit,regression}-*-v3.log`. These are targeted
component checks, not another full workspace/corpus snapshot. Deep type-function
recursion and other remaining static forms still require implementation.
Runtime Div accounting remains independent.

## Type-producing tail applications

`type_invocation.rs` now drives direct type-function tail applications through an
explicit loop. A pending type expression retains the environment in which its
actual arguments were written, including a selected match binding or local
declaration group. Entry keys include declaration, group identity and normalized
arguments, so the same local declaration in two factory activations is not a
false recursive cycle. Ordinary meta invocation saves and clears the type-return
mode and restores it afterwards.

`target/static-type-tail-audit.ril` previously reached the implementation nesting
limit for 512 finite steps. Four new frontend groups cover finite/mutual/explicit
return/match tails, a 1,024-versus-1,025 event boundary including the meta argument
helper, changing-argument infinite recursion, and type-return family isolation.
An additional CLI test uses the computed type to produce a native constant and
executes the result. Both Windows and Linux pass the four new frontend groups,
the existing 20 independent audit groups and seven quota groups, and the six
CLI tail-call groups. The paired logs are `target/static-type-tail-*-v2.log`;
Windows CLI coverage is in `target/static-type-tail-native-windows-v1.log`.
This loop does not yet eliminate the stack used by arbitrary non-tail type
construction.

## Ordinary static defaults and labelled applications

Static typing and evaluation now share `StaticApplicationPlan`. The plan maps
each written argument to one declaration slot, rejects unknown labels and
duplicate or missing arguments, and records which omitted slots use defaults.
The evaluator computes the callee first, then explicit values once in written
order, then defaults in parameter order inside the selected callee's lexical
declaration group. Function/callback entry is charged only after binding finishes.
A return in a default exits that callee; a return in a computed callee or explicit
argument still exits the enclosing callable. Nested calls retain their own return
boundary. All defaults are type-checked even when callers supply every slot.
Self/later parameter names are unavailable to a default, including through local
helpers; earlier parameters and genuine local shadowing remain available.

Known callable values retain their declared labels and defaults until an explicit
callable type supplies a new interface. A private callable view then carries that
destination interface, erases the source defaults, and forwards the same evaluated
values to the original target. It neither changes the target's captured environment
nor adds a language entry event. Typed bindings, parameters, results and supported
container members apply the same interface projection without copying collection
nodes. Meta type-token rejection and existing mode/permission restrictions remain.
Generic arguments still require the ordinary static inference proof; an omitted
default cannot borrow a similarly named caller type parameter. Builtin labelled
calls and unsupported callable obligations remain explicitly incomplete.

The new compiler `static_applications` suite has 15 groups covering the plan,
typing, control flow, quota boundaries, lexical capture, destination interfaces and
shared constant origins. Its CLI counterpart has five groups: five source programs
execute natively across four groups, and one group checks precise rejection codes.
Both Windows and Linux pass these suites. The existing 32 static evaluator unit
tests, 20 tail/environment tests and seven budget tests also pass after integration.
Evidence is in `target/static-applications-{final,linux,lib,regression}.log` and
`target/static-applications-native-{windows,linux}.log`. These targeted checks do
not replace the frozen workspace/corpus evidence.

## Contextual static numeric selection

Static typing and actual evaluation now use the shared exact `numeric_literals`
kernel. A known binding, selected parameter/default, callable result or fresh
aggregate member supplies its numeric context before the literal is evaluated.
Rigid typed peers constrain arithmetic literals without changing the peer's own
type. Integer magnitude is retained until selection, including values above i128;
integer-to-f32 rounding never passes through f64. Committed StaticValue variants
retain int layout, fixed integer width/sign, bigint magnitude, or float width and
IEEE value. Stored values and written suffixes cannot acquire a new choice.

The application plan obtains parameter contexts from the actual selected callable
and an already prepared signature or pure structural witness. It does not execute
type functions to predict a later parameter context. Arguments still evaluate once
in written order. Incomplete generic/late context preparation remains NI; rigid
suffix or stored-value conflicts retain E0301. Written binding annotations are
elaborated before their initializer: a standalone annotation owns a real root,
while a binding inside static execution inherits the active root. Retention
consumes the resulting witness. Exact parsing spends implementation work only.

Finite ordinary reification emits explicit formats and a separate unary sign;
non-finite values use the sealed constant pool. Normalized static/type arguments
use a temporary private committed-float carrier containing width and exact bits,
with strict decoding and no pool-index dependency. Type-argument NaNs are
canonicalized only at that identity boundary. Public source and owned ASTs reject
the private carrier, and ordinary typing/lowering consume it as an already typed
value. `REFACTORING.md` records replacing this bridge with a typed normalized node.

Thirteen frontend/Core groups cover exact representation, both layouts, actual
default and label slots, return/aggregate contexts, quota and panic ordering,
stored-value negatives, generic NI, owned-AST injection, and portable NaN/zero
identity through fresh/edited sessions and independent effect/foreign normalizers.
Five CLI groups cover four native execution sources and a diagnostic group.
Both targets pass the new suites; the related Windows integration run passes
100 tests. Logs are `target/static-numeric-source*.log`,
`target/static-numeric-native-{windows,linux}.log` and
`target/static-numeric-regressions.log`.

## Closed static Result flow

The proved subset and sealed static-to-runtime receipt contract are documented in
[`STATIC_RESULTS.md`](STATIC_RESULTS.md). Universal definition checking is separate
from actual static evaluation: a successful evaluated path cannot excuse an
unchecked producer on another normal path. Publication preserves producer identity
and reached-inspection causes; ordinary clones create their usual fresh duties.
Uncovered Result transfer and collection/callback shapes remain explicitly NI.

## Immutable static loops and lexical control

Four finite programs previously returned static-evaluation NI: an unmarked meta
`loop { last 7 }`, a `for` that uses `next` and returns its first positive element,
a false `while`, and a type computation that leaves a loop with `type<T>`. The
original sources and before JSON/time reports remain in
`target/static-{loop-last,for-return,while-false,type-loop}-before.*`. Their exact
bytes are also retained as CLI fixtures; native wrappers append an ordinary
assertion entry without changing those original files.

The evaluator now executes `loop`, `while`, `for`, `next`, `last`, and return
through private lexical loop frames. A new body entry creates a fresh declaration
EnvironmentId after binding the iteration element. Values and declaration maps
restore on normal completion, next, last, return, tail handoff and failure.
Returned local helpers keep their selected iteration's immutable environment.
Named, anonymous and type invocation isolate loop targets, so a helper cannot
break or continue a caller's loop. Written caller arguments retain their own
lexical transfers; defaults and callee bodies use the callee's boundary.

Array sources run in index order and Maps in first-insertion order. Direct integer
ranges use a lazy cursor that preserves the selected endpoint format. An inclusive
maximum endpoint is yielded once and followed by a terminal test, without an
overflowing increment. There is no implicit String or iterator-Source iteration.
First-class range values, Set/window symbolic constructors and mutable meta locals
remain outside this implementation checkpoint. No mutable StaticValue store or
new public value/constant-pool interface was introduced.

Each unconditional loop body entry consumes one existing LoopIteration event.
While consumes one before every condition test; for consumes one before every
next-element test, including the final unsuccessful test. Next cannot bypass the
next event. Last and return exit without another terminal test. Helper/callback
entries retain their existing charges; syntax, proof work and environment creation
remain implementation work. For example, a meta function traversing two entries
with no callback needs four events: one function entry and three next tests.

Static typing checks unused definitions and unselected source branches. Reachable
last values have one common loop result type; while/for last values must be unit.
A last operand receives that loop's expected numeric context, while return uses
the containing callable's result context. Committed values and literal suffixes
retain their selected types. Normal iteration and last transfer immutable handles
without copying their collection identities or changing existing ConstantPool
nodes; native regression verifies sharing and ordinary clone isolation.

Halt certification remains independent of evaluation and its quota. The static
termination visitor recognizes proved first-iteration exits, false conditions,
and finite collection/bounded-range iteration with finite per-element dependencies.
It checks control transfers inside strict aggregate operands, type arguments and
short-circuit expressions. A skipped last or hidden next cannot certify a cycle.
Unproved halt cycles retain E0820; evaluated unmarked infinite loops exhaust their
language events with E0811.

Universal Result loop checking and the floating reception proof correction are
described in `STATIC_RESULTS.md`. Neither the one actual evaluated path nor a
rounded value's original literal spelling supplies an absent universal proof.
Windows and Linux pass the eight Source/Core loop groups, nine universal Result-loop
groups, eighteen existing Result groups, thirteen contextual numeric groups, and
six new CLI loop groups. The related new/old Result CLI suites and finite recursive
clone harnesses also pass on both hosts, as do the selected compiler/CLI Clippy
gates. Logs are `target/static-loop-foundation-{source-windows-v2,native-windows-v1,native-linux-v1,clippy-windows,clippy-linux}.log`
and `target/static-result-loops-linux-v1.log`. These targeted results do not
replace a full workspace/corpus snapshot.

A separate memory-boundary probe exposed a real environment-retention fault. A
loop with a fresh local declaration group and a captured 1 MiB immutable string
retained a deep copy per iteration without charging the copied bytes. The legal
source `target/static-loop-large-capture-v2-before.ril` hit the verified 512 MiB
job limit/monitor after 499 ms, with peak committed memory 529821696 bytes and no
language verdict. Its original source and failed bounded report remain unchanged;
the failure is not counted as E0811, NI or a successful evaluation.

Owned environment copies now require admission from the existing interpreter
work allowance before cloning or retaining the snapshot. String/byte and bigint
payload sizes, owned syntax, captured lambda/view environments and copied map
keys contribute to that cost. Arc collection payloads contribute their handle
cost; admission does not unfold their reachable graph. Named callable captures
remain EnvironmentIds and do not recursively expand the environment arena.
The cost walk has its own nesting/delegation bounds and returns explicit NI when
it cannot finish. These are implementation limits, separate from language event
quotas, lexical identity and the independently checked halt obligation.

| Owned copy/retention entrance | Admission |
| --- | --- |
| Callable/type/transform save and restore | `capture_environment`, `copy_environment`; restoration moves the admitted snapshot |
| Selected declaration or global default environment | `declaration_environment` |
| Fresh block group and late local binding refresh | `enter_block`, `refresh_local_functions` before arena retention |
| Values-only snapshots and repeated pattern/default restoration | `snapshot_values`, `copy_values` |
| Callable-view dependency capture | `capture_dependencies`, charging only selected owned entries |
| Static-name/callable lookup, pattern-name binding, global publication, for-cursor elements and callback arguments | `copy_static_value`, `copy_static_callable` |
| Owned named-function or lambda syntax retained for evaluation | `clone_work::function`, `clone_work::expression` |

Fresh EnvironmentIds and all language event charges are unchanged. The same
original 1 MiB source now returns explicit work-allowance NI under a preinstalled
512 MiB Windows job in 413 ms; the conservative job peak is 67489792 bytes and
includes its dedicated PowerShell helper. With language quota 1 it instead
returns E0811 before the first LoopIteration, in 221 ms with peak 67235840 bytes.
Reports are `target/static-loop-large-capture-v2-{after,short-after}-bounded.json`.
Under the same 512 MiB/20-second Linux limit, the default and quota-1 runs both
finish in 0.20 seconds, with maximum RSS 38244 and 36836 KiB respectively; their
ordinary exit codes are 2 (NI) and 1 (E0811). Raw JSON, time and exit evidence is
`target/static-loop-large-capture-v2-{default,short}-after-linux-v2.*`.
The durable independent regression is `ril-cli --test static_capture_limits`;
it requires complete JSON and ordinary exits under 512 MiB/20 seconds, and never
counts a timeout, signal or empty output as success. The compiler's separate
shared binary Arc graph test verifies that cheap snapshots do not unfold sharing.
These targeted checks do not establish a global memory bound for all compiler
phases or every static expression.

At this memory-fix checkpoint, both hosts pass 360 compiler unit tests with the
explicit full execution-oracle matrix still ignored, the 49 loop/Result/numeric
source groups, and 46 existing application/budget/tail/type-tail groups. Both
also pass 23 selected CLI groups (the bounded capture regression, six loop,
five Result-loop, five existing Result and six tail-call groups), with actual
native execution where those suites require it. Selected compiler/CLI Clippy
gates pass with warnings denied. Evidence is
`target/static-clone-admission-{compiler-windows-v3,final-lib-windows-v1,compiler-linux-v1,cli-windows-v3,cli-linux-v1,clippy-windows-v1,final-cli-clippy-windows-v1,clippy-linux-v1}.log`.

The later closed-local reference publication and lexical-shadowing correction
uses the same constant pool and retains the memory admission gates. Its binding
identity, first-publication order and independent evidence are recorded in
`STATIC_PUBLICATION_BINDINGS.md`.
