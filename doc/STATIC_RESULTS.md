# Static Result inspection and publication

This is a closed implementation subset, not complete static Result support.
Static typing, universal control-flow verification, actual evaluation and runtime
publication each retain their own proof boundary.

## Producer identity and control flow

Each evaluated Prelude `Ok` or `Err` creates a typed producer identity. Aliasing
preserves that identity; another constructor with equal contents creates another
producer. A reached constructor test observes that producer's tag. Payload tests
run only after its outer tag matches, so an outer `Some(_)` or `Ok(_)` does not
inspect a nested Result. Equality is not tag inspection.

`static_eval/result_flow.rs` checks meta definitions independently of their actual
execution. Every normal path must inspect a locally produced Result or transfer
it in the returned value. Panic paths do not become normal exits. Parameters and
captured values preserve their existing producers; creating an inspector closure
does not execute its body. Defaults have separate omitted and supplied paths.
The analysis preserves correlations between the same boolean input and repeated
tag tests, including aliases and negation. Unproved arithmetic path feasibility
does not turn a potentially impossible path into a language rejection: it remains
an implementation limitation when its Result coverage cannot be established.

The finite domain covers known calls and anonymous callbacks, exact immutable
tuples, records and constructed arrays/maps, ordinary parameter/return transfer,
constructor patterns, short-circuit conditions and explicit abnormal exits.
Implementation work and path limits report NI and do not consume language static
budget events. Unknown callbacks, recursion, unquantified Result collections,
local named captured environments, escaping Result-capturing closures, and Result
flow through unsupported type computations remain NI. Actual execution of one
branch never substitutes for checking a definition's other normal branches.

## Immutable loop exits

`result_flow_loops.rs` interprets loop control separately from actual execution.
Each loop body has a lexical target. Conditions and sources run in the enclosing
scope; invocation and anonymous-definition checking isolate their loop targets.
`last` transfers its value from the nearest loop, `next` continues only that
loop, and `return` or an abnormal exit remains a callable exit. Every iteration
restores its outer lexical bindings without removing producer duties.

Known arrays and maps visit their exact members, including aliasing and
first-insertion order. A map overwrite keeps the displaced Result's obligation.
Direct ranges with exact i128-carrier integer endpoints use a lazy proof cursor;
inclusive maximum endpoints do not require an overflowing extra increment.
Empty collections and false conditions retain the zero-iteration normal path.
Early `last` does not inspect unvisited members.

For `loop` and `while`, a worklist visits complete abstract states. Revisiting
the same environment, duties, tag/boolean constraints and ownership closes a
control-flow cycle only after its successors and normal exits have been covered.
Infinite paths do not create normal exits. The 512-state implementation allowance
and existing proof-work allowance report NI, independently of language budget
events. Unknown collections, nonexact or larger integer proof carriers and loops
requiring quantified producer invariants remain explicit limitations.

Type reception also limits numeric path facts. An integer inference hole selected
as `f32`/`f64` cannot keep its unrounded integer equality evidence. Annotated
containers, explicit record constructors, named/lambda returns and callable views
propagate that restriction. Until the universal domain represents exact IEEE
values, a pending Result on such an uncertain branch remains NI. Actual numeric
evaluation and committed constant graphs retain their existing exact rules.

## Sealed constant receipts

Successful universal checking allows the private static constant pool to seal
an actual inspection receipt. The receipt contains the exact producer and its
production and reached-inspection spans. A pending producer cannot be exported
as an already checked runtime constant; that transfer remains NI. The receipt is
not a user-constructible AST or Core field.

The constant pool maps each producer to one constant node. Equal values from
different producers do not merge. Ordinary constant installation creates a
Result duty with the receipt's cause chain and preserves aliases to that duty.
Container values retain their reachable child duties; only an actual outer
Result has an outer duty. The closed Result type witness also survives export,
including numeric payload representation and the unselected branch's type.

An ordinary clone creates its normal new inspection duties. It does not inherit
the original producer's receipt. Checking one clone element cannot inspect a
different element or an unvisited nested Result. Editing a session discards old
producer receipts along with the old private evaluation pool.

## Validation

`crates/ril-compiler/tests/static_results.rs` covers unused definitions, aliases,
separate equal-valued producers, parameter/return/default paths, closure creation
versus invocation, nested patterns, short circuiting, finite member graphs,
Core node identity and provenance, numeric type witnesses, incremental edits and
constructor resolution. Its independent concrete oracle enumerates 16 combinations
of entry/branch inspections and an abnormal branch, comparing every normal exit.

`crates/ril-cli/tests/static_results.rs` has three native execution groups, one
negative diagnostic group and one explicit NI boundary. Both Windows and Linux
pass those five groups. The original plain `let copied=clone(tuple)` example is
retained: installing tuple child Result metadata fixes its publication proof,
rather than changing it to a different copy operation. Related evaluator, static
numeric and Result regressions remain separate evidence from full workspace or
frozen conformance runs.

`crates/ril-compiler/tests/static_result_loops.rs` adds ten source/Core groups
covering loop/return/abnormal transfers, zero iterations, symbolic conditions,
member aliases, map overwrites, lexical restoration and unknown collections. Its
separate finite oracle enumerates all 16 combinations of collection length 0–3,
inspection and early exit. A saved failing test showed an unrounded integer fact
incorrectly accepting an `f32` branch; seven scalar/container/call forms now
refuse that proof for both ordinary `if` and loop exits. Integer inference holes
retain mathematical values without prematurely selecting target `int`; an
unsuffixed maximum-u64 Result payload also passes in its actual typed context.
Windows and Linux pass these ten groups, eight evaluator-loop groups, and the
existing 18 Result and 13 numeric-context groups
(`target/static-clone-admission-compiler-windows-v3.log` and
`target/static-clone-admission-compiler-linux-v1.log`). The tenth group checks
that deep finite calls stop at the separate universal proof-stack limit with NI,
while shorter calls retain their complete Result exit proof.
The earlier failed construction/fixture logs are retained and are not passes;
Windows and Linux also pass the five new Result-loop CLI groups and the five
existing Result CLI groups, including real native publication/copy duties and
the ordinary-if/loop rounded-float NI cases. Evidence is in
`target/static-loop-foundation-native-{windows,linux}-v1.log`; the selected
compiler/CLI Clippy gates pass on both hosts. These are targeted integration gates,
separate from the retained large-capture memory boundary in STATIC_EVALUATION.md.

## Declaration applications and complete receiving types

The universal Result engine now prepares each real named invocation with the
same pure type-application checker as ordinary static typing. Its activation
identity comes from that invocation's owner allocation. It supplies lexical
source witnesses, including explicit unknown-binding tombstones, and receives
the selected binder and shared-row environment before binding the arguments.
Actual evaluator tags and inspection receipts do not prove a template body.

Generic receiving positions preserve the actual callable target, parameter
labels and defaults, including inside alias wrappers. A written callable type
still introduces its declared view. Raw parameter and result syntax controls
this distinction. Contextual numeric receiving clears an unrounded integer
fact when the selected representation is floating point. Complete source
witnesses accompany annotated formal values and projections; neither a storage
length nor an erased callable type can reconstruct missing source information.

`static_record_bound_results` adds nine compiler groups: known bound fields on
both static layouts, actual caller Result inspection, an uninspected Result in
an open remainder, universal branch coverage, direct and wrapped callable
interfaces/defaults, explicit type arguments, an incremental edit comparison,
and the explicit rounded-float NI boundary. Windows and Linux pass these groups,
the existing 41 static groups, and 407 unit tests with one explicitly ignored
test (`target/static-result-application-root-windows-v4.log`,
`target/static-result-application-root-linux-v4.log`, and the matching Linux
unit gate `target/channel-conditional-context-after-linux-v8.log`). Earlier failing logs
are retained: the new native fixture entry points originally omitted their
required global `ANSWER` capability; the compiler correctly rejected them with
E0510. Their declarations now contain that capability. Four shared positive
fixtures also execute natively on both platforms in
`target/static-bound-result-native-windows-v1.log` and
`target/static-bound-and-channel-static-native-linux-v1.log`. Those four actual
executions are separate from the source rejection and explicit NI safety tests.

Local named capture groups, recursive Result summaries, escaping symbolic
explicit-type callable descriptors, exact floating-point branch proofs and
unquantified collection families still require their own complete proofs.
