# Static generic result contexts: integration contract

The return-context batch is implemented and verified on Windows MSVC x86_64
and Linux GNU x86_64. The current v30 component run on each host passes 679
Rust tests across 25 targets: 484 library and 195 Source integration tests,
with one explicit pre-existing ignored library test. Its compiler all-target
Clippy gate passes with `-D warnings`. The Source results are recorded in
`target/const-int-and-dependent-bound-full-source-windows-v30.log` and
`target/const-int-and-dependent-bound-full-source-linux-v30.log`.
The earlier v21 checkpoint (637 passes) remains historical evidence.
The frozen v9 `E0344` observations remain historical before evidence.

## Evidence and authority

`ResultContext` owns the complete written type syntax, its purely normalized
source syntax, an admitted immutable `Arc<BoundEnvironment>` from the lexical
site, its ordinary `Ty`, and an optional genuine closed `SourceTypeWitness`.
Construction stays inside the Typer's source-backed helpers: original contexts
use `result_context`, projections retain that lexical source, and Optional
lifting only wraps the existing context. An open `[]U` keeps the registered
caller's `StaticBinderId`; it has no closed witness. All syntax/environment
copies use the existing finite admission and implementation-work budget.

The context constrains Type parameters. It contains no value tags, objects,
allocation regions, Result producers, inspected flags, participants, permission
roots, freshness, or escape facts. Its written syntax is retained separately
for ordinary receiving. Input-selected callable descriptors are never replaced
by the context's labels or defaults during inference.

The implementation retains NI for same-declaration unresolved rigid result selection,
unrepresented composite open Type candidates, and unavailable lexical alias
meaning. Result-context inference still selects Type parameters only. The
separate v30 scalar `n: int` path preserves genuine const IDs in this same
frozen lexical environment; it does not infer a value from an expected ordinary
type. Dependent const dimensions, other Meta value sorts, static keys and
higher kinds remain NI. Existing
numeric-result guards remain until their own complete numeric preparation is
proved; adding a result context does not certify a stored unrounded fact.

Computed fixed dimensions normalize only a written length expression's existing
static integer proof. They never come from `Ty::Array` storage lengths or
backing counts. The original written annotation remains available to actual
receiving and its language budget root. Alias metadata is read only from an
existing exact `TypeInstanceKey`, including the canonical declaration name,
captured environment and complete arguments. A cache miss retains the original
name for the existing pure alias normalizer or NI; it never evaluates an alias
definition's free values in the caller.

## Exact private interface

The module under `typing::applications` re-exports the opaque `ResultContext`
with visibility `pub(in crate::static_eval)` and provides:

```rust
TypeApplication<'a> {
    // Existing arguments, plan, captured/caller environments and real instance.
    expected: Option<&'a ResultContext>,
}

Typer::result_context(
    &self, written: &TypeExpr, lexical: &BoundEnvironment,
) -> Result<ResultContext>

Typer::named_application_scope_at(
    &self, function: &Function, explicit: &[TypeExpr], arguments: &[Argument],
    env: &mut Env, expected: ExpectedResult<'_>, instance: u64,
) -> Result<(BoundEnvironment, Vec<Ty>)>

ExpectedResult<'a> {
    ordinary: Option<&'a Ty>,
    source: Option<&'a ResultContext>,
}

Typer::project_result_context(
    &self, context: &ResultContext, projection: ResultProjection,
) -> Result<Option<ResultContext>>

Typer::optional_result_context(
    &self, context: &ResultContext,
) -> Result<ResultContext>
```

`ResultProjection` has `ArrayElement`, `Tuple(usize)`, `Record(String)`,
`MapKey`, `MapValue`, `OptionalPayload`, `ResultOk`, and `ResultError`.
Projection follows the actual full source kind and retains the frozen lexical
environment. It does not use the receiving mask's transparent `Immut` helper.
The context exposes read-only `ordinary`, `written`, and `closed_schema`
accessors to the private static-evaluation subtree.

The `ExpectedResult::ordinary` field retains the existing numeric/construction
hint. It cannot synthesize `ResultContext` or a source witness. Its `source`
field transports the independently proved context; call sites without written
source use `None` there. The wrapper and both independent Result-flow consumers
retain their original fields and selection priority.

Complete-source queries also need an expectation-aware helper:

```rust
Typer::expression_source_schema_expected(
    &self, expression: &Expr, actual: &Ty, env: &Env,
    caller: &BoundEnvironment, result_context: Option<&ResultContext>,
    depth: usize,
) -> Result<Option<Arc<SourceTypeWitness>>>
```

The existing source-query method remains a wrapper with `None`. Its Call arm
repeats named selection with the same frozen context used by expression typing.
Otherwise an already typed `empty()` would fail again while querying its
schema. The queried source remains the instantiated declaration's return
source; it must not become the expected receiving witness. Projections without
a complete base context retain their existing inference limits.

`check_function_application` keeps explicit/input selection first, including
its existing dependency discovery. It then calls
`infer_application_result_context`, repeats bound-dependency discovery, solves
the shared row equations, checks all input roots, and diagnoses unresolved
parameters. Finally `check_application_result_context` checks the declared
instantiated return source against the full context. It does not ascribe a
value or apply a callable view.

The inference walk snapshots the still-missing callee-owned binder IDs.
Repeated occurrences of a binder selected by this context must agree. Already
selected and captured binders are skipped. A dynamic declared return array
remains dynamic: `[]T` with expected `[0][2]int` may select `T = [2]int`, but
the subsequent root receiving check rejects its dynamic outer shell. A known
fixed source may enter a dynamic receiving type where the existing receiving
rules already permit it; that does not replace the selected Type.

## Typer call sites

`expr_result_expected(expr, env, expected_ty, result_context)` and its block
helper retain the existing `expr_expected`/block helpers as wrappers with no
complete source context. Contexts are explicit arguments and cannot leak from
an ambient mutable current-expression context into unrelated operands.

| Producer of a written expectation | Required use |
| --- | --- |
| `verify_binding` and local `StmtKind::Binding` | Construct context from `binding.ty` before typing the initializer; preserve the existing receiving afterward. |
| `contexts::collect` typed local binding | Use the same context-aware typing/source queries while collecting lexical definition environments. |
| `verify` function body and explicit lambda return | Freeze the declaration's lexical scope and return syntax; give the body tail and return operand that context. |
| `verify_defaults` | A default argument's written formal type supplies its own complete context. |
| Typed record constructor (`ExprKind::Record::ty`) | Use the constructor's written source for its member contexts before existing receiving. The current AST has no `TypeAnnotation` expression variant. |
| `named_application_scope_at` argument loop | Derive a child context from the declared/selected formal syntax, with its real scope, for nested calls in that argument. |
| Array, tuple, record, map and constructor operands | Project full source child syntax; keep ordinary numeric contexts and fresh-constructor receiving distinct. |
| `if`, `match`, final block expression | Forward the same expression-result context to each alternative/tail. Other statements receive none. |
| `return` inside loops/blocks | Use the owning callable's frozen return context, independent of the current expression context. A nested callable installs its own return context. |

The Typer keeps a private optional frozen return context alongside its existing
`return_type`. Callable boundaries install their own context. `??` lifts a full
result context into an Optional type context for its left operand; this adds
no `Some` fact. Its right operand uses the proved left payload source where
available. Both source queries retain the same contexts. Loop `last` uses its
own loop's context, while `return` uses its callable's frozen context. Callee expressions,
tests, index operands and unrelated arithmetic operands must not inherit the
whole result's source schema.

## Actual evaluator call sites

The optional context reaches
`typing::runtime_applications::infer_named_type_arguments`. Its sibling
`expected_result_context(evaluator, written, caller_environment)` builds it
using the already existing pure `selected_environment` conversion. No evaluator
final actual values participate in a universal proof.

`Evaluator::expression_inner` already receives `Option<&TypeExpr>` and
`numeric_arguments` already projects raw parameter/constructor syntax to its
operand evaluations. At `ExprKind::Call`, capture the caller environment and
construct the result context before changing environments. After evaluating
arguments exactly once, prepare a generic `StaticCallable::Named` through the
shared solver with that context and the real checked activation counter. Then
tail/invoke the resulting `Prepared` callable. This avoids adding a context
field to `TailInvocation` and preserves the existing raw/resolved signatures.

The non-context invocation/callback path passes `None`; its Named fallback can
continue to infer from complete actual arguments. Preparation at the call site
must increment the activation counter once, not again inside Prepared dispatch.
It must not ascribe the result to the expected syntax: the existing declared
return and outer receiving contracts still perform those operations.

## Root-owned independent Result-flow integration

Root owns all `result_flow*` changes. The shared contract needed from this batch
is the opaque clonable `ResultContext` and the named helper's extra argument.

| Current Root call site | Required context plumbing |
| --- | --- |
| Module meta binding verification (`engine.expr` before `receive_annotation`) | Build the context from the annotation and `state.bound_scope` before `expr_expected`; receiving stays afterward. |
| `Engine::block` local binding and last expression | Same annotation handling; only the last unterminated expression inherits the block result context. |
| `Engine::expr` / `expr_inner` | Add expectation-aware counterparts; current wrappers pass none. Project full contexts for legitimate child receiving positions. The post-transfer `expression_source` query forwards that same context through the Typer source-query helper. |
| `ExprKind::Call` and `Engine::invoke` / Named dispatch | Preserve the expression's context through argument evaluation, then pass it to `named_application_scope_at` with the real new owner ID. Arguments get their own formal contexts. |
| Named/lambda bodies and `ControlOperation::Return` | Install an immutable callable return context under the declaration's selected scope; save/restore it with the caller frame. A return inside a loop uses that frame context. |
| Parameter default expression | Supply that parameter's complete formal source before evaluation, then keep the original receiving afterward. |

Root prepares a real Named call's owner/scope once before evaluating its
arguments. Each argument receives its selected formal source according to the
actual `StaticApplicationPlan`; invocation reuses that same prepared owner and
scope. This is needed for `count(empty())` and avoids preparing a second
activation after evaluating the arguments. Callable return contexts are saved
and restored on the Engine frame; State, Value and producer identities are not
changed by the new context plumbing.

Context plumbing changes no producer identity, inspected flag, optional choice,
tag constraint, escape edge, or callable target. `Value.source_type` continues
to describe the proved expression/declared result, not the desired receiver.
Actual `None` must not remove a fresh local producer created and discarded on
the definition's universal `Some` path. Borrowed parameter producers retain
their caller ownership; a callee is not required to inspect every borrowed
Result merely because the formal type can contain one.
Returning a Result through `retain<T,U>` keeps the caller's original producer;
selecting `U` from `[]int` does not inspect the returned `T`.

## Verified Source and native cases

The positive fixture covers `[]int`, complete empty nested dimensions,
registered open caller `U`, branches, a typed formal argument, and a real
callable target received through an explicit renamed view. `result_transfer`
requires the original producer to remain inspectable after contextual inference.

Negative fixtures require:

- `reject_dynamic_outer`: `E0301` for dynamic `[]T` received as `[0][2]int`.
- `reject_explicit_selection`: `E0301` without replacing explicit `T = int`.
- `reject_input_selection`: `E0301` without replacing a declared dynamic input.
- `reject_callable_mode`: retain the independent callback-mode NI boundary;
  this batch must not make it accept by erasing the actual writable formal.
  When that separate mode proof is implemented, the mismatch needs `E0301`.
- `reject_view_default`: `E0314` after the explicit view erases defaults.
- `reject_result_inspection`: `E0720` for the original uninspected producer.
- `reject_universal_some`: `E0720` for a fresh local Result on the `Some` branch,
  independently of the actual `None` argument.

The v30 Source gates pass all five `static_result_context` groups and all five
`static_result_context_flow` groups on both hosts, including pointer32 and
pointer64 checks and Core lowering for positives. Pure binder/schema tests and
the existing numeric-budget and callable-interface regressions pass in that
same snapshot. The additional non-authorizing scoped cases remain Source safety
regressions; their NI outcomes are not native or language-acceptance results.

The fresh native reports are
`target/const-int-and-dependent-bound-native-windows-v30-report.json`
and
`target/const-int-and-dependent-bound-native-linux-v30-report.json`.
Each host actually executes all 17 test executables, with 22 passing Rust
tests, covering 49 distinct positive Ril source programs and 53 entry jobs.
All 19 artifact hashes (CLI, runtime and 17 test executables) agree before and
after execution. The context CLI target runs three programs, including the
computed alias and original Result producer transfer; the flow target runs
three programs covering return/fallback/constructor contexts, containers, loops
and lexical shadowing. No ignored, filtered, empty or unavailable native run is
counted as passed.

An unannotated lambda return is still not inferred automatically from an
expected callable return type. Scalar `n: int` Meta function generics now have
their own selection path and pass the v30 native fixture's seven values on both
hosts. Their eight pure tests and six Source groups are included in this same
checkpoint, together with four independent const Result-flow Source groups
and its native fixture. Broader Meta value sorts, symbolic `[n]T`, static keys,
higher kinds, first-class generic callable Source typing, unproved recursive
summaries and composite open Type selections remain NI. The const unknown-branch
regression allows NI or `E0720` and therefore is not itself a completed negative
language result. These batch results do not claim full language
conformance or completion of the compiler.

The v9 frozen Windows CLI parsed all nine prepared fixtures without lexer or
parser diagnostics. The positive and transfer fixtures reproduce `E0344`, as
do the newly contextual negative paths; explicit selection already rejects
with `E0301`. The callback-mode fixture reaches the independent NI boundary
`static callback data parameter mode typing proof`. The observations are in
`target/static-result-context-draft-*-before-windows-v9.json`; they are before
evidence, not current acceptance results. The original borrowed-Result-only
`discard(None)` example was corrected to create a fresh local producer in the
`Some` branch; borrowed producer ownership remains with the caller. Early
global callable publication and computed tuple-projection drafts were also
separated from this batch's local callable-interface and ordinary tuple-access
tests, with their original sources retained in `target/`.

## Completed lint-only interface and control representation changes

Actual v28 Clippy diagnostics required private parameter packing and smaller
control payloads. `ExpectedResult` is now implemented in
`named_application_scope_at`; its entry destructures the two original fields.
`ApplicationInference` and `ResultInference` group immutable recursive-walk
inputs, and `CoalescingOperands` groups the lazy fallback operands. The walks
retain their original caller IDs, pending-binder snapshot, depth/work charges
and mutation order. `TypeApplication`, expression typing and source-query
authority are unchanged.

`Failure::Return` and loop `Exit::Last` box their moved `StaticValue` payloads;
the range cursor boxes its original five-field state. Small loop transfers
remain inline. Return unboxing moves the same value/producer into the original
completion path. Compile-time size assertions and the actual v30 compiler
all-target Clippy runs confirm bounded error/control representations, without
lint `allow`s, language-budget changes, capture changes or reordered outcomes.
The successful logs are
`target/const-int-and-dependent-bound-clippy-windows-v30.log` and
`target/const-int-and-dependent-bound-clippy-linux-v30.log`.

The v31 whole-workspace format check passes after formatting-only edits. The
v30 artifact reports remain the execution evidence; no v31 semantic rebuild or
native rerun is claimed. These changes do not start the later overall compiler
refactor requested after implementation and commit.
