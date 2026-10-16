# Ordinary explicit named Type application: proposed direct-call contract

Status: readonly design after v30, unregistered. No production, public scope,
arena, ABI or Cargo change is made. Root's evaluation-receipt contract remains
the owner of its shared interface window.

## Exact current gap

`checker/expressions.rs` handles `ExprKind::Generic` by evaluating the base and
dispatching only to constructor/standard generics. `standard.rs` deliberately
leaves an ordinary `Callable::Named` application NI. The v23 `first<U>`, `count<U>`
and `read<U>` retries therefore did not bind explicit U. Their sources remain
`tests/fixtures/record_bounds/pending/*_explicit.ril`; the inferred versions are
now accepted native regressions, not this gap.

The initial proposed range is an immediate, uniquely resolved named call with
an explicit prefix of ordinary Type arguments. The remaining owned Type/row
arguments may use the existing input/bound solver. Value/key/effect/constructor
sort arguments, escaped applied function values and indirect/multiple targets
need their own contract and stay NI. This first range must not silently accept
`let applied = f<T>; applied(...)` without transport evidence.

## Private prepared input

Resolve type argument syntax in the actual caller environment **before**
`generic_scope(callee)` replaces it. A private prepared input should contain:

| Coordinate | Purpose |
|---|---|
| Original named DefinitionId | Preserve real source ownership; do not clone a function into an invented declaration |
| Physical callee expression / CopyCallEventId and caller InvocationContext | Tie the type arguments to this actual Generic/Call occurrence, including repeated identical spans |
| Ordered explicit prefix with real generic indices | Too many arguments or wrong sorts fail; an omitted suffix is inferred rather than fabricated |
| Frozen caller Type/row identities and selected parent arguments | A caller U remains rigid; the same spelling in the callee cannot substitute for it |
| Full ArgumentKey plus genuine source syntax per selected type | Preserve dimensions, callable modes/qualifications and namespace; retain open binder keys without inventing a closed witness |
| Actual source cause | Extend the existing explanation chain without proving any access |

The direct call's private evaluation result can thread this input alongside its
callee Value and arguments. Initial direct support should not add a new Callable
variant or mutate global function definitions. Generic source layers must still
record their ordinary expression observations/references: skipping a Generic
layer to reach the Name must not weaken direct-call/ancestry replay.

The existing `StaticArgumentWitness` can represent open symbolic selections:
`effect_argument_syntax` uses registered `\0effect-binder:<UID>` tokens, and the
static-argument validator checks both frozen key and syntax. Whether that
existing transport suffices for every new direct-call receipt must be reviewed
at the shared-contract window; missing syntax/key cannot be silently treated as
an explicit argument. A separately stored/escaped application would require
additional receiving/identity transport before acceptance.

## Invocation and independent replay

After entering the genuine callee scope, clear only its owned selections, then
seed the checked explicit prefix. Preserve **unselected source templates** for
input constraints: substituting U into the semantic Ty before recording its
actual input schema would erase the occurrence and can skip full callable/array
identity comparison. Existing/input/bound choices must agree with explicit
choices; no later argument may replace an explicit choice.

Run the existing complete source, field/row, numeric, parameter-mode, loan,
resource/Result and escape checks. An explicit Type argument changes no Value
permission, origins, callable target/environment, default interface or Result
producer. It cannot create new callable defaults for an already restricted view.

Independent replay must locate the real Generic/Call AST in the real caller
owner, verify the physical application event/target, reconstruct each provided
Type argument under that invocation's original caller namespace, and compare
the actual own static-argument row at its genuine index. If a caller U is
selected in an ancestor invocation, follow only that actual ancestry's frozen
arguments. No display-name/span fallback, missing row, captured replacement or
another same-span application's successful choice can stand in.

Numeric preparation needs to receive the same explicit selection before
committing a literal representation. A truly explicit selected instance has a
different source from the current structural-input deferred candidate; merely
lifting the expected-only NI or counting an explicit syntax node is not proof.
The same instance's complete explicit receipt must be consumed before Frozen.

## Minimal proposed ownership window and gate

Likely private changes are `expressions.rs`'s call/callee dispatch, `calls.rs`'s
invocation preparation/selection order, a private prepared-Type helper and
complete source-selection checks retaining raw parameter templates. Independent
explicit-application replay may be a new private validator using the existing
actual AST walk. Public scope/receipt changes, if necessary, belong to Root's
separate review; this document does not register or allocate them.

Start by accepting the three preserved explicit sources with unchanged native
assertions. Add an unused explicit U case, a same-spelled caller/callee U, partial
prefix inference, explicit/input disagreement and a pre-restricted callable
view. Mutation checks should remove/misplace the own static-argument row, change
the explicit type while keeping the same erased Ty, replace caller scope or
application event, and borrow another same-span invocation. Wrong dimensions,
callable modes/qualifications and restored defaults must fail. Source, independent
facts, Core and actual two-platform native execution are separate gates; NI or
an unexecuted adapter is not positive conformance.
