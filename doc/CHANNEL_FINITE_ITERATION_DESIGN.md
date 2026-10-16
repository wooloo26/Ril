# Finite channel iteration proof (proposed)

This document proposes the next implementation batch. No field or operation
described here is registered yet. Current repeated business-message operations
still require an iteration-indexed proof and remain NotImplemented.

The first admitted sources should be literal integer ranges and immutable
finite literal arrays, with at most 64 entries. Analyze their actual entries in
order instead of analyzing one representative callback. Each execution creates
its own Result producers, transport outcomes and channel events. A source with
two entries must produce two sends, including when both sends have the same
syntax span and equal payload contents.

The initial body admission should require normal fallthrough on every reached
path. Nested helper calls can return normally; a return or break from the loop,
conditional next, cancellation or resumed cleanup needs a later explicit
iteration-exit proof. Existing conservative analysis remains available outside
the admitted subset. Unknown collections and sender interleavings gain no
permission from the finite source feature.

## Shared source and coverage contract

A proposed iteration group contains these facts:

| Fact | Purpose |
| --- | --- |
| Stable group ID and optional parent iteration ID | Distinguish repeated visits and establish nested coverage without cycles. |
| Actual invocation context and loop expression span | Select the real typed source loop within its callable and activation. A surrounding application span alone is insufficient. |
| Iterable expression observation and frozen value graph | Preserve the actual input, sources, element identities and entry allocation epoch. |
| Claimed finite cardinality | A cached claim only; the independent reader must derive the count from the observed typed source and frozen input. |
| Entry and completion sequence boundaries | Tie all iterations to the actual half-open event interval. Missing completion keeps the proof incomplete. |

Later array callback groups need a separate source kind: the actual builtin
application, callback argument occurrence and evaluated callback target are
distinct from the input observation. A builtin Array::map callee is not the
named callback's callee. The reader must resolve the callback parameter's
selected Named/Lambda value, then bind its entry snapshot to the exact finite
input element. Helpers called inside that callback still use their own
physical call occurrences. The group must not manufacture an ordinary named
source-call token for an implicit callback entry.

Each proposed iteration fact contains:

| Fact | Purpose |
| --- | --- |
| Group ID and zero-based index | Prove exactly one actual entry at each position in the ordered finite source. |
| Bound element snapshot and pattern/source identity | Reconstruct which concrete element the body receives; equal contents do not identify independent producers. |
| Activation and entry allocation epoch | Anchor the body's actual execution and recency transport. |
| Observation execution identity | Distinguish repeated evaluations of one inline expression within the same named/closure invocation. Source span and caller context alone are not sufficient. |
| Event start and end sequences | Include transitive helpers, inspections and cleanup belonging to this entry. |
| Normal completion evidence | Prove that execution proceeds to the next entry; the first batch must not infer this from absence of an explicit abnormal record. |

Channel events and relevant exit receipts refer to their innermost actual
iteration. Existing representative repetition intervals remain a different
fact kind. Presence of an iteration record never grants an inspection receipt,
resource permission or successful transport outcome.

An observation execution identity is not a new permission root, storage cell
or heap independence proof. Outer mutable cells, ambient aliases and captured
roots remain the same participants across entries. Allocations and retained
values still follow their actual recency/escape history. Assigning a new
iteration identity must not locally discharge an escaped write obligation or
make two reachable objects disjoint.

## Independent reconstruction

The reader starts from the real typed loop and its iterable observation. It
independently derives the finite ordered input, then checks that entry indices
are exactly `0..count`, with no duplicates, gaps or reordered intervals. Every
actual operation inside the source loop must be covered by the correct entry,
including operations inside called helpers. Each source operation observation
must retain its physical transport producer and execution context.

The bound pattern values must agree with the observed source element and its
source graph. Proofs cannot substitute one array element for another, turn an
AnyIndex summary into a concrete sequence, or discard Result producers behind
an element. Allocation recency changes transport the complete frozen graph and
producer identities; they do not merge physically distinct sends.

Deleting every iteration record cannot erase the obligation: existing source
loop reconstruction still observes multiple possible entries. Changing a
count, caller selector, source reference or parent edge cannot select a less
demanding proof path. Missing or ambiguous source evidence remains incomplete.

The current reader repeatedly walks the same frozen callable syntax. A later
implementation can index that structural syntax by owner/span and cache its
pure syntactic bounds, charging each lookup against its work budget. Actual
callee selection, input snapshots, callback binding and iteration count still
belong to their individual execution; a span-only cache cannot certify those
facts. This is an optimization proposal, not a larger proof budget.

Coverage removes the multiplicity restriction only for its exact source loop
or callback occurrence and execution. It must not set a global `once` flag that
also hides an uncovered nested loop, another callback, or a repeated caller.

## Producer and replay integration

The checker needs a separate finite-entry path before its existing loop fixed
point. It evaluates the actual iterable once, binds each observed element, and
analyzes the normal body in order while retaining the resulting channel state.
It must not join the entry state back into every exit as if zero entries remained
possible after a proved nonempty iteration.

Root owns the integration with loop Result obligations and normal completion.
The finite path must create one physical producer obligation per actual entry;
the representative loop Result family machinery cannot stand in for those
producers. C owns private channel custody and independent Source coverage.
Public SemanticFacts, Core provenance and mapper registration stay with Root
after this contract is agreed. Native lowering already emits the source loop;
this feature first changes the proof used to authorize that lowering.

The lowering contract must also distinguish physical observation instances
from the shared source expression. Repeated evaluations can have different
producer IDs and known scalar values while the emitted loop body remains one
dynamic source body. Picking the first iteration's constant or branch fact as
the only source fact would be incorrect. Source typing and narrowing need a
consistent representation across all covered entries; Core retains the
per-entry proof identities even when native lowering emits an ordinary loop.

## Acceptance and adversarial gates

Positive native programs should send and inspect zero, one, two and three
messages, exercise each finite element, and demonstrate FIFO order. Existing
two-entry cardinality gap sources must become actual E0720 rejections when the
second physical receive reaches the unchecked send; they must never execute as
negative tests.

Source mutations should delete an entry or all coverage, duplicate or swap an
index, change the source count or element snapshot, merge iteration producers,
relocate an event across intervals, and substitute caller/parent/source
selectors. A separate concrete finite queue model should agree with the
abstract custody on every accepted normal path. Bound exhaustion remains
NotImplemented and never counts as an implemented positive case.
