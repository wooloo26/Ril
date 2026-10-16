# Ordinary reference answers after resumption

`resume operand` supplies the operation result, then receives the answer of the
actual protected continuation. These are different types and different values.
The post-resumption suffix runs after that continuation and its body cleanups.
It receives the complete answer Value under ordinary binding reception.

`OrdinaryChecked` admits complete known ordinary reference graphs and aggregates
of those graphs. It neither copies the answer nor grants freshness or writable
authority. Origins, correlated origins, field graphs, permissions, publication,
participants, and pending obligations remain present. A fresh mutable answer
can enter an appropriate mutable binder. An immutable answer stays read-only;
a live answer still needs a lawful live reception. An explicit clone in the
suffix has its ordinary separate copy contract.

The eligibility reader rejects Result, resource, scoped, callable, unresolved
row, generic, and pending-copy constituents. Existing exact identity transport
keeps its separate Result behavior and inspection obligations. Retained abort
reference answers still need a terminal-exit proof; a continuation-answer
certificate does not establish one.

Each actual suffix records a `ResumptionStep` with its handler, operation, fresh
boundary, arm scope, dynamic invocation context, and input/output expression
indices. Its continuation and arm answers use frozen `CopyValueSnapshot`
material: only their reachable nodes, fields, array metadata, and relations.
The snapshot structure is reused for recording, without copy qualification or
permission semantics. Each snapshot retains its own allocation epoch. Current
answers follow subsequent recency moves across helper checking and cleanup;
historical snapshots remain unchanged. Core preserves the allocation history,
epochs, snapshots, and dynamic identities.

Operation receptions record every resolved parameter's mode and optional loan.
Separate `OperationLoanStart` records tie borrowing parameters to their actual
source snapshot, arm scope, boundary, handler, operation, parameter, and dynamic
context. The independent validator reconstructs the required ended set from
the resolved operation and these receptions. Removing all start/end tables
cannot turn a mutable operation into an empty-loan proof. Only ordinary `mut`
operation loans end when resumption starts. Retained `^mut` operation authority
and outer function/callback loans keep their own lifetimes.

A retained ordinary answer references the steps belonging to its own fresh
invocation scope, handler, and operation. Matching another call's span or answer
type cannot replace these records. Fixed retained answer types still agree with
their declaration boundary and use E0614 for incompatibility.

Suffix reads, writes, projections, stored sharing, and cleanup use the ordinary
checks. Derived operation aliases remain invalid after their temporary loan
ends (E0540). Independent captured and ambient paths remain separate from an
outer parameter's active loan, retaining E0523/E0524. Read-only reception cannot
be used to regain a writer (E0520/E0528), and publication still checks surviving
writers (E0535).

When the protected body has actually finished, its private local writers can
otherwise remain marked alive until after the suffix. `ContinuationScopeExit`
records retirement of only this invocation's ordinary answer-reachable locals
in the ending lexical boundary. Parameters, outer locals, ambient roots,
handler and cleanup environments, and potential named or closure captures
remain protected. The validator independently reconstructs that protection
closure from frozen binding and reachable field observations; editing the
recorded protection set cannot authorize retirement.

The scope-exit record preserves the answer's fields, relations, origins,
participants, and permission at its allocation epoch. An already writable
Fresh/Older graph with no surviving writer can regain construction publication
under the existing scoped-exit rule. Read-only paths and immutable child fields
retain their permissions. Current answers follow later recency moves while the
historical scope-exit snapshots remain unchanged. Complex saved control states
conservatively retain their writers until their roots have an independent
enumeration proof.

`non_tail_reference_answers` covers source verification, Core evidence, native
execution, helper recency, reference sharing, fresh mutable answers, retained
invocations, operation loan ends, independent retained authority, and negative
permission/alias/Result cases. Mutation tests remove graph nodes, erase both
loan tables, alter permission evidence, remove steps, and substitute another
call's steps. Legacy identity Result and cleanup suites remain separate gates.
The private-local regression additionally covers an escaping captured writer,
an ambient writer, read-only reception, and a writable aggregate with a
read-only child. Its mutation checks erase the scope certificate or alter
protection, historical liveness, epoch, or answer permission.
