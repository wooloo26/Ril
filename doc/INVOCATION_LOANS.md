# Ending formal loans without losing retained authority

SPEC's parameter-mode table (around lines 3554–3558), shared-step example
(3827–3836), and retained-sharing rules (3930 and 3964–3982) distinguish a
call's borrowing participant from the source authority which can survive it.
`mut` cannot retain a writable path. `^mut` permits retention, and an existing
shared closure and its original object may be mutated sequentially. Invoking
an already shared object does not publish another writer.

Previously, named and anonymous returns normalized the top-level result and
forwarded access footprints, but a captured parameter binding or stored child
could keep its maker's `LoanId`. Two later sequential closure invocations then
looked like simultaneous independent maker loans and produced E0523. The
unchanged example and old diagnostic are saved in
`target/escaping-shared-closure-loans.ril` and
`target/escaping-shared-closure-loans-before.json`.

Each actual local formal loan now has an entry record containing its precise
invocation identity, lexical owner, activation, parameter mode/index, bound
parameters, source Value and origins, original participants and allocation
epoch. A checked invocation ends only the local loan IDs it created. The end
record retains the original parent mapping and an explanation cause. Named
calls, closure calls and productive recursive-summary instantiations use the
same mechanism; operation loans are separate.

The replacement map is transitive only through loans whose invocation has
ended. An active parent loan and every unrelated ambient participant remain
independent. Unknown entries stay unchanged; a cycle does not produce an empty
proof. Empty parent sets preserve the actual source recorded at entry rather
than inventing a new root. The update changes participants of current bindings,
stored Values and all nested result carriers. It does not change origins,
permissions, temporary/scoped flags, captured binding identities, resource
metadata, or Result producers and duties.

Before an access footprint is consumed, ended loan participants are normalized
again. This handles a saved branch/control Value restored after the boundary.
Frozen access/check and invocation snapshots remain historical observations.
The new loan entry/end records explain the subsequent participant projection;
they are not permission to rewrite those observations or to regard another
active loan as ended. Borrowing a closure through a mutable formal continues to
overlay its captured accesses with that formal participant, so two independently
borrowed environments which share storage still conflict.

The independent solved-facts validator checks entry registry/source agreement,
allocated activation and binding membership, actual invocation and lexical
declaration ownership, mutable parameter modes, unique coverage of every
completed mutable invocation parameter, end membership, duplicate ends and
cycles. Deleting both entry and end tables cannot make a mutable invocation
vacuously pass. Core preserves both tables, source facts, typed callable/
invocation identities and cause chains for later trace consumers. This validates
the stated boundary's structure and coverage; it is not full historical graph
replay.

Tests retain the original sequential maker example, original-root interleaving,
marked local closure aliases, returned tuple members, conditional creation,
and distinct captured objects. Negative source checks retain E0523 for active
parameter/capture overlap and independent mutable closure parameters, E0619 for
overlapping Parallel branches, and E0720 for an uninspected Result. Escaping an
ordinary temporary `mut` capture remains the existing explicit NI boundary;
the loan-end fix does not convert it into an accepted retained authority.
Invalid overlapping examples are checked only. Native tests execute only the
legal shared sequence and independently check the conflict source.
