# Conditional closure exclusivity

A closure signature probe supplies hypothetical arguments. Its captured source
and mutable formal can overlap without proving that any real invocation is
invalid. Conversely, type checking the probe is not permission to invoke that
closure with arbitrary aliases. The old `checked_closures` set only records type
coverage; it cannot discharge these alias conditions.

The checker now freezes each probe or actual invocation's access footprint
before projecting local parameter loans back to their caller participants.
`ClosureCheckId`, `ClosureObjectId`, and the shared `ClosureInvocationId` identify
the check, actual semantic object, and invocation separately. The record keeps
the lexical `ClosureSiteId`, named/closure/default creation ancestry, invocation
kind and completion, observation/current allocation epochs, historical owner
alternatives, access participants and paths, queried relations and observed
nodes. Diagnostic spans are locations, not identities.

An independent pairwise predicate reconstructs the read/write and write/write
conditions from those frozen records. Unknown relations leave a condition.
Each successful real call must have its own complete, unconditional check.
Actual conflicts use E0524/E0523, including a conflicting sibling object or a
later conflicting invocation after an earlier successful call. Signature probes
keep their original conditions; a `Discharged` status references the exact calls
or explicit discard receipts and never changes the probe to `Proved`.

## Closed factory subset

A private, directly called named factory can return a conditional closure when
all actual creator instances and all objects created at that lexical site are
covered. Matching uses canonical definition IDs, exact evaluated call events,
references, dynamic parent chains and creation IDs. Extracted factories, public
exposure, unknown or recursive creator contexts, uninstantiated factories,
uncovered sibling objects, and incomplete or failed calls retain NI. A completed
budget-validation traversal is not an actual-call or zero-execution witness.
The current subset does not infer termination or absence of accesses from a
missing completed body.

An explicit terminated expression can instead discard its newly created direct
closure result. This deliberately narrow receipt stores the complete evaluated
Value graph, the newly created object interval, named-call interval, lexical
owner, dynamic named/closure ancestry and allocation epoch. The creator must
belong to that exact evaluation's call ancestry. The object must have no actual
calls needing an unresolved check and no unclosed returned/stored exposure.
For example, `make(cell);` can discharge future-call conditions, while storing
the same object outside the factory before returning it prevents that discharge.
A reference to an existing binding, wildcard binding, complex carrier or general
dead-code argument is not a discard receipt in this subset. Creation-time
capability, capture, loan, copy and Result obligations are unchanged.

## Final consistency and Core evidence

The finalizer records the object-to-calls and template-to-objects certificate,
with discarded objects separately identified. Before Core lowering, the domain
validator reconstructs this certificate from complete facts and compares it to
the stored certificate. It validates one check per completed invocation,
creation links, frozen origin/owner coverage, choice coverage, epochs and queried
relation endpoints. Deleting probe records cannot create a vacuous empty proof.
Missing, cyclic, inconsistent or incomplete evidence fails closed with NI.

Core retains invocation, check, exposure, discard and certificate tables using
the same typed identities and the existing provenance origin mapping. The
tables are available for later explanation/hover consumers. They do not grant
authority to externally constructed IR. Recomputing conditions checks this
closure domain's evidence consistency; it is not an independent proof of the
producer's historical relation truth or full allocation-history replay. The
remaining replay material is described in `ACCESS_PROOFS.md`.

The concrete oracle enumerates 216 object/field assignments and compares the
conditions against independently computed storage collisions. Source and Core
mutation tests cover aliasing, multiple actual objects and generic instances,
uninvoked/public/extracted/stored objects, creation-specific discards, missing
checks, missing snapshots, missing coverage and cyclic dynamic ancestry. Native
tests execute legal disjoint calls and repeated object use; conflicting sources
are checked only.

The separately identified maker-loan false positive was closed in the subsequent
invocation-loan batch: `INVOCATION_LOANS.md` describes its source, explicit loan
end evidence and retained active-parent checks. Conditional closure coverage
itself does not grant retained authority or normalize those loan identities.
