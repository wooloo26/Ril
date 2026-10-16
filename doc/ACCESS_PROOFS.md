# Historical access evidence

An access footprint describes an observation made while the semantic heap had
a particular allocation history. A NodeId alone is not a permanent concrete
object identity: evaluating a site again moves its prior recent allocation into
an older node, which can represent many objects.

`AccessFact.observed_recency` is the observation's original allocation-history
index. `AccessFact.recency` is the index through which its origins have already
been transported. They are analysis indices, not runtime timestamps. Every
access remains an independent fact through frame cloning, branch merging,
handler propagation and loan-participant normalization. Observations from
different epochs are not deduplicated into one purported observation.

Before consulting the current graph, transport applies exactly the moves after
the fact's current cursor to both its origin set and every conditional origin
alternative. It then advances that cursor. Replaying an already applied move
must not turn a newly observed recent object into old history. Participants,
access modes and source causes remain attached to the same observation.

Each origin also has historical `AccessOwners` evidence. `Known` contains a
nonempty set of the owners represented at the time of the access; `Unknown`
means the available evidence is incomplete. Missing entries and empty Known
sets are treated as Unknown. When transport merges two observed origins, their
known owner sets are unioned, and Unknown absorbs every other alternative.
No owner is recovered from the later heap just to fill a missing proof.

A callback may omit an access from its outside footprint only when every
observed owner for that origin is proved inside the callback's scope. This is
a statement about the recorded access. It does not refine the current heap
owner, establish singleton identity, restore write permission, close a loan,
release a resource or prove escape safety. Current heap ownership joins must
independently enclose every allocation represented by an older node.

Core `ConditionalAccess` exposes these facts as `observed_allocation_epoch`,
`allocation_epoch`, `origin_owners`, conditional origins, participants, paths
and causes. A hover should distinguish historical access ownership from current
object ownership and should show unknown or multiple owners explicitly.
It must not describe MayMany history as one object merely because a historical
access had one known owner.

The executable semantic consumers normalize accesses before disjointness,
temporary-loan exclusivity, callback locality and invocation-summary checks.
The Core mapping retains the same evidence and is covered by an independent
mapping regression. Core provenance remains inspectable evidence; constructing
it directly does not create a VerifiedProgram. The compiler does not yet have
one independent replay validator covering every relation, root and escape
judgment. In particular, historical disjointness must not be reconstructed from
a later coarser heap alone.

Source regressions are in `crates/ril-compiler/tests/parallel_recency.rs` and
`binary_recency.rs`; concrete owner-history and per-observation transport oracles
are in `sema/facts.rs`. Native tests execute only disjoint positive sources.
The same-origin racing counterexamples are checked for E0619 and never run.

## Solved structure validation

`sema::validate::solved_facts` is a separate pass over the solved SemanticFacts.
It returns `ValidatedStructure` or typed issues with available source spans and
causes. The token means only that this pass's structural equations hold. It is
not a permission proof and does not replace the earlier semantic checks.

The pass cross-checks origin references, heap edges against the stored-field
table, root identities against binding identities, loan parents, cause IDs and
their parent ordering, Boolean-condition references and formal pivots. It rejects
directly contradictory unconditional equality/disjointness, invalid summary
multiplicity, malformed allocation transitions, missing callback evidence and
unresolved Parallel termination. Concurrent scope/task references must exist;
Fork and Join require a task, and a task cannot be its own scope. Resource kind,
ownership, transfer and cleanup truth are not reconstructed from those IDs.

Each checked access must have exact origin coverage in every conditional
alternative and in its owner table. Known owners must be nonempty and refer to
registered scopes; Unknown remains explicit. Its observation epoch cannot be
later than its current epoch, and its current epoch must equal the complete
analysis allocation-history length. This last check establishes canonical
transport state, not that the earlier transport was semantically correct.

`SemanticFacts.allocation_history` is copied from the checker's actual transition
sequence. `allocated_scopes` comes from its continuous scope allocator, including
global scope zero. It is not inferred from the graph being checked. The MAX
formal sentinel is absent from that registry and is admitted only in explicit
formal graph/access positions. It is never a general scope-existence exemption.

Normal compiler diagnostics retain priority. The verification boundary now
runs this pass only after the preceding semantic checks would otherwise accept;
structural failure produces NI with the specific issue kind and location, not
an invented language rejection. Missing material within this pass's declared
scope cannot default to success.

## Material still required for independent history replay

The current access record has its original epoch but no immutable original
origin/choice snapshot. The current allocation log records relocation pairs,
not complete before/after ownership and allocation-birth observations. Thus this
pass cannot replay historical ownership truth or certify every relocation by
recomputing it from independent original data.

A later replay layer needs an immutable observation record with its original
origins, conditional alternatives, owner alternatives, mode, participants,
cause, lexical owner and actual invocation identity. Allocation events must
retain the prior recent and older identities, their owners and multiplicities,
the new allocation, and the scope-ancestry material used for an ownership join.
Node births need an explicit epoch as well. The replay implementation must be
independent of the production transport helper.

Loan normalization and removal of callback-local origins also need explicit
derivation records. A boundary must identify every actual access it consumed,
including accesses omitted because they were local; an empty outside footprint
alone cannot prove there were no omitted outside accesses. Historical
disjointness needs a frozen boundary graph or a complete typed relation witness.
Current may-graphs can merge distinct older objects and cannot supply that
historical proof after the fact. Missing replay material must keep that future
proof boundary unresolved; `ValidatedStructure` cannot substitute for it.

## Closure conditional footprints

`CLOSURE_EXCLUSIVITY.md` describes the separate per-object conditional closure
coverage layer. Its check snapshots preserve the observed nodes and queried
relations at the access check epoch, before local invocation loans are
normalized. The Core mapping retains both observation and check epochs and
historical owners rather than reconstructing the footprint from the final
coarse heap. Its certificate validation checks actual-object coverage and
frozen-record consistency; it does not extend `ValidatedStructure` into an
independent historical permission proof.
