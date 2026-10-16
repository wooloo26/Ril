# Channel Result message obligations

Channel sends and receives use one actual-event ledger for inline operations,
formal endpoint parameters, nested helpers, and captured calls. A send's outer
Result reports transport. On Ok, its ordinary business Result payload becomes
the channel's responsibility; on Err, the original producer remains the
caller's responsibility. Inspecting or returning the outer transport does not
inspect or return its business payload.

The private flow enumerates feasible guarded custody cases. A known queued
receive succeeds and removes its actual message. A failed receive cannot
consume a queued producer or manufacture a successful transfer. Normal caller,
receiver, and scope completion retain every unpaid business duty. A business
Err returned by a scope is ordinary completion; it does not prove cancellation.
Resources, unresolved rows, scoped values, and retained callable environments
remain outside this ordinary message proof.

The public provenance records each actual send/receive, frozen carrier graph,
producer generation, return/inspection receipt, alias, and task order event.
Result producers retain immutable creation owners. Actual ordinary owner
changes have separate frozen ResultTransfer receipts, including reception from
an outside producer. Lexical ancestry alone does not prove a transfer.

Explicit returns and propagation failures preserve their actual guarded flow.
The normal fallthrough receipt applies only to its own paths. Complete records
the union of this invocation's actual exits and supplies no return or inspection
authority. Invocation summaries retain their actual activation and context;
the independent validator reconstructs their message sets from actual events.

Result family aliases convey physical identity. Their Ok/Err formulas are
reconstructed from actual returned members and their guards. They cannot turn
one new family Ok into all old sends succeeding. A complex implicit joined
family without complete member receipts remains NotImplemented.

Successful sends from one task retain their FIFO order. Fork and join events
build task vector clocks before child analysis and after actual completion.
Messages from incomparable sender tasks require an interleaving proof and
currently remain NotImplemented. Analysis visitation order supplies no global
message order. Recency cannot merge distinct live clock identities to invent
happens-before.

Guards are normalized bounded DNF: at most 256 terms and 128 literals per term,
with a 65,536-literal-operation work bound. Incomplete formulas never become
true. The producer also bounds worlds, packets, frozen graphs, and event count;
independent replay bounds its history and cases. Exceeding proof limits retains
the duties and yields NotImplemented.

`channel_message_validation` replays frozen evidence independently of the
checker's ledger and final Result flags. It reconstructs primitive and exit
coverage, actual invocation summaries, producer custody, received message
identity, task causality, and constructor-dependent returned presence. Removing
an entire event/exit table or replacing final flags cannot erase these duties.

Complete production coverage is checked before every send/receive, including a
carrier whose currently visible Result set is empty. A bounded reader follows
the complete frozen Result/Option/variant graph and concrete collection slots.
Finite incoming `Result` trees now retain both typed constructor payloads and
distinct borrowed producers. Their construction is bounded to 256 type nodes
and depth 64. The outer producer is unconditional; a child producer exists only
under the corresponding parent constructor. These symbolic inputs remain read
only and supply no fresh allocation or disjointness proof.

The private ledger and independent replay enumerate conditional producer
presence from the complete frozen carrier. Only producers present in a case
change custody or enter its message packet. Equal producer sets can join their
presence guards, and equal complete custody states can join their case guards.
These joins do not inspect a tag. The physical Result tag and generation have
their own guard identity, separate from transport outcomes and evaluated
booleans. Actual inspection and return receipts are still required for each
present business producer.

Uninstantiated function declarations have separate analysis regions; actual
calls retain their common outer invocation region. Each operation must have
an actual expression observation with its invocation context and physical
transport producer. An incoming application token can describe a surrounding
callback; it does not replace that operation observation. Reachable message
completion and scope exit belong to the same execution region. Independent
declaration probes do not submit physical messages; their actual invocations
retain the caller's scope completion obligation. Moving an event to another
declaration cannot hide its unpaid producers.

Finite incoming `Option<Result<...>>` graphs preserve an independent immutable
Some/None identity and a typed payload witness. The Some case contains the
actual inner producers; the None case contains none. Testing Some/None only
selects presence and does not inspect a Result. Deep clones retain that tag bit
but create new inner Result producers. Inspecting the original cannot pay the
clone's duties. Independent formal parameter paths cannot be identified with
one tag, even when their arena entries, owners, types and causes are valid.
See [Optional constructor tracking](OPTIONAL_TAGS.md) for the source and join
contract.

Unknown nominal/recursive payload graphs containing Results still need their
missing branch witnesses. Constituents proved Result-free need no business
presence choices, including an unknown `Option<int>`. One symbolic AnyIndex
family cannot represent every Result or optional constructor bit in a formal
array or map. Known finite collections retain all producers.
Concrete lengths prove coverage of those producers and do not reconstruct
fixed source-type dimensions.

Representative repeated callbacks record an actual activation interval,
including transitive helper and cleanup events. Ordinary loops retain the same
event-count restriction. Without an independent single-entry proof, repeated
Send, Receive, and task-order events relevant to business messages yield
NotImplemented. Scalar-only channels keep their existing resource rules; a
deferred repeated event cannot subsequently authorize a business Result send.

The independent validator follows real source application IDs, selected callee
values, closure/named invocation ancestry, and default evaluations. Source
syntax locates loops only within the selected callable; a call to an externally
defined helper still carries its incoming loop context. Deleting all repetition
records and clearing their event references cannot erase this reconstruction.
Traversal has a 65,536-operation bound. Missing entry evidence and ambiguous
callee alternatives remain incomplete.

An old Result inspection inside an optional callback does not discharge a later
message. A nonempty literal array and the normal Io read_all/write_all contract
can establish minimum entry; an unknown array, unknown foreign callback, or
zero-entry path cannot. The existing named-call source token retains its strict
callee contract. An implicit named callback without a separate physical source
anchor currently remains NotImplemented when a message proof depends on it.
Iteration-indexed message counts and cross-sender interleavings remain separate
extensions rather than consequences of checking one callback body.

Tests cover Source/Core, evidence mutation, formal/inline/nested/captured native
execution, propagation and fallback, normal close and business-error exits,
same-sender FIFO, and conservative cross-sender rejection. Negative programs
are checked without execution. A separate finite conservation model enumerates
all 64 single-message choices and both two-sender physical interleavings.
It also enumerates zero through three physical callback entries, checking the
second receive and the effect of inspecting an old producer before a later send.

The Optional source-entry batch passes the same 544 compiler tests on Windows
and Linux (one explicit audit remains ignored). Its native gate actually runs
17 distinct positive source programs through 19 entry executions on each host,
including scalar globals, ordinary Result conditionals, actual input aliases,
direct named forwarding and single-element array lambdas. Seven E0720 negatives
and two remaining multiplicity NotImplemented sources are checked only.

The callback routes use separate entry activations and bounded compositions.
An earlier nine-scope single entry exceeded the existing proof budget and
remains unsupported; its original source, hash and JSON are retained. These
tests do not claim support for that larger composition or raise the proof
limits. The detailed chronology and frozen binary manifests are retained in
the channel-message implementation audit under `target`.
