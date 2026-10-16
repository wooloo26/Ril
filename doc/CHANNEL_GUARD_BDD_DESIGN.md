# Bounded channel guard proofs (next-window proposal)

This is an implementation proposal. No BDD arena, new guard representation,
larger budget, finite iteration permission or shared syntax facade is registered.
The v11 source-index optimization has separate Source and native evidence in
[Channel source lookup](CHANNEL_SOURCE_INDEX_DESIGN.md).

## Observed failure and root-cause boundary

The original single-entry nine-scope source is retained byte-for-byte as
`channel_message_optional_callback_scope_budget.ril` (SHA-256
`E50829579B8E6185754B6D04B714503D538CE7683E6F5465388F0C4E1CD8987F`).
Its real Session still reports event 657, `bounded inactive event intersection
is unavailable`. It is not executed. The separate original split source now
passes Session/Core and three fresh native entry executions on each platform;
that success is not evidence for the nine-scope input.

The failing operation in `Replay::record` is `A AND NOT B`, where `A` is the
current complete custody case guard and `B` is the event guard. The complement
has already succeeded. The source index has completed its work before this
failure. Increasing or caching source traversal cannot resolve it.

Current guards use bounded DNF. `and` enumerates clause pairs, allocates union
clauses, checks contradictions, scans prior clauses for absorption, and then
performs another normalization. Normalization repeatedly searches every clause
pair for a complementary-literal consensus. `not` distributes complements
through this same machinery. These repeated scans can exhaust work even for
Boolean functions with shared or redundant history. Case merging retains all
custody, queues, inspections, task clocks and executed-event history; it joins
guards only when that entire state is equal.

The original diagnostic alone identified the representation and failing phase,
not the exact exhausted counter. The test-only v15 observation below now
distinguishes absorption work from input, literal, clause and consensus limits.
It also establishes that this actual failing intersection is nonempty. BDD
emptiness cannot resolve this sample.

## Actual v15 sample and smaller next algorithm

The frozen v15 Windows library test executable directly reruns the unchanged
real Session test. It passes its expected NI assertion in 19.36 seconds, emits
exactly one metrics record and retains SHA-256
`4D488E2312145D1A7E275AE446A06CE49F38406AFA914542970CB4FF143C9C6C`
before and after execution. No Cargo or native Ril program executes in this
sampling gate. Evidence uses the prefix
`target/channel-guard-event657-frozen-windows-v15`, with stdout/stderr/log,
`-report.json` and `-hashes.json` retained separately.

The diagnostic's 657 is a record sequence, not a physical event ID: this sample
has `record_sequence=657`, `record_kind=Event` and
`actual_channel_message_id=493`.

| Operand or failure | Actual observation |
| --- | --- |
| A, case guard | 36 clauses, each one literal; complete |
| B, event guard | One clause of 36 literals; complete |
| NOT B | 36 clauses, each one literal; complete |
| Structural comparison | A and NOT B are exactly equal, including all physical literal fields |
| First failure | Absorption at work 65,538, limit 65,536 |
| Executed set | Empty |
| Transport support of A/B | Events 260, 265, 300, 305, 342, 384, 389, 425, 430, 466 |
| All support executed | False |

The aggregate observation reports absorption charges 63,147, pair charges 3,795,
consensus charges 3,888 and contradiction charges 2,520 across complement and
intersection calculations. Their local counters are separate in the unchanged
algorithm; these totals must not be misreported as one shared quota. The exact
first failing local counter is the absorption counter above.

Here `A AND NOT B` equals `A AND A = A`, which is nonempty. It must retain the
inactive case, including its negative unexecuted Transport references and all
owed custody. The proposed exact-empty oracle both fails its admission rule
and cannot prove this intersection empty. No classical tautology or executed
membership is invented to make it applicable.

The measured smaller algorithm is now registered in the central conjunction
implementation, **awaiting its first compiler gate**. Both existing bounded
input checks run first. A private full structural comparison charges one unit
for the guard header, one for each clause and one for each full literal. Its
maximum is `1 + 256 + 256*128 = 33,025` units. A mismatch keeps the charged
comparison cost in the same conjunction counter before the original algorithm
continues. Exact equality alone selects `self.normalized()`; raw equal inputs
cannot skip contradiction, absorption, consensus or the normalization bound.
Normalization is the existing separate terminal phase of conjunction, not a
second attempt after an exhausted operation. No numerical quota is increased.

Full equality includes sort, all physical IDs, generations and truth fields,
including Transport producer/version metadata beyond its logical event key.
It is not Boolean equivalence, span equality or support-set equality. Expanding
`A AND A` would contain every original clause as a diagonal pair, plus unions
that are supersets of those original clauses. Absorption removes the latter;
contradiction removal and the subsequent deterministic normalization therefore
start from the same subset-minimal clause set as `normalized(A)`. The shortcut
retains the old normalized DNF result and its support, rather than exporting a
different Boolean-equivalent path cover. For the real 36-singleton input this
keeps all ten negative Transport references and the nonempty inactive case.

Two private test groups cover every field of fifteen representative physical
atoms, linear comparison cost and exact remaining-gas exhaustion. Four new
public guard-law groups cover the measured operand, raw normalization, unchanged
unavailable/shape/work bounds, and retaining different physical metadata. The
original nine-scope source's unit gate requires real Session verification and
Core lowering under this central algebra law. The v16 gate passes the algebra
checks but the complete source proceeds to another real NI at record 661. The
native adapter remains `.rs.pending`; no original nine-scope native execution
is authorized by that partial progress.

The v14 attempt passed the same NI test but emitted no metrics because its
test observer selected `ChannelMessageId(657)` instead of `record.sequence()`.
That observer mistake was corrected only under `cfg(test)`. The original v14
log/hash/report remain retained as a failed sampling attempt, not an operand
measurement.

## Actual record661 sample and exact raw-clause absorption

The frozen v17 sample identifies `record_sequence=661`, actual MessageId 497.
A remains the same 36 singleton clauses. B contains one 37-literal clause;
its complement consists of all clauses of A plus the singleton physical
`Result(producer=74, version=0, success=true)`. A is therefore a strict subset
of the complement's **raw physical clause set**. The first failure is the
contradiction scan at 65,537/65,536. The executed set is still empty and the
exact-empty oracle remains inapplicable.

The actual Source/Core positive target fails with that NI in 17.87 seconds;
its frozen library executable retains SHA-256
`52F1A9D846F8E06498709DDA8A267F5FBFA6E12334D7C35BA9C3ECC7318D9AC4`
before and after. Its exact operands, diagnostic, logs and hashes use the prefix
`target/channel-guard-record661-frozen-windows-v17`. This failed gate is retained.

The measured narrower optimization is now registered: if every entire raw
clause of A also occurs in B, `A AND B` selects `normalized(A)`, with the
symmetrical case selecting B. Complete equal guards use the existing equality
path. Equal clause counts with different physical structures cannot be proper
subsets. A monotone ordered merge compares full clauses and charges one plus
the literal counts of both compared clauses to the same conjunction counter.
It creates no clones or proof cache. Lookup exhaustion returns unavailable;
normalization retains the existing terminal quota. Input completeness and
clause/literal bounds are still checked before any structural optimization.

Every selected clause has its identical diagonal product in the old expansion.
Every other product is a superset of a selected clause, so absorption removes
it. The original and selected calculations have exactly the same subset-minimal
physical-clause basis before deterministic normalization, not just the same
Boolean meaning. This preserves the old normalized literal support, negative
unexecuted references and inactive custody case. Physical metadata in both
inputs must still undergo its independent validation; equal logical transport
event keys with different producer/generation fields are not equal clauses.

The unregistered independent audit `guard_clause_subset_model.py` and JSON under
`target/implementation-gap-audit/channel-message` examine all 11,035,684 ordered
pairs of 3,322 small four-sort guards. All 22,924 subset/equality pairs, including
19,602 proper subset pairs, retain the same truth table, subset-minimal physical
clause basis and literal support. This finite model is not a compiler pass.

The v18 frozen Windows gate actually passes all four private comparison/identity
tests and all fourteen public guard laws. It then runs the unchanged E508 source
through a real Session, which reaches a further NI at record 858 after 73.20
seconds. That failed Source/Core target and before/after hashes use the prefix
`target/channel-guard-raw-subset-frozen-windows-v18`. The entire source is still
unsupported and is not executed. Test-only observation of record 858 is being
sampled before choosing any further production algorithm.

## Actual record858 sample and witnessed physical term subsumption

The v19 frozen observation identifies record sequence 858 as actual MessageId
636. A has eight clauses with 336 literals in total (clause sizes 43, 43, 42,
42, 42, 42, 41, 41). B has one 48-literal clause and its complement has 48
singleton clauses. The first failing absorption counter is 65,581/65,536.
The actual case has twelve executed events and sixteen Transport references
across the operands; the all-support-executed admission condition is false.
The positive Source/Core target still fails with NI, in 94.68 seconds. Evidence
uses `target/channel-guard-record858-frozen-windows-v19`; executable SHA-256
`43D4648C8D7559C1519B3793B12629FFC94B03ABE35119B2BCCD4B2F8A671720`
is unchanged before and after the direct run.

Exact parsing of the retained physical literals establishes **no common raw
clause** between A and the complement. General common-clause factorization is
therefore not the appropriate next fix. Instead, each of the eight clauses of
A contains exactly one complete singleton clause from the complement: either
the false observation ConditionEvaluationId 63 or 64. Other physical fields in
the large clauses remain intact. The parser and its report are retained as
`inspect_record858_guards.py/.json` in the channel-message audit.

The approved narrower algorithm is now registered, awaiting its first gate:
for every clause a of A, require a physical clause b of the other operand with
`b subset-of a`. Every literal comparison uses the complete GuardLiteral
identity, polarity and generation. Only these explicit witnesses permit
selecting `A.normalized()`; the opposite direction is checked symmetrically.
Every header, selected-clause visit, witness visit and both clauses' literal
counts are charged to the same conjunction counter, after previous structural
checks. Exhaustion has no fresh fallback or extra quota. Complete/shape checks
and the normalizer's existing quota are preserved.

The proof is stronger than a Boolean implication oracle: for each a, the old
product set has the exact product `a union b = a`. Every other product is a
superset of its originating a, so the subset-minimal physical-clause basis is
identical to A's original basis. Deterministic normalization and subsequent
executed-term filtering therefore receive the same representation and support
as the old successful calculation would have produced. The inactive case is
retained, including its unexecuted references and debts; no branch is declared
classically empty. Independently validated input metadata is not skipped.

The separate unregistered `guard_term_subsumption_model.py/.json` examines the
same 11,035,684 small ordered pairs. All 701,419 physically witnessed pairs,
including 688,296 beyond raw clause-set inclusion, retain the original truth
table, exact subset-minimal physical basis and literal support. The model
also rejects same-event altered transport producer/version and different
sort/generation witnesses. It is not compiler or native evidence.

The v20 frozen Windows gate passes all six private identity/budget groups and
all seventeen public guard laws, including the exact eight-clause record858
regression in both directions and raw normalization/unavailable/work boundaries.
It then actually checks the unchanged entire nine-scope Session/Core positive
target. That gate advances beyond record858 but remains NI at **record957,
`independent channel replay exceeds its case bound`**, after 105.56 seconds.
This is the 256-distinct-state replay bound, not another guard conjunction
failure. All logs and unchanged before/after executable hashes use the prefix
`target/channel-guard-term-subsumption-frozen-windows-v20`.

The original program is still unsupported and its native adapter stays pending.
The registered unit is now
`structural_guard_laws_do_not_authorize_the_preserved_replay_state_gap`: it
requires Provenance NI and the exact record957 case-bound detail. Passing this
unit means the compiler still refuses the input; it is not a positive semantic
pass. Complete Session/Core verification is separately retained as
`channel_source_positive.rs.pending`, and the native adapter remains pending.
No case limit is increased and no completed history, execution evidence,
custody, queue, task clock or debt is discarded. A separate observed-state
contract is needed before changing case representation or compaction. A proof
that drops a nonempty continuation or forgets a live old predicate would be
invalid even if it reduces the state count. Only actual complete Source/Core
success permits
registering native execution. Its exceptional wall timeout may be 180 seconds
for this large original source; existing 20-second cases and all compiler
work/shape limits remain unchanged, and a wall timeout is always a failure.
The next diagnostic-only proposal is described in
[Channel replay-state observation](CHANNEL_STATE_OBSERVER_DESIGN.md). Its
test-only v23 observation is now registered and actually sampled; it supplies
no compression or liveness proof. Inspection variants dominate the measured
prefix, and an actual retained false literal contradicts a recorded true
exhaustive-pattern condition. The proposed remedy requires complete guarded
evaluation receipts and independent Source truth reconstruction, as described
in [Boolean evaluation receipts](BOOLEAN_EVALUATION_RECEIPTS.md); it is not a
global constant filter and has not been registered.

A general exact common-clause factorization remains unregistered. Its proposed
law is `A=C OR A'`, `B=C OR B'`, so `A AND B=C OR (A' AND B')`, where C is the
intersection of complete physical raw clauses. The independent
`guard_common_clause_model.py` checks all 511,920 non-subset common-clause pairs
in the same small domain, preserving the full pre-consensus physical basis,
support and truth table. Any eventual implementation must charge partition
lookups, clones and products to one conjunction counter and run the existing
contradiction, absorption and normalization rules. The model alone does not
justify registering this broader algorithm before the actual next sample.

## First safe algorithm slice

Use a private reduced ordered BDD kernel as an exact bounded emptiness and
implication procedure, before replacing stored guard representations. Its first
consumer is the inactive continuation: prove `A AND NOT B = false`. Only an
exact false root permits returning `ChannelGuard::never()` and omitting this
unreachable continuation, and only after the executed-support admission rule
below. A satisfiable or unavailable result supplies no
inspection, independence, execution or producer-presence evidence.

Nodes are immutable `(atom, low, high)` entries with separate false/true
terminals. A deterministic total atom order, a unique-node table and `low==high`
reduction provide shared reduced subgraphs. Iterative Apply uses an explicit
pending stack and a memo table keyed by operation and exact operand node IDs.
Negation is a memoized graph traversal in the first implementation; complement
edges and dynamic variable reordering are unnecessary initial complexity.
DNF import combines each literal into its clause and each clause into the root.
An `and_not` operation can avoid constructing a distributed DNF complement.
The established ordered-decision-diagram algorithms are described in
[Bryant's original paper](https://doi.org/10.1184/r1/6622400.v1).

Atoms retain separate sorts and physical identities:

| Sort | Identity |
| --- | --- |
| Boolean | Actual ConditionEvaluationId |
| Optional | Actual OptionalTagId |
| Result | Physical producer and generation |
| Transport | Actual ChannelMessageId, validated transport producer and generation |

Transport metadata must first establish the event-to-producer/version mapping.
Its current logical contradiction key is the event ID; full validated identity
must remain available for diagnostics and source checks. Two mismatched physical
transport mappings cannot be silently identified by the BDD importer. Different
sorts, versions, parameter paths or source activations do not become one atom
because their types, spans, causes or truth values coincide.

The arena and Apply memo store Boolean structure only. They do not cache
instance arguments, selected callees, borrows, source existence, tag ownership,
Result inspection, queues, event order or completed-scope permission. A cache
hit is not a reason to skip any independent Source replay. Lifetime is one
independent validation region against immutable facts, with deterministic
construction and no reuse across Session updates. Initially use operation-local
arenas; broader region sharing requires the same explicit lifetime and gas rules.

## Work and representation boundaries

The numerical limits remain 65,536 work units, 256 DNF clauses and 128 literals
per DNF clause. BDD nodes, edges, unique/memo lookups, pending work and input
visits must all consume a specified bounded work counter. Arena and memo sizes
are bounded by charged entries; recursion cannot consume an unbounded Rust stack.
Node-ID overflow and every exhausted resource return unavailable, never true
or an empty authorized branch.

Do not first spend 65,536 units in the old operation and then run a fresh
65,536-unit oracle. The new logical-operation driver must own a single counter.
A successful emptiness proof returns immediately. If the result is nonempty,
the existing DNF calculation may use only the remaining counter, and must
produce its original representation or remain unavailable. This scheduling can
introduce resource pressure on previously admitted formulas, so small/cheap
operations should retain their direct path and the full acceptance regression
must be measured. Selecting a cheap algorithm is not permission to reset gas.

An alternative after operand measurement is an exact indexed DNF absorption
algorithm with the same counter. Which route actually closes event 657 depends
on whether its operands are large, contradictory or satisfiable. The first
implementation should not export arbitrary BDD paths as replacement DNF merely
to fit the clause bound.

## Why a complete BDD replacement needs a later contract

Current code observes more than a guard's Boolean truth table:

- `Replay::record` and the checker's `executable` helper discard DNF terms that
  mention a transport event absent from the case's actual executed-event set.
- Result alias/outcome reconstruction and `present` inspect physical literals
  occurring in terms.
- Metadata validation checks each literal's actual producer, version, source
  observation and sequence position before trusting its branch.

Canonical Boolean reduction may erase an atom or introduce a different path
cover. These support-sensitive consumers cannot be replaced by scanning BDD
support or assigning an unexecuted transport variable false. Both positive and
negative literals of an unexecuted event are unavailable to an active term.
Complete migration requires an explicit evaluated/definedness domain and
independent provenance for all source references, with a differential concrete
model. The initial oracle must refuse any unexecuted transport support; classical
emptiness alone is insufficient even when no stored guard is rewritten.

## Exact-empty admission and no-lost-case proof

There is no established invariant that every Transport literal in `case.guard`
has an executed event. An inactive complement can introduce a negative literal;
negative transport predicates require execution just as positive ones do.
The proposed oracle is therefore restricted to all of the following:

1. Both input guards are complete and bounded, with their real per-sort physical
   metadata, sequence and Source references already independently validated.
2. Every Transport event mentioned in either input, regardless of polarity,
   belongs to this actual case's complete `executed` set. Compare actual event
   IDs and validated producer/generation mappings; a lexical span or another
   event with the same producer cannot substitute for membership.
3. The ordinary active intersection has succeeded and remains nonempty after
   its existing executed-term filter. The first slice keeps NI if this check
   fails, even if a Boolean oracle alone would call the inactive side empty.
4. The bounded exact oracle proves `A AND NOT B` false with the same charged
   operation budget. Otherwise it cannot eliminate this inactive continuation.

Let `suppT(G)` be the Transport event identities literally present in guard G,
and let `F_S` discard DNF terms mentioning a Transport event outside executed
set S. The existing conjunction and normalization introduce no new literal:
union creates literals only from its two inputs, absorption removes terms and
consensus takes a subset. Consequently
`suppT(and(A,B))` is a subset of `suppT(A) union suppT(B)`. Under rule 2 it is a
subset of S, so `F_S(and(A,B)) = and(A,B)`. Exact classical emptiness gives
`A implies B`, hence the active guard is semantically A. Every assignment
previously admitted by A still has its active continuation. No owed producer
can disappear through dropping an unexecuted-literal term. Rule 3 additionally
prevents optimizing a case whose active continuation has already been lost.
Subsequent event processing retains its existing custody and exit checks.

Without rule 2, the abstract witness `A = B = not Transport(0)` with an empty
executed set has a nonempty A, an empty classical inactive set and a completely
filtered active set. An unpaid custody entry would vanish if both sides were
removed. This is a representable guard/filter counterexample, not a claim that
an accepted Ril source currently reaches that exact state. No stronger Source
reachability invariant is assumed to dismiss it. The conservative admission
rule rejects it by inspecting negative support too.

The independent unregistered audit
`target/implementation-gap-audit/channel-message/guard_oracle_definedness_model.py`
enumerates all 3,322 raw guards of at most two clauses over four distinct atom
sorts and all sixteen truth assignments. Across both executed-set choices it
checks 11,179,325 eligible operand pairs; all 789,138 exact-empty pairs preserve
every left-hand assignment after active-term filtering. Its retained JSON also
records the unexecuted-negative counterexample and its admission rejection.
This is a finite algebra model, not compiler/native execution or a proof of
source reachability. The symbolic argument above covers normalization's
literal-subset property beyond the model's clause size.

Test-only record-657 capture includes the complete actual executed-event ID
set, both original guards, their successful complement, Transport support and
`all_transport_support_executed`. The v15 real Session sample proves that this
particular case does not satisfy the proposed admission condition. No
production oracle is registered.

## Verification and counterexamples

First retain the real event-657 operands and failure reason with test-only
instrumentation; the original fixture and its previous NI JSON remain intact.
Compare new and old guard operations on every small finite assignment, including
all four atom sorts, opposite truths, producer generations and independent
formal Option paths. Exhausting any quota must leave the result unavailable.
Check deterministic node construction, reduced-node uniqueness and memo entries
against a separate direct truth-table model.

All Source/header/caller/owner/iteration selector mutations and ordinary
Result-only controls remain required. Include a conditional event absent from
the case's executed set and a future transport reference, so atom reduction
cannot authorize an observation that never occurred. Keep all custody fields
in merge equality. No completed-scope history, Result debt or retained ambient
permission is garbage-collected as a shortcut for this batch.

Only after the unchanged nine-scope fixture actually verifies through Session
and Core can its three input routes be authorized for native execution. If it
still has a nonempty oversized guard or exceeds work, report that precise NI.
An unpaid-message variant must still be rejected without execution.

## Read-only syntax facade for sibling validators

Propose moving the structural index behind a small `sema::source_syntax` facade
owned by C, with Root registering the shared module. It accepts immutable
SemanticFacts, a real CallableOwner, full file/start/end span, an explicit
Expression/Call query role and a caller-owned mutable work counter. It returns
the unique frozen AST expression or a missing/ambiguous/inconsistent/budget
error. No fallback by name, span alone, first row or guessed DefinitionId exists.

Function roots contain their own body, signature-where declarations and
defaults. Lambda roots contain their actual site body. Nested function/lambda
bodies never appear under an enclosing owner; congruent duplicate definitions
may agree, conflicting headers or bodies refuse. The existing complete walker
remains a test oracle. Failed partial builds are never installed and every
lookup remains charged.

A needs only Expression lookup and may inspect the resulting real Name/Field/
Index chain. The returned spelling is not a resolved symbol, receiver authority
or instantiated type proof; A still validates its actual typed receiver and
substitution environment. C keeps syntactic repetition bounds and actual-ID
application/caller-row indexes in a channel adapter. Caller rows are immutable
evidence references, never a memoized dynamic proof. The facade exports no
borrow, optional presence, Result generation, callback multiplicity or finite
iteration claim. Per-validator indexes may share the same frozen lexical input
but never an instance proof or a budget reset.

## Finite physical iteration remains separate

After the guard slice, implement the agreed finite for contract in
[Finite channel iteration](CHANNEL_FINITE_ITERATION_DESIGN.md): actual ordered
entries and physical producers, frozen per-entry source values, completion and
event intervals, independent coverage, and permission-root continuity. A BDD
can compact conditional paths but cannot turn one representative send into two
physical sends. Unknown collections, missing entry coverage, recursive inputs
and unproved sender interleavings remain obligations. Root owns shared
iteration/Core contracts and loop Result integration; C owns channel custody
and independent replay. This document does not register those fields.
