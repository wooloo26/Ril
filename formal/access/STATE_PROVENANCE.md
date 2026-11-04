# State Provenance in Ril: Coverage, Authority, and Their Limits

## Abstract

Can a compiler account for every state source that a program may access?
For Ril, this question involves more than finding the object named by a variable.
Aliases, captured environments, mutation during a call, effect handlers and
cleanup can all connect an operation to state that its surface expression does
not name. We present a Lean formalization of a mathematical core for reasoning
about these connections. A finite constraint solver computes grounded provenance
facts, and a simulation theorem proves source coverage for every finite
execution prefix of a resolved control-flow language. Separate verified
interfaces address authority in a finite access/call calculus, cyclic graph
reachability, frozen call-entry origins, summary substitution, local discharge
and affine resumption. The central design distinction is between an object's
origin, the authority of a path to it, and the role of an origin in a summary.
Conflating these notions permits false freshness or false locality conclusions.
The artifact passes 176 positive and adversarial checks and a transitive axiom
audit. Its results support conservative source coverage within the stated
interfaces; they do not establish a complete Ril compiler or universally exact
source prediction.

**Keywords:** state provenance; access modes; abstract interpretation; aliasing;
algebraic effects; mechanized verification.

## 1. Introduction

A function can mutate an object without naming the binding from which that
object originally came. A closure can carry state through an apparently
immutable function value. A handler can eliminate an effect while writing to an
outer counter. In each case, inspecting the immediate expression gives an
incomplete account of the state involved.

Ril makes these dependencies part of static checking. Its
[specification](../../doc/SPEC.md#state-and-provenance-tracking) distinguishes parameter
writes, independently retained writers, surviving environment creation, named
external access, and root or contained return dependencies. These distinctions
make a useful promise possible: a wrapper, alias or interface should not make
a required state obligation disappear.

The promise has two separate dimensions. **Coverage** asks whether the inferred
sources include every source that an execution can involve. **Precision** asks
whether those sources exclude dependencies that no execution can exercise.
Coverage tolerates extra sources; permission checks cannot treat those extra
possibilities as evidence of uniqueness, disjointness or confinement.

This paper investigates the mathematical basis of that promise. Its contributions
are an executable finite provenance analysis with a source-coverage proof,
verified authority and boundary judgments that preserve the distinctions required
by the specification, and a concrete account of the remaining correspondence
and trust obligations. The contribution is a mechanized case study of Ril's
access and provenance distinctions.

The scope matters. There is no source-language compiler in the artifact. The
provenance language admits cyclic heaps and unbounded control-flow execution.
The integrated authority checker instead handles a finite access/call language
with fixed allocation trees. A graph oracle and boundary kernels establish
further results under their own interfaces. These results are collected in one
certificate, but their conjunction is not a soundness theorem for an unrestricted
language combining all those features.

We begin with a small example that explains why this separation is necessary.

## 2. A running example: reachability is not history

Consider the following pseudocode. It describes an object-graph operation, not
a complete Ril source program.

~~~text
insert_then_return(store):
    fresh = allocate_cell()
    store.child = fresh
    return store.child
~~~

Suppose the object graph at call entry contains objects 1 and 2:

~~~text
At entry:       store #1 ──child──> old #2
After insertion: store #1 ──child──> fresh #3

Frozen entry set: {#1, #2}
Current reachable set after insertion: {#1, #3}
~~~

The returned object is reachable from `store` when the function returns.
Nevertheless, it did not belong to that parameter's graph at call entry.
A return contract claiming an entry origin cannot be justified by the later
store. Ril's [return-source rules](../../doc/SPEC.md#return-construction-access-modes-and-sources)
explicitly require the historical relation.

Two other distinctions are already visible. First, the allocation site of
`fresh` is a static name; repeated execution can create different objects at
that site. Second, if a closure later captures object 3, that capture refers to
an existing object. A subsequent call must not interpret its allocation origin
as an instruction to create a new object identity.

These are different questions:

| Question | Information needed |
| --- | --- |
| Which source may contribute to an operation? | A conservative source abstraction |
| Which object does this particular access designate? | Concrete identity and alias relations |
| Does a path permit writing? | Its own authority and lifetime dependencies |
| Was an object in a parameter's entry graph? | A frozen entry relation |
| May a summary reference be substituted? | Its explicit reference role |

The rest of the paper gives each question an appropriate interface.

## 3. A finite analysis of state sources

### 3.1. Concrete origins and execution

A concrete origin is a tuple

$$
o=(k,d,a,\iota,t,\ell),
$$

where $k$ is a source kind, $d$ a declaration or allocation-site identifier,
$a$ an activation, $\iota$ an object identity, $t$ a task, and $\ell$ a
scope. Source kinds distinguish parameters, modules, captures, allocations and
foreign state. The provenance abstraction retains only

$$
\alpha(o)=(k,d).
$$

This projection explains why equal abstract sources need not denote the same
object. It also explains why source coverage alone cannot establish exclusive
authority.

A concrete configuration contains a control point, roots, heap edges, accumulated
events, fresh-object and context identities, and call, handler and cleanup
stacks. An edge records a parent, field and child. Concrete stores replace the
selected edge; projections select an actual field. Reachability is an
inductively defined finite path relation, so cyclic graphs do not require
infinite proof objects.

Execution is defined independently of analysis. Its rules introduce a source,
copy a handle, update or project a field, emit a root or reachable-object event,
or change a context. Events distinguish reading, writing, retention, capture,
root return, contained return and transfer. They record access/state obligations,
not arbitrary information flow between scalar values.

Context labels preserve explanation metadata. A transition labelled `handler`
does not implement handler dispatch, and one labelled `clone` does not by
itself implement graph copying. Such operations require their actual evaluation
steps and state dependencies to be represented by a correct lowering.

### 3.2. Abstract facts and grounded inference

For a resolved program, the analyzer generates a finite set of Horn rules over
five fact forms:

| Fact | Meaning |
| --- | --- |
| $\operatorname{active}(p)$ | Program point $p$ may execute |
| $\operatorname{root}(r,s)$ | Root $r$ may have source $s$ |
| $\operatorname{edge}(s,u)$ | A heap edge may connect the source classes |
| $\operatorname{desc}(s,u)$ | Source $u$ may be reachable from source $s$ |
| $\operatorname{event}(q,s)$ | An event of kind $q$ may involve source $s$ |

For example, a reachable store propagates sources from its parent and child
roots into an edge fact. Projection propagates possible children into the
destination root. A deep observation follows descendant facts.

Given rules $\mathcal R$, define

$$
F_{\mathcal R}(X)=X\cup
\{c\mid(P\Rightarrow c)\in\mathcal R,\;P\subseteq X\}.
$$

The analysis starts from the empty set and repeatedly adds an enabled rule
conclusion. This is a finite instance of the fixed-point approach developed by
[Cousot and Cousot (1977)](https://www.di.ens.fr/~cousot/COUSOTpapers/POPL77.shtml).
The artifact proves its solver directly; it does not mechanize a general
Galois-connection framework for all the interfaces in this paper.

**Theorem 1 — Grounded least solution.** The solver terminates and returns a
duplicate-free representation of the least closed set of rule consequences.
Every returned fact has a finite derivation from the generated rules.

*Proof idea.* The pending list contains the distinct possible conclusions.
Each successful iteration removes one conclusion from that list, giving a
strictly decreasing natural-number measure. The solver preserves a derivation
for every known fact. When no pending conclusion is enabled, the result is
closed. Induction on derivations shows that every closed solution contains it.

Grounding rules out circular justification. Constraints saying “use of $x$
follows from use of $y$” and “use of $y$ follows from use of $x$” derive
neither use without a base operation. Contract annotations are checked against
the inferred result; they cannot supply that missing base.

### 3.3. Coverage of every finite prefix

Let $A(P)$ denote a successful analysis of program $P$, and let
$c_0\to_P^*c$ be a finite concrete execution from its initial configuration.

**Theorem 2 — Source coverage.** Every recorded event is covered:

$$
e\in\operatorname{events}(c)
\quad\Longrightarrow\quad
\operatorname{event}
\bigl(\operatorname{kind}(e),\alpha(\operatorname{origin}(e))\bigr)
\in A(P).\operatorname{facts}.
$$

*Proof idea.* A simulation invariant relates concrete control points, roots,
edges and events to abstract facts. Each concrete step preserves that invariant.
The graph case is an induction on the concrete reachability path; the execution
case is an induction on the trace.

This formulation also covers infinite execution: every event occurs in some
finite prefix. It does not require proving that the program terminates.
A companion theorem covers roots queried at reachable program points.
Those queries share the flow-insensitive solution; they are not distinct
precise solutions for each point.

The theorem is relative to the resolved concrete semantics. If lowering omits
a cleanup edge or a captured environment operation, it has changed the program
whose sources are being covered. No property of the solver repairs that omission.

## 4. Authority requires more than a source set

Ril separates slot replacement from access through a slot. The
[specification](../../doc/SPEC.md#binding-modes-and-storage-matrix) also distinguishes
temporary mutable parameters, independently retained writers, construction
qualification and lifetime restrictions. These facts cannot be reduced to a
single chain of increasingly powerful modes.

| Ril notation | Distinction relevant to this study |
| --- | --- |
| `let` / `var` | Whether a binding's target slot can be replaced |
| Plain reception / `ref` | Deeply immutable data versus a read-only path that may observe a live writable origin |
| Parameter `mut` / `^mut` | Temporary write authority versus authority permitting retained writers |
| `new` handoff | Transfer of eligible construction authority while preserving object identity |

The parameter modes in the table have context-specific reception rules; local
bindings must also meet their own exclusivity and sharing obligations.

For example, a `ref` path may observe a graph whose writable origin remains
live. It does not make that graph deeply immutable. A `mut` parameter provides
temporary write authority but does not, by its spelling alone, establish unique
ownership. A construction-qualified value must independently meet the relevant
alias and isolation checks before a handoff.

The finite access/call checker computes permissions, grants, dependency tokens,
loans and use evidence from declarations and operations, starting from an empty
world. Inputs cannot inject authorization tables. Its independently defined
runtime erases the checking metadata.

**Theorem 3 — Authorized execution of the finite calculus.** If checking
succeeds, every observation in every finite execution prefix has authorized
evidence and an inferred source. The checked program also has a concrete
execution.

The progress part prevents a vacuous interpretation in which checking succeeds
only because the runtime cannot take a step. Supporting lemmas connect access
evidence to original declarations, writable member paths and active dependency
tokens. Temporary authority cannot justify independent retention. Construction
transfer preserves the designated identity and ends the source authority;
derived paths that depend on it consequently become unusable.

This theorem applies to the finite calculus. Arbitrary cyclic storage is
addressed by a separate graph interface, not silently admitted by the same
execution theorem.

### 4.1. Aliases, cycles and output correlations

The graph oracle computes finite-path authority closure on a complete finite
graph. Each path attenuates access through the declared and held member modes.
A writable path to an object cannot upgrade a different read-only path to the
same object. A checked immutable-consistency condition excludes an immutable
access coexisting with a writer to that object.

For root set $R$, let $V_H(R)$ be the set of object identities reachable in
heap $H$. The separation check establishes

$$
\operatorname{separated}(H,R_1,R_2)=\mathrm{true}
\quad\Longrightarrow\quad
V_H(R_1)\cap V_H(R_2)=\varnothing.
$$

It compares object identities even when two origins describe the same object
with different provenance metadata. Cycles are handled by the closure
computation. Unknown selections contribute all their possible targets.

Branch correlations provide useful precision without weakening this condition.
Suppose a permutation returns either $(a,b)$ or $(b,a)$, with $a\ne b$.
Both joint outcomes have separate components. Taking marginal unions instead
gives $(\{a,b\},\{a,b\})$, which loses that relation. The artifact retains
alternatives in the finite calculus and proves the corresponding common-relation
rule for abstract output pairs. Applying it to a source program still requires
those alternatives to cover its actual joint outputs.

## 5. Preserving history across a call

### 5.1. Entry snapshots

For formal parameter $x$, let $R_x$ contain the saved, already evaluated
argument roots, and let $H_0$ be the heap at callee entry, after argument and
default preparation. The entry relation is

$$
E_x=\{o\mid \exists r\in R_x,\;\operatorname{Reach}_{H_0}(r,o)\}.
$$

**Theorem 4 — Exact entry capture.** The computed snapshot contains precisely
the origins in $E_x$. Every parameter selection accepted by the entry-based
summary checker is reachable from a saved argument root in $H_0$.

Both the producer and the membership check matter. A membership theorem for a
caller-supplied list alone would not show that the list represents an entry
graph. The formalization connects the computed snapshot to concrete reachability.

Return to the insertion example. Object 3 is absent from $E_x$, even though it
is reachable from the parameter after the store. Claiming it as an entry-origin
return is rejected. An independent later call may legitimately include object 3
in its own snapshot. Entry origin is relative to a particular call boundary.

Saved values also matter. Rebinding the caller's argument slot during preparation
does not replace a value already prepared for an earlier argument. Conversely,
the graph snapshot must reflect preparation that really occurred before entry.
The entry kernel takes these saved roots and the entry heap explicitly; proving
that a compiler supplies them correctly remains a lowering obligation.

### 5.2. Reference roles and fresh instances

A summary has six state components: root returns, contained returns, writes,
independent retention, environment creation and named reads. Its effect row is
separate. Each origin reference has one of three roles:

| Role | Instantiation |
| --- | --- |
| Concrete origin | Preserve its full identity |
| Formal selection | Select an origin from the formal's frozen entry graph |
| Fresh allocation template | Construct a new identity for this instance |

A source kind is not a reference role. A captured allocation is concrete,
although its source kind remains “allocation.” A captured parameter origin is
also concrete; a new call must not bind it to that call's argument.

Fresh instances use an identity range above the supplied old-object set.
Distinct fresh templates require distinct serials, while repeated references
to one template preserve aliases. Checks also prevent an old origin from being
classified as owned by the new callee context. Freshness here concerns an object
identity: a fresh root can still contain references to old state. Graph
separation is checked separately.

**Theorem 5 — Checked substitution.** Concrete identities survive
instantiation. Accepted formal selections have frozen entry origins. Fresh
instances differ from covered old objects and from instances of distinct fresh
templates. Accepted old references cannot be discharged as callee-local state.

These are boundary theorems with explicit inputs. The old-object set must cover
the actual existing objects, and activation identities must be authentic.
Substitution success does not prove that an arbitrary supplied template describes
a function body. The finite call checker derives body facts by checked inlining;
general symbolic summary generation remains outside that checker.

## 6. Handling effects without hiding state

Algebraic handlers interpret operations and their continuations, as developed
in [Plotkin and Pretnar's treatment](https://lmcs.episciences.org/705).
For provenance, a separate question remains after an operation has been handled:
what state did the body, selected handler and cleanup access?

A handler that answers an operation and increments an outer counter has removed
that operation from the outward effect row. The counter write still occurred.
Similarly, early abort does not undo prior writes, and cleanup may add new ones.

Write a boundary summary as

$$
\Sigma=(R_{\mathrm{root}},R_{\mathrm{contained}},W,T,C,N;\mathcal E),
$$

where $W,T,C,N$ record writes, independent retention, environment-creation
obligations and named reads, respectively. The boundary kernel combines the
body, handler and cleanup components before applying effect elimination.
Eliminating an effect changes $\mathcal E$; it preserves every state component.

### 6.1. When local state may be discharged

Local discharge needs a footprint of authority roots, environments and escapes.
The footprint must include handler and cleanup environments, even when they
are absent from the body's own roots. Checking only the body can incorrectly
classify state as confined.

**Theorem 6 — Sound discharge under coverage.** If an abstract footprint covers
every root, environment and escape in a concrete footprint, an event removed by
abstract discharge is also removable under the concrete footprint.

The implementation removes only owned, confined local reads and writes.
Retention, capture and return events are preserved. An outside handler or
cleanup environment blocks confinement; an outside handler or cleanup write
survives outward state computation.

The covering premise carries real content. Unknown environments or escape
relations cannot establish it. For the finite access calculus, live bindings,
loans and recorded publications are enumerated from the checked world.
For other interfaces, footprint coverage must be established separately.

### 6.2. Affine resumption through shared identity

A copyable `used` flag is insufficient to establish affine resumption.
Two handles might each retain a copy that still says “unused.”
The resumption kernel therefore gives aliases one identity and stores
consumption in a shared ledger.

Successful resumption consumes that identity before continuation execution.
It removes the operation's temporary authority, preserves independent authority,
and checks the current arm, callable and task context.

**Theorem 7 — No second resumption through an alias.** After one successful
resumption, the same identity cannot resume again after any sequence of the
kernel's resumption and context-switch transitions.

*Proof idea.* Consumption is monotone along those transitions. The resume guard
rejects every identity already in the ledger, so aliasing cannot restore an
unused state.

Administrative resumption steps also preserve the committed event log.
This does not say that a resumed continuation performs no writes. Continuation
evaluation and cleanup must contribute their own concrete steps and summaries.
The theorem describes the shared-record kernel; source handlers must be lowered
in a way that preserves that record and its authority dependencies.

## 7. Why exactness has a different limit

The reference provenance analysis deliberately merges root histories and ignores
field coordinates in abstract edges. Consequently, overwriting a root can leave
its old source in the solution, and projecting a known field can retain sources
from other fields. The artifact includes a concrete execution invariant proving
one such old source spurious. A least constraint solution can therefore remain
an overapproximation of execution.

More precision can remove particular false positives, but a general exact
algorithm faces a computational boundary. Instrument an arbitrary small-step
machine to publish a distinguished marker exactly when it halts. The artifact
proves

$$
\operatorname{Publishes}(M,s)
\quad\Longleftrightarrow\quad
\operatorname{Halts}(M,s).
$$

This connects source-reachability questions to the classical computability
setting of [Turing's work](https://doi.org/10.1112/plms/s2-42.1.230).
The formal diagonal argument makes its premise explicit: the computational class
must represent the program that halts exactly when a proposed computable decider
answers negatively. Under that premise, no computable total exact decider exists.

The instrumented machine is a separate model. The artifact does not prove an
encoding of arbitrary machines into surface Ril or its resolved CFG. Thus the
general impossibility conclusion is conditional on representability; it is not
an unconditional universality claim about the implemented analyzer.

## 8. Validation and evidence

The reported results describe artifact revision `3132c64`, using Lean 4.33.0
and its bundled libraries. At that revision, a clean verification run passed
176 positive and adversarial fixtures. The audit examined 3,705 model declarations,
including 1,355 theorems. These counts include generated declarations and are
not counts of independent scientific results.

Representative cases exercise complementary sides of the checks:

| Case | Expected and observed result |
| --- | --- |
| A legal shared alias with its source obligation | Accepted; hidden-source variant rejected |
| A cyclic graph and a shared descendant | Reachability retained; false separation rejected |
| A permutation of distinct objects | Accepted with joint alternatives |
| Unknown selections that may overlap | Separation rejected |
| Insertion after call entry | Current reachability retained; entry-origin claim rejected |
| Captured allocation or parameter origin | Original identity preserved |
| Local mutation with an outside handler environment | Discharge blocked |
| A second resume through an alias | Rejected; independent authority remains usable |

The acceptance cases are important: a checker that rejects every program could
satisfy a safety implication without providing a useful analysis. The fixtures,
a nonempty concrete provenance execution, and the finite calculus's progress
theorem supply distinct evidence against that failure mode. Fixtures supplement
the universally quantified proofs; they cannot replace them or establish
unmeasured performance or full-language coverage.

The axiom audit examines every imported declaration in the model's `RilAccess`
namespace and its transitive axiom dependencies, including generated helpers
and fixture proofs. The permitted union is exactly `propext`, `Classical.choice`
and `Quot.sound`. No custom unproved axiom, unfinished proof or unsafe project
declaration is accepted. Four negative probes verify rejection of an added
axiom, `sorryAx`, an unsafe definition and native proof evaluation.
This follows the distinction between kernel-checked proofs and proofs that
introduce additional compiler-trust axioms described in the
[Lean reference](https://lean-lang.org/doc/reference/4.33.0/Axioms/).

## 9. Interpretation and remaining obligations

The results support conservative coverage within the stated models. Applying
them to Ril requires a correspondence argument, not just a collection of
similarly named operations.

For source-to-core translation, the artifact defines an explicit contract:
the encoded initial state must be correct, each source step must be simulated
by a finite core trace, and every source event must appear in the encoded
events. Coverage transfers to the source execution once these premises are
supplied. The conditional theorem is proved; an actual compiler satisfying its
premises has not been implemented here.

The same distinction applies to boundaries. Complete entry heaps, saved argument
values, old-object coverage, branch alternatives, environments and resumption
records must correspond to the program being checked. Foreign bodies have a
named conformance premise. Opaque interfaces must preserve hidden source
identities, and task/resource implementations must obey their stated access and
lifetime contracts. The artifact does not verify a scheduler, resource library
or foreign implementation.

Ordinary aggregates, closures, `via`/`infer`, clone/derive and storage APIs
must be audited as instances of these obligations. This avoids replacing a
missing frontend proof with a miniature model that merely carries the same
feature name. A complete compiler would additionally need verified symbolic
summary generation and a proof that its combined representations preserve the
relations established by the separate kernels.

The audit identified implementation-model mistakes rather than a need to amend
the normative specification. Frozen entry graphs, separate state/effect rows,
complete discharge environments and affine resumption are already required by
SPEC. The explicit reference roles and shared identity ledger enforce those
existing distinctions. The resulting SPEC verdict is limited to these audited
mathematical interfaces.

## 10. Conclusion

Complete state-source accounting is feasible as a conservative guarantee over a
faithfully represented program. The difficult boundaries are historical and
relational: a currently reachable object need not be an entry origin, an
allocation-origin capture need not be fresh, and an eliminated effect can leave
state obligations behind. The verified kernels preserve these distinctions and
make their premises inspectable. Their application to a complete Ril compiler
remains a correspondence problem; universal exact source prediction remains
subject to the stated computability limit.

## Appendix A. Artifact correspondence

The paper's theorem statements summarize the interfaces below. Names identify
the precise machine-checked statements; the surrounding text states their
scope and remaining premises.

| Paper result | Lean evidence | Source |
| --- | --- | --- |
| Theorem 1 | `solve_exact`, `solve_least`, `solve_nodup`; termination of `solveAux` | [Solver](RilAccess/Solver.lean) |
| Theorem 2 | `provenance_coverage`, `program_point_coverage` | [Concrete semantics](RilAccess/Provenance/Semantics.lean) |
| Theorem 3 | `Calls.every_prefix_authorized`, `Calls.source_progress`; supporting declaration/path lemmas | [Call proofs](RilAccess/Call/Proofs.lean), [access progress](RilAccess/Access/Progress.lean), [access proofs](RilAccess/Access/Proofs.lean) |
| Graph separation | `CoreEntry.separated_paths_cannot_alias`, `GraphAuthority.analyze_exact` | [Entry graph](RilAccess/Call/Entry.lean), [graph oracle](RilAccess/Graph/Authority.lean) |
| Theorem 4 | `entry_capture_exact`, `checked_at_entry_parameter_is_reachable` | [Entry capture](RilAccess/Call/Entry.lean), [summary checker](RilAccess/Call/Summary.lean) |
| Theorem 5 | `every_concrete_identity_survives`, `checked_distinct_fresh_objects`, `checked_fresh_origin_excludes_frozen_entry`, `checked_existing_origin_is_not_callee_local` | [Summary substitution](RilAccess/Call/Summary.lean) |
| Theorem 6 and effect conservation | `static_discharge_safe`, `handled_state_components`, `external_environment_blocks_discharge` | [Contracts](RilAccess/Contracts.lean), [effect boundary](RilAccess/Effects/Boundary.lean) |
| Theorem 7 | `aliases_cannot_resume_twice`, `operation_authority_ends`, `resume_keeps_committed_state` | [Resumption kernel](RilAccess/Effects/Resumption.lean) |
| Exactness limit | `source_reachability_iff_halting`, `no_computable_exact_decider` | [Limits](RilAccess/Provenance/Limits.lean) |
| Source-language transfer | `complete_sources_given_lowering`, with `Lowering` as premise | [Simulation](RilAccess/Provenance/Simulation.lean) |

The aggregate certificate is
[`CoreVerification.verified`](RilAccess/Verification.lean).
It packages these kinds of results with their distinct quantifiers and premises;
it does not compose the interfaces into an unrestricted execution theorem.

## Appendix B. Reproduction

From this artifact's directory, `formal/access`:

~~~powershell
uv run --locked python check.py
~~~

The command builds the library and executables, runs the examples, replays the
declaration audit, and executes all four rejection probes. Python is selected by
the local [`.python-version`](.python-version); uv creates this project's own
environment from [pyproject.toml](pyproject.toml) and [uv.lock](uv.lock).
The Python runner uses only the standard library. Lean and Lake must be installed;
the Lean toolchain is pinned in [`lean-toolchain`](lean-toolchain), and the project
has no external Lean package dependencies.

## References

1. Patrick Cousot and Radhia Cousot. 1977.
   [Abstract interpretation: a unified lattice model for static analysis of programs by construction or approximation of fixpoints](https://www.di.ens.fr/~cousot/COUSOTpapers/POPL77.shtml).
   *POPL*, pp. 238–252.
2. Gordon D. Plotkin and Matija Pretnar. 2013.
   [Handling Algebraic Effects](https://lmcs.episciences.org/705).
   *Logical Methods in Computer Science* 9(4:23), pp. 1–36.
3. A. M. Turing. 1937.
   [On Computable Numbers, with an Application to the Entscheidungsproblem](https://doi.org/10.1112/plms/s2-42.1.230).
   *Proceedings of the London Mathematical Society* s2-42(1), pp. 230–265.
4. Lean reference manual, version 4.33.0.
   [Axioms and transitive dependency inspection](https://lean-lang.org/doc/reference/4.33.0/Axioms/).
5. [Ril specification](../../doc/SPEC.md).
   Canonical language rules for access, provenance, effects and checking metadata.
