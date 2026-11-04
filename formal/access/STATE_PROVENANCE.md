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
reachability, frozen call-entry origins, summary substitution, confined functional
graph updates, local discharge and affine resumption. The central distinction is
between an object's origin, the authority of a path to it, and the role of an
origin in a summary.
Conflating these notions permits false freshness or false locality conclusions.
The artifact passes 255 positive and adversarial checks and a transitive axiom
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
further results under their own interfaces. A draft kernel additionally permits
variable-shape collection updates while preserving immutable input snapshots.
These results are collected in one certificate, but their conjunction is not a
soundness theorem for an unrestricted
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

Successful provenance analysis does not establish definite initialization or
execution progress. Its missing-operand diagnostic asks whether the global
may-source solution contains a source, not whether every incoming path has
initialized the operand. For example, a CFG that first reads register 7 and then
seeds it is accepted, although its initial configuration has no concrete step.
The artifact proves both facts for this counterexample. Grounded Horn derivation
does not imply temporal availability. A frontend needs a separate well-formedness
judgment; the finite access/call checker in Section 4 separately proves progress.

### 3.4. Identity is not an explanation label

A graph can contain two provenance explanations for one object. Traversing it
by equality of the entire origin tuple would incorrectly disconnect those
explanations. For example, an edge from object 1 with label A to object 2 must
also be visible through an argument naming object 1 with label B. Otherwise the
argument's region could falsely appear separate from object 2.

Physical graph closure therefore uses object IDs. Normalization retains every
known source label for a reached ID, and verifies agreement of its activation,
task and scope metadata. Conflicting ownership is diagnosed rather than selected
arbitrarily. The provenance CFG additionally proves a birth/identity invariant:
old origins are preserved and each newly allocated ID is above existing IDs.
Represented argument roots from such a trace can consequently be frozen without
assuming a consistency flag from the caller.

This is an internal representation result. Mechanism and context labels in the
CFG are not proofs of actual dynamic activation freshness or a handler/call
dispatcher. Boundary metadata must still correspond to the real execution.
Tree-shaped permissions also retain their full region key, allocation plus
coordinate, rather than flattening every subobject to its root allocation ID.

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
E_x=\{i\mid \exists r\in R_x,\;\operatorname{PhysicalReach}_{H_0}(r.\mathrm{object},i)\}.
$$

**Theorem 4 — Exact physical entry capture.** The validated snapshot contains
precisely the object IDs in $E_x$ and retains every recorded origin explanation
for them. Every accepted formal selection has a recorded source and a physical
path from a saved argument root in $H_0$. All formals share one frozen heap and
preparation boundary; arbitrary inferred source lists are not accepted instead.

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

## 6. Functional updates with variable collection shape

A functional update must preserve the immutable input even when its recipe
changes a collection's length. The specification distinguishes this from a
change to the data type: array/map/set contents may change shape, whereas tuple
arity, record fields and a selected variant's declared shape remain fixed.
The [derive rules](../../doc/SPEC.md#functional-updates-via-derive) also require
one draft counterpart per source object, including inserted immutable objects.

The generic draft kernel represents an ordinary object by its origin, a storage
schema and an ordered list of constituent values. A fixed schema records member
types and modes; a variable schema records the homogeneous entry type and mode.
A canonical schema registry prevents a type tag from being reused with a
different declaration. The checker validates normalized immutable reception modes
and source-graph consistency. Mere absence of a writer does not make a
`ref` reception immutable.

Inputs are a finite closed catalog of immutable source objects, including
admitted insertion candidates, an old-object reservation set, schemas, received
modes and outside authority/environment metadata. Those metadata must describe
the actual checked boundary. The reference policy makes a complete logical copy
of the catalog. With $B$ above all reserved old identities, it assigns

$$
\phi(i)=B+i.
$$

Every copied reference uses the same injective function. Thus two fields pointing
to one source array also point to one draft array. Rewriting that array's entries
changes what both draft aliases observe; the original array retains its complete
contents, order and length. Inserting another admitted immutable object uses its
existing counterpart. Recipe-local allocation uses a separate fresh range.

A single typed contents-rewrite operation expresses collection insertion,
deletion and reordering. It changes a variable-length payload while preserving
its storage schema. Fixed storage checks the exact number of members, so the same
operation cannot enlarge a tuple or add a record field. Declared member modes
remain unchanged: the extra writing privilege belongs to the active private
draft phase. It does not modify ordinary access attenuation.

**Theorem 6 — Checked functional graph updates.** A finite recipe accepted by
the draft checker has a matching execution under unchecked graph operations.
Throughout its checked execution, every input catalog object retains its
original contents and metadata, and every materialized source counterpart
retains its identity and declared schema. A normally published result has the
input root's schema and immutable access. Publication ends the draft phase;
abort publishes no result and preserves prior external state/effect events.

*Proof idea.* Draft writes and local allocations address only identities above
the old-object boundary. A memory frame theorem therefore preserves the actual
old cells, rather than merely retaining a snapshot field. Rewrites keep each
cell's origin and schema. Type preservation connects newly assigned references
to existing cells of the declared type. Path transport proves that the initial
copy preserves finite paths, aliases and cycles; later edge changes are exactly
the requested rewrites. The counterpart identity is independent of the path or
current collection index.

Only terminal publication exposes a result handle. Checked transitions cannot
use any old draft alias after the shared phase closes. External observations carry events, effects and a footprint of roots,
environments and escaping references. A known footprint must exclude the private
region, including contained/captured references behind an old wrapper object.
An unresolved footprint remains an obligation and cannot be treated as empty.
Under the named completeness/conformance premise, external observations cannot
expose a draft identity or write, transfer or retain a writer to an input object. Their declared events remain in the log on both normal
completion and abort. Confined draft writes can be discharged; outside captured
environments continue to block unjustified discharge.

External instructions record observations of separately checked operations.
They do not execute or authorize an external body; its access, alias and lifetime
conditions still belong to the caller and implementation conformance boundary.

Operation-derived finite Horn rules cover the kernel's recorded state events
at every checked finite prefix. A separate invariant bounds the sources of all
heap cells and published outputs by the catalog sources and the fresh producer.
A named world invariant is proved from initialization and local step deltas:
input cells are framed, types remain valid, the old/private heap cut stays
sealed, and accepted boundary footprints are known. Every prefix of an accepted
recipe's independent unchecked execution inherits this invariant and source
coverage. Agreement only at the final state would be insufficient.

This kernel is a permitted reference policy for resolved ordinary shared-object
recipes. It copies the whole admitted catalog for changed results and can reuse
the source root for a no-op. More selective sharing or lazy materialization needs
a correspondence argument preserving these invariants. Arrays, maps and sets
instantiate ordered homogeneous entry storage; key uniqueness, hashing,
iterator validity and specific library operators remain their own contracts.
The kernel neither derives general symbolic recipes from source nor replaces
the caller's checks of deep immutability and lifetimes.


## 7. Handling effects without hiding state

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
obligations and named reads, respectively. For handled family $h$, the boundary
kernel eliminates $h$ from the protected body's effect row before combining it
with the operation arm and residual cleanup summaries:

$$
\mathcal E_{\mathrm{out}}=
(\mathcal E_{\mathrm{body}}\setminus\{h\})\cup
\mathcal E_{\mathrm{arm}}\cup\mathcal E_{\mathrm{cleanup}}^{\mathrm{res}}.
$$

An arm uses outer handlers even when it requests its own family. Consequently,
an arm whose summary contains $h$ must leave $h$ outward; an enclosing handler
can discharge that obligation later. Filtering the combined rows would wrongly
make this example appear effect-free. `handled_effects_exact` proves the precise
membership equation and is part of the aggregate certificate.

Cleanup summaries here contain residual obligations after resolving the handlers
at each cleanup site. Cleanup effects handled inside the protected body belong
to its body summary instead. Establishing this site-specific dispatch is a
boundary correspondence obligation, not a behavior implemented by this kernel.
All body, handler and cleanup state components are combined unchanged;
effect elimination never removes state.

### 7.1. When local state may be discharged

Local discharge needs a footprint of authority roots, environments and escapes.
The footprint must include handler and cleanup environments, even when they
are absent from the body's own roots. Checking only the body can incorrectly
classify state as confined.

**Theorem 7 — Sound discharge under coverage.** If an abstract footprint covers
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

### 7.2. Affine resumption through shared identity

A copyable `used` flag is insufficient to establish affine resumption.
Two handles might each retain a copy that still says “unused.”
The resumption kernel therefore gives aliases one identity and stores
consumption in a shared ledger.

Successful resumption consumes that identity before continuation execution and
checks the arm, callable, task and operation scope. Its authority state is the
actual token/loan ledger used by the access checker. Mutable temporary roots
are computed from that ledger; readonly observations and retained parameters
are not revoked simply because they belong to the same scope.

Lifetime dependencies are distinct from token origin ancestry. The checker
validates dependency closure and token identity/freshness. Resumption ends the
mutable roots and releases loans whose views depend on them. Derived views
become unusable through their ended dependencies, while independent retained
rights and outer authority components remain intact. A token's active bit alone
is not a usable permission. Current access resolves the current ledger; an
unchanged historical evidence snapshot proves only that the earlier access was
legal. Actual handoff likewise uses these token transitions, not a separate
flag-based authority model.

**Theorem 8 — No second resumption through an alias.** After one successful
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

## 8. Why exactness has a different limit

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

## 9. Validation and evidence

The reported results cover the core and generic draft extension distributed with
this paper, using Lean 4.33.0 and its bundled libraries. Verification passed
260 positive and adversarial fixtures, including identity, lifetime, effect
routing and initialization counterexamples, plus ten audit rejection probes.
Declaration/theorem counts are diagnostic output,
not the completion criterion: ownership of compiled modules and the entire
source import closure determine what is audited.

Representative cases exercise complementary sides of the checks:

| Case | Expected and observed result |
| --- | --- |
| A legal shared alias with its source obligation | Accepted; hidden-source variant rejected |
| A cyclic graph and a shared descendant | Reachability retained; false separation rejected |
| A permutation of distinct objects | Accepted with joint alternatives |
| Unknown selections that may overlap | Separation rejected |
| Insertion after call entry | Current reachability retained; entry-origin claim rejected |
| Captured allocation or parameter origin | Original identity preserved |
| A collection grows, shrinks or reorders its entries | Accepted; base contents and aliased counterparts preserved |
| A tuple gains a member, or a schema/type tag is forged | Rejected |
| An immutable insertion is later edited | Its draft counterpart changes; the source object stays unchanged |
| A readonly reception without immutable admission | Rejected |
| Draft capture/retention or an external write to an input | Rejected |
| Local mutation with an outside handler environment | Discharge blocked |
| An operation arm requests its own handled family | Its effect remains outward; an outer handler can discharge it |
| An already-resolved cleanup has the same residual effect | Its obligation remains outward |
| A CFG reads a register before its later seed | Provenance analysis accepts; concrete first-step impossibility is proved |
| A second resume through an alias | Rejected; independent authority remains usable |
| One physical parent with two source labels | Child path retained; false separation rejected |
| Conflicting owner metadata for one ID | Entry validation rejects the contradiction |
| A dependent observer after resume | Current view fails; old historical evidence remains historical |
| An old event wrapper with a private captured reference in its footprint | Rejected |
| Unknown external footprint | Remains unresolved; cannot justify discharge |

The acceptance cases are important: a checker that rejects every program could
satisfy a safety implication without providing a useful analysis. The fixtures,
a nonempty concrete provenance execution, and the finite calculus's progress
theorem supply distinct evidence against that failure mode. Fixtures supplement
the universally quantified proofs; they cannot replace them or establish
unmeasured performance or full-language coverage.

The axiom audit examines declarations owned by project modules, including those
in other namespaces, private/generated helpers, fixture proofs and validation
entrypoints. It also verifies that every model source module is imported into
the audit environment. Both completed entrypoint modules, `Audit` and `Main`,
are imported and scanned separately. A source-local audit only sees declarations
preceding the command; replaying it cannot establish coverage of the completed
module. A regression probe compiles a module whose local audit passes before a
trailing axiom, then verifies rejection when the completed module is imported.
Namespace spelling cannot hide a project declaration. The permitted union is exactly `propext`, `Classical.choice`
and `Quot.sound`. No custom unproved axiom, unfinished proof or unsafe project
declaration is accepted. Negative probes exercise added and inherited axioms, `sorryAx`, unsafe code,
native proofs, cross-namespace declarations, unaudited source modules and
`implemented_by`/`extern` replacement of logical definitions. Standard-library
implementations remain outside this project-owned declaration scan; transitive
axiom dependencies are still checked.
This follows the distinction between kernel-checked proofs and proofs that
introduce additional compiler-trust axioms described in the
[Lean reference](https://lean-lang.org/doc/reference/4.33.0/Axioms/).

## 10. Interpretation and remaining obligations

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

Ordinary aggregates, closures, `via`/`infer`, clone and concrete storage APIs
must be audited as instances of these obligations. Derive now also has the
generic checked graph kernel of Section 6; source recipes, optimized copying
strategies and collection-specific operators still require correspondence to
its stated invariants and premises. This avoids replacing a
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

### 10.1. Reading the certificate

| Evidence class | Meaning |
| --- | --- |
| Mechanical result | The stated checker/semantics and its validated representation invariants imply the theorem; no proof placeholders or project axioms are used |
| Contract premise | Actual reserved identities, owner epochs, reception modes, authority roots, summaries and complete external footprints must describe the real boundary; `ExternalConforms` and `OperationConforms` name the relevant obligations |
| Remaining correspondence | Source lowering, symbolic summary generation, concrete collection algorithms, optimized sharing and external implementations still need their own arguments |

Structural checks establish consistency of supplied metadata, not truthfulness of
an opaque body. They cannot replace a body-summary proof. Conversely, uncertainty
cannot become a favorable permission or a missing environment. The mathematical
interfaces make that distinction explicit rather than hiding it in a large
aggregate of unrelated helper propositions.

## 11. Conclusion

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
| Provenance acceptance without progress | `future_seed_accepted`, `future_seed_has_no_first_step` | [Provenance cases](RilAccess/Examples/Provenance.lean) |
| Theorem 3 | `Calls.every_prefix_authorized`, `Calls.source_progress`; supporting declaration/path lemmas | [Call proofs](RilAccess/Call/Proofs.lean), [access progress](RilAccess/Access/Progress.lean), [access proofs](RilAccess/Access/Proofs.lean) |
| Graph separation | `CoreEntry.separated_paths_cannot_alias`, `GraphAuthority.analyze_exact` | [Entry graph](RilAccess/Call/Entry.lean), [graph oracle](RilAccess/Graph/Authority.lean) |
| Theorem 4 | `Identity.objects_exact`, `CoreEntry.snapshot_objects`, `snapshot_sources_complete`, `checked_at_entry_parameter_is_reachable` | [Entry capture](RilAccess/Call/Entry.lean), [summary checker](RilAccess/Call/Summary.lean) |
| Theorem 5 | `every_concrete_identity_survives`, `checked_distinct_fresh_objects`, `checked_fresh_origin_excludes_frozen_entry`, `checked_existing_origin_is_not_callee_local` | [Summary substitution](RilAccess/Call/Summary.lean) |
| Theorem 6 | `checked_recipe_prefixes`, `trace_invariant`, `old_root_cannot_reach_draft`, `base_snapshot_preserved`, `source_counterpart_persists`, `copy_preserves_paths`, `trace_well_typed`, `published_schema_preserved`, `publication_ends_privilege` | [Draft execution/checking](RilAccess/Draft/Core.lean), [graph/type proofs](RilAccess/Draft/Proofs.lean), [boundary proofs](RilAccess/Draft/Boundary.lean) |
| Draft admission, source coverage and exits | `admitted_mode_is_immutable`, `admitted_inputs_have_no_writer`, `recipe_source_coverage`, `trace_sources`, `conforming_external_cannot_escape`, `external_state_survives`, `abort_preserves_state` | [Draft proofs](RilAccess/Draft/Proofs.lean), [state/publication](RilAccess/Draft/Boundary.lean), [Draft cases](RilAccess/Examples/Draft.lean) |
| Theorem 7 and effect conservation | `static_discharge_safe`, `handled_effects_exact`, `handled_state_components`, `external_environment_blocks_discharge` | [Contracts](RilAccess/Contracts.lean), [effect boundary](RilAccess/Effects/Boundary.lean) |
| Theorem 8 | `aliases_cannot_resume_twice`, `derived_access_ends`, `dependent_operation_loan`, `retained_authority_survives`, `resume_keeps_committed_state` | [Resumption kernel](RilAccess/Effects/Resumption.lean) |
| Exactness limit | `source_reachability_iff_halting`, `no_computable_exact_decider` | [Limits](RilAccess/Provenance/Limits.lean) |
| Source-language transfer | `complete_sources_given_lowering`, with `Lowering` as premise | [Simulation](RilAccess/Provenance/Simulation.lean) |

The aggregate certificate is
[`CoreVerification.verified`](RilAccess/Verification.lean).
It groups principal solver, provenance, access, entry, effect and draft results.
Auxiliary consequences remain with their owning modules. Core imports exclude
examples; the separate example aggregation and executable entrypoints are all
included in the audit. The grouped certificate preserves distinct quantifiers
and premises rather than composing them into an unrestricted execution theorem.

## Appendix B. Reproduction

From this artifact's directory, `formal/access`:

~~~powershell
uv run --locked python check.py
~~~

The command builds the library and executables, runs the examples, replays the
declaration audit, and executes the audit rejection probes. Python is selected by
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
