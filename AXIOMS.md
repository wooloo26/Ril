# Ril semantic kernel axioms

This document defines the architecture of `ril-compiler`, especially `sema/`.
`doc/SPEC.md` and `doc/STD.md` remain the language authority.
`DEVELOPMENT.md` records workflows, implementation gaps and unresolved
specification questions. Implementation techniques in this document do not
change language semantics.

The direction is to replace duplicated semantic truth and feature-pair patches
with explicit identities, complete type information, shared value operations,
owned analysis domains and independently checked derivations. Domain separation
does not prove a total O(N) algorithm. Graph relations, alias analysis, BDDs,
specialization and constraint solving have their own state spaces and costs.

## 1. Identity, history and control outcomes

### Distinguish kinds of identity

- Declarations, binders, patterns and types have canonical static identities.
  A declaration identity does not require a runtime occurrence.
- A value evaluation has its original HIR identity and an analysis occurrence
  in an explicit activation/context. Repeated evaluations without an allocation
  must still be distinguishable.
- Solver revisions and worklist visits are not new program executions.
  Allocation-recency cursors and resumption epochs are not occurrence IDs.
- Loops and recursion use finite abstract contexts and justified summaries.
  Do not enumerate an unbounded runtime trace or create new semantic identities
  indefinitely merely because a solver revisits a node.
- IDs are interpreted within their owning program/revision. Equal ordinals,
  names, graph contents or source coordinates do not authenticate an identity.

`Span` locates text for diagnostics and source-location queries. It must not be
the primary key of semantic state, obligations or validation joins. Use the
appropriate HIR/declaration ID and, where needed, its actual context/occurrence.

Generated syntax carries a typed origin and a real anchor. Catalog declarations
have stable catalog identities. Neither gets authority from fabricated AST
nodes with borrowed spans. Use `HirApplication` for actual call/pipeline roles
and `BlockIndex` for block membership and tails.

### Preserve history without freezing inference prematurely

An emitted observation's birth, context and recorded value remain immutable.
Later reads, receiving views and epoch changes derive new views with explicit
inputs and transitions; they do not rewrite historical observations.

A pending inference variable may acquire a checked solution in the constraint
store. Preserve its original identity, context and dependencies. This is
different from overwriting a previously observed value or replacing its Source
with information guessed from a final erased type.

### Record actual outcomes

An evaluation summary distinguishes its normal value from possible abrupt exits,
suspensions and control transfers. These alternatives may coexist under different
path conditions. Only the normal component can enter a normal value receiver.

An interrupted argument/default prefix retains the operands actually evaluated
and their effects and duties. It does not manufacture a constructor result,
callee body entry or completed default. A resume request and a completed protected
answer are distinct events. Do not substitute unit for an unavailable answer.
`Ty::Never` alone is not an execution-outcome certificate.

## 2. One semantic value, with complete scoped types

A canonical value descriptor links the following components:

| Component | Required information |
| --- | --- |
| Source/type view | Structural type, fixed dimensions, nominal identities, generic sorts, rows and public callable contracts |
| Interpretation | Authenticated declarations, substitutions and frozen contexts needed by that view |
| Heap/provenance | Origins, paths, correlations and formal loan participants |
| Capability view | Access permissions, publication, construction eligibility and active borrow restrictions |
| Recency/control | Birth and current epochs, protected answers and relevant continuation history |
| Duties | Result inspection obligations, optional refinements, resources and channel state |

These components may be immutable handles into domain stores. They do not need
to be copied into one giant struct. Each fact has one authoritative owner;
indexes and caches derive from that owner and cannot become competing truth.
Historical packets must retain the versions they actually observed.

### Source is a graph, not an erased shape

Complete Source information lives in a canonical finite graph. Recursive types
and contracts may use justified backedges; algorithms must handle cycles with
visited pairs, SCCs or other appropriate relations. An alias-only cycle is not
evidence of a productive recursive type.

Type, Const, Key, row, effect and provider parameters keep their actual sorts and
declaration identities. In particular, a Key coordinate is not a Type UID.
Standard declarations use authenticated catalog identities rather than
uninterpreted names borrowed from an arbitrary caller context.

Once a complete type view is available, runtime `Ty` is its consistent lossy
projection. During inference, partial shapes and constraint variables are valid
working information. They never authorize missing dimensions, Source
coordinates, permissions or contracts. Do not reconstruct these from erased
`Ty`, backing collection lengths, final heap contents or parsed witness keys.
Original literals, declarations and certified static values are genuine ingress
points; formatting a retained graph back into syntax is not a new origin.

### Preserve each dependency's interpretation

The physical evaluation context and a Source declaration/contract context are
different coordinates. A record may contain closures from different legitimate
declaration environments. Each scoped component must retain its own declaration
references and interpretation; one convenient `FrozenEnvId` must not overwrite
the interpretations of all children.

Composition, instantiation and rebasing require explicit checked relationships.
Equal environment contents or identical names do not establish those
relationships. Later lexical initialization must not silently redefine an
earlier declaration's captured interpretation.

Keep separate judgments for:

1. Authenticating a particular declaration, occurrence, snapshot or recipe.
2. Comparing semantic types/contracts under their authenticated interpretations.
3. Checking receiving compatibility and capability/duty transitions.

Exact occurrence, context or node identity may be required by the first
judgment without being the definition of semantic type equality. Conversely,
semantic equality cannot authenticate an origin. A fully resolved closed graph
can be equivalent across different environment IDs; an empty binder list alone
does not make opaque names or textual contracts environment-independent.

### Represent incomplete knowledge honestly

Distinguish pending constraints, available information, unavailable evidence,
invalid evidence, resource exhaustion and unreachable normal flow.
A genuine symbolic binder is not an erroneous unknown type.

Solve relevant pending constraints before the use that requires them, or before
final certification. An unrelated unresolved fact must not poison every value.
If a required proposition remains unproved, reject that use or report the
implementation limit. Never convert an error to absence, unknown to safety,
exhausted work to success, or a missing capture to an exemption.

## 3. Shared operations and receiving coverage

Use a small shared algebra with explicit preconditions and conclusions:

| Operation | Responsibility |
| --- | --- |
| Evaluate / construct | Produce actual value components and control outcomes |
| Receive | Check a completed value against a receiver and install its lawful view |
| Project | Select a constituent through an authenticated path and access view |
| Instantiate / ascribe | Derive a selected or constrained view without restoring erased authority |
| Copy / move / capture | Apply their distinct identity, aliasing and lifetime rules |
| Join | Combine reachable alternatives while preserving correlations and pending obligations |
| Transport | Derive an epoch/control view from actual history |

Receiving, joining and transporting are different operations. They share domain
judgments and evidence formats; they do not replace one another.
A default expression is evaluated before its result is received. A branch join
does not itself prove a value was received.

The following ten families form a coverage checklist, not ten identical
instances of a unary operation:

1. Local bindings and destructuring.
2. Supplied call and pipeline operands.
3. Default parameter evaluation and formal binding.
4. Records, tuples, variants, arrays and dynamic collection admissions.
5. Slot replacement and interior storage mutation.
6. Named/anonymous callable, iterator and handler captures.
7. Channel sends, receives and yielded payloads.
8. Effect arguments, resumption inputs and protected answers.
9. Control-flow alternatives and lexical block completion/drop.
10. Callable returns and module/static publication.

Each family supplies its genuine source/receiver roles, context and outcome,
then composes the common operations it needs. Necessary domain-specific
receipts are allowed. Duplicated type, provenance or permission truth is not.
Fixing a shared primitive benefits all consumers, but each adapter still needs
its own coverage and validation.

Receiving must preserve structural coordinates and install only the destination's
declared view. Product and callable ascription must check actual constituents
and body/probe evidence; copying an expected whole graph over unknown children
is not a proof. Deferred callable inference must preserve the original birth
and authenticate any later constrained current view.

Permissions cannot be amplified through an existing restricted handle. A legal
slot replacement, fresh copy or return of an existing parent loan has its own
transition; the entire machine is not a single ever-decreasing permission field.
An ended child/operation loan cannot be revived by resumption or by an unrelated
alias. Duties transfer with values and control flow; only actual inspection,
cleanup or another specified discharge rule can remove them.

## 4. Solving domains and checking certificates

Use owned domains with explicit interfaces and a shared identity vocabulary:

| Domain | Responsibility |
| --- | --- |
| Type/Source | Type graphs, inference, substitutions, scoped contracts and numeric selection |
| Heap/capability | Origins, access, loans, sharing, copies and recency |
| Application/effect | Evaluation roles, callable entries, effects, handlers and resumptions |
| Obligation/duty | Results, optionals, resources, channels and path-sensitive obligations |
| Termination/budget | Descent, loop/call summaries and finite-evaluation coverage |

These domains interact. Their ownership boundaries do not imply mathematical
independence. Exchange explicit constraints and reductions; do not make each
domain reconstruct another domain's state.

Each fixed-point computation defines its approximation order and convergence
mechanism: finite height, bounded contexts, widening, restricted refinement or
another justified method. Runtime transitions may start/end loans and change
knowledge; monotonicity concerns the analysis order, not every state field.
An implementation work limit is a resource guard, not a convergence proof or a
proof of program termination.

### Independent validation

Only complete, validated analysis can produce `VerifiedProgram`. Failed or
incomplete analysis still exposes an uncertified `AnalysisSnapshot`.

The producer emits typed derivations with original inputs, roles, contexts,
solutions and conclusions. The verifier checks their local premises and
conclusions against original HIR, trusted catalog/static inputs and referenced
history. Document those trusted inputs. Sharing pure graph relations,
normalizers and derived indexes is appropriate; trusting producer success flags,
rerunning inference, executing lambda bodies again or searching for missing
evidence is not certificate checking.

Coverage follows original syntax, control flow and actual analysis contexts.
Require evidence appropriate to each HIR/derivation role, including construction,
projection, completion, transfer and summary use. Do not require every expression
to have a receiving certificate. Check static/unreachable syntax according to
SPEC; do not invent execution records for untaken paths. Loop and call summaries
quantify over executions that are not individually enumerated.

Deleting or corrupting required evidence must reject certification. Deleting
an unused cache or irrelevant optional table need not reject a correct program.
A ledger's mere presence, or an empty table, is not coverage.

## 5. Bounded and deterministic implementation

- Charge shared implementation work before traversal, allocation and owned
  copying. Failed speculative work still consumes its allowance. Cache hits
  require the same original identities and versions as their inputs.
- Account for visited nodes/edges, relevant graph pairs, contexts and certificate
  size. Reuse indexes and shared immutable graphs instead of repeatedly scanning
  whole fact collections. Do not hide repeated work by increasing quotas.
- A shared arena identity does not prove that every immutable prefix snapshot
  contains a later root. Authenticate inputs in their own snapshots before a
  relational traversal or import.
- Keep language `Div`/static evaluation event accounting separate from compiler
  implementation work and memory limits.
- Deterministic inputs and a fixed target must produce deterministic diagnostics
  and IR. Use deterministic traversal and serialization. Pointer32 and pointer64
  may legitimately produce different layout-dependent results; host `usize`
  must not choose target layout.
- Preserve original evidence when work is exhausted. Report the appropriate
  missing-proof diagnostic or explicit implementation limit; do not mislabel
  an implementation resource limit as a proved language violation.

## 6. Compiler, standard library and runtime boundaries

Ordinary library behavior belongs to checked library definitions. The compiler
knows language operations and a small, explicit set of necessary intrinsic
contracts. The runtime supplies storage, execution and host capabilities. Moving
all existing name switches into a larger builtin table does not establish this
boundary.

| Owner | Responsibility |
| --- | --- |
| Compiler | Resolution, complete types, inference, receiving, capabilities, effects, duties, termination, primitive contracts and lowering |
| Standard library | Ordinary data declarations, collection and iterator combinators, ordering algorithms, formatting and resource/I/O composition |
| Runtime | Allocation/GC, object storage, low-level operations, continuations, cleanup, scheduling, host calls and opaque handles |

### One declaration and call path

Load versioned standard-library sources through the same module, declaration,
visibility and checking infrastructure as user sources. Prelude bindings are
imports of real declarations. A standard module's spelling does not supply a
type, implementation, effect, permission or termination proof.

Distinguish source definitions, trusted primitive declarations and anchored
generated declarations in the common declaration store. All have stable
declaration, parameter and binder identities. A primitive's public wrapper may
be an ordinary library function. Primitive bindings and language-item roles are
sealed identities checked against their declared shape; arbitrary user names,
attributes or lookalike module paths cannot manufacture them.

Resolve calls to declaration/instance identities or actual callable values.
Ordinary calls, aliases, first-class functions, defaults, captures and library
calls use the same argument plan, receiving transitions and callable summaries.
Do not create temporary parameter ASTs with caller spans to stand in for a
missing declaration. A missing callee in lowering is an error, never an implicit
request for runtime builtin-name dispatch.

### Keep the intrinsic boundary small and explicit

An intrinsic is justified by a language operation, an unforgeable identity or
capability, an opaque representation, or access to an external execution
mechanism. An ordinary algorithm's current implementation difficulty is not by
itself a reason to make its public name intrinsic.

Each admitted primitive has one authoritative declaration/contract containing
its identity, complete type scheme and parameter modes, phase availability,
effects, capability and duty transitions, termination/budget behavior, and its
backend/runtime binding where applicable. The contract may compose shared
domain operations; a signature alone does not prove aliasing, cleanup or callback
behavior. Abstract checking, static execution and native execution remain
different consumers of that contract.

Typical primitive families include numeric and structural operations, storage
admission and resizing, graph copy/publication, windows and access reservations,
effect/continuation operations, scheduling and host resource access. Algorithms
such as map/filter/fold, iterator adapters, sorting, read-all/write-all and
resource wrappers should be ordinary checked bodies whenever their contracts
can be expressed through those families.

Preserve existing Source graph catalogs and trusted identities where they
describe genuine primitives. Move ordinary record/sum definitions into the
library as their consumers migrate, retaining any required language-item role.
Do not replace one set of hand-maintained signatures with another parallel set.

An efficient native implementation may remain behind an explicit library
binding. This does not give the compiler knowledge of its public algorithm or
permission to assume a bodyless foreign function terminates. Optimized ordinary
definitions must first be checked, and their replacements must preserve the
declared data, control, authority and budget behavior. A checked ordinary
implementation remains the reference path.

### Share semantic elaboration across execution phases

Static execution consumes the eligible subset of the same elaborated
declarations, type graphs, operations and control-flow representation used by
ordinary compilation. It should not maintain a second language checker or a
second implementation of every ordinary library algorithm.

Type elaboration can request constant/type computation, and that computation
can require elaboration of another declaration. Represent those dependencies
explicitly, with staged queries, original environments and cycle handling;
do not assume the entire program can be fully typed before any static query.
Concrete static execution is not a replacement for checking symbolic inputs
or unreachable branches.

Phase availability remains a declaration property under SPEC/STD. Migrating a
dual-phase standard function into a source file does not make arbitrary pure
runtime functions callable statically. The interpreter uses target layout and
an isolated value store; it cannot acquire host I/O by calling the general
runtime dispatcher. Pure scalar/encoding implementations may be shared where
their semantics agree, without sharing host handles or mutable runtime state.

Keep abstract language events explicit through elaboration, specialization,
inlining and CPS. Moving a library loop or callback into an ordinary body must
not silently add or remove specified budget charges, change callback order,
hide suspension or alter cleanup/failure behavior. Necessary phase, mode or
event contracts that current public syntax cannot express remain explicit,
bounded trusted declarations; exposing new language syntax is a separate
specification decision.

### Normalize the remaining temporary paths

| Temporary path | Required replacement |
| --- | --- |
| Runtime Ty, static Ty and textual witnesses competing as complete types | One authoritative scoped Source graph and constraint store; execution/layout shapes are derived views |
| Late AST reconstruction for accessors, adapters, defaults and static values | Origin-preserving HIR lowering, real argument plans and constant/type-value references |
| Same birth packet mutated into a receiving view without a retained transition | A shared receiving derivation linking actual input, receiver, declaration interpretation, capability/duty changes and output |
| Declaration assumptions, default preparation, untaken paths and actual execution mixed together | Explicit roles and control outcomes; check syntax without inventing executable events |
| Ordinary library algorithms generated after semantic certification | Check their real bodies before lowering; backend transforms existing typed operations |
| Public-name or Span-based specialization and callback classification | Declaration/instance IDs, typed primitive metadata and checked effect summaries |
| Per-feature history tables and verifier searches | Shared allocation, storage, call and control histories with indexed references and local derivations |
| Repeated AST execution or larger quotas used as a recursion/loop solution | Domain fixed points, explicit approximation orders and reusable checked summaries |

Domain-specific adapters remain legitimate, but they compose the shared
operations. Adding a library function or a new value representation must not
require a new parallel type system, execution model or authority checker.

## 7. Execution order and completion criteria

Migrate through end-to-end slices, not by enabling a new universal validator
before its producers and protocols exist.

1. **Restore a reviewable baseline.** Finish or remove partially connected
   implementation changes and resolve newly introduced regressions. Retain
   honest acceptance/failure identities; an unbuildable intermediate state is
   not the starting acceptance baseline for the architecture migration.
2. **Define the boundary and common ingress.** Classify library operations by
   ownership, settle the small primitive contracts and load real library
   declarations. Unify declaration/parameter identity, scoped types, explicit
   assumptions, argument plans and receiving derivations. Keep existing domain
   graphs and verification that already satisfy these contracts.
3. **Prove one complete library slice.** Start with an optional-value combinator,
   then Array::map to exercise generic callbacks, traversal, allocation and
   duties. Compile the same checked body through ordinary calls, first-class
   uses, eligible static execution and native execution. Fix missing generic
   language mechanisms instead of adding another public-name exception.
4. **Delete each replaced path in the same migration.** Remove that family's
   checker simulation, static algorithm copy, late HOF body generator, runtime
   algorithm dispatch and duplicate classification lists. Preserve genuine
   low-level primitives. Extend to other collection/iterator/order algorithms,
   then resource and buffered-I/O composition as their common protocols close.
5. **Complete shared phases and receiving coverage.** Replace remaining static
   checker/AST bridges and lossy type adapters as their consumers move. Reuse
   common operations across storage, captures, defaults, channels, handlers,
   resumptions and publication. Implement recursion/loop summaries and actual
   control outcomes; do not defer domain ownership until every legacy field has
   acquired a second representation.
6. **Validate the complete compiler.** Preserve positive and negative cases,
   original case identities and execution coverage. Check both pointer layouts,
   Windows MSVC, Linux GNU and applicable native execution. Run bounded model
   audits with their documented scope.

A slice is complete only when its lawful programs work and its required
rejections remain correct. Conservative rejection is necessary when proof is
absent, but adding false rejections is not successful language implementation.
Track changed failure sets, not only totals. Unknown, unimplemented, timeout,
crash and empty selection are never passes.

For an ordinary library slice, additionally require:

- Adding or changing its algorithm requires library source/tests, not new
  compiler dispatch branches or runtime algorithm state machines.
- Renaming, aliasing, re-exporting and first-class use retain the same checked
  declaration behavior; a user's lookalike name receives no builtin privileges.
- Static/native executions agree on admissible data and order. Test callback
  effects, suspension, failure, duties, empty inputs, fixed/dynamic views,
  nested closures and exact language-event accounting where applicable.
- The replaced implementation and its private compatibility routes are gone.
  CI checks dependency boundaries, primitive bindings and the absence of new
  public-library-name dispatch outside explicitly retained migration adapters.

This roadmap supports completing the compiler under SPEC/STD. Completing a
representation refactor, passing a focused suite, or renaming stores does not
by itself complete either the kernel or the compiler.
