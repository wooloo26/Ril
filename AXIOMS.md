# Ril compiler architecture

`doc/SPEC.md` and `doc/STD.md` define the language. This document constrains
implementation, not language semantics. `DEVELOPMENT.md` records the build
workflow, remaining implementation gaps and unresolved specification questions.

The first release is a complete compiler. Internal APIs, data structures, IR,
ABI and implementation tests have no compatibility guarantee. Replace an
inadequate design and delete its consumers together; do not maintain parallel
versions, compatibility bridges or a second implementation of the language.

## 1. One semantic representation

Resolve names to declaration and binder identities. Source positions locate
diagnostics; they do not identify declarations, values or executions. Generic
arguments retain their sorts: Type, Const, Key, row, effect and provider.

Use one authoritative complete type store and one constraint store. Types retain
fixed dimensions, nominal identities, rows and callable modes/contracts. Scope
and substitution belong to resolved references, not reconstructed name strings.
Recursive types use finite graphs and cycle-aware relations. Partial inference
is valid working state; it cannot authorize a use requiring a solved type.
Machine/layout shapes are derived only after the relevant semantic checks.

Type elaboration, semantic analysis, static execution and lowering consume the
same declarations and elaborated operations. Constant computation and type
elaboration may request each other through staged, cycle-aware declaration
queries. Static execution uses target layout and an isolated value store.
It does not provide a second type checker or a second library implementation.

Keep syntax HIR, typed/control-flow IR and backend IR only where each has a
concrete responsibility. A backend receives executable operations and the
metadata needed to compile them, not a copy of the frontend analysis history.

## 2. Semantic checking is trusted compiler code

The first release does not require independently checkable certificates for
all semantic analysis. Remove certificate production, cross-phase proof copies
and replay engines as their consumers are replaced. Do not leave them running
as a second mandatory path or move the same machinery into a debug-only compiler.

The semantic analyzer remains responsible for every SPEC/STD rule: types,
capabilities and borrowing, effects, duties, resources, channels and termination.
Removing certificate replay does not remove these checks. A checked program can
be constructed only after all required analysis succeeds. A missing required
fact, exhausted analysis, timeout or unimplemented path cannot count as success.
Expose incomplete analysis for diagnostics without authorizing compilation.

Use ordinary IR validation for declaration references, operand/result types,
control-flow structure, phase prerequisites and backend invariants. Pure graph
relations, domain algorithms and indexes have one implementation. Test semantic
behavior and the invariants actually used by the compiler, rather than requiring
it to reject arbitrary mutations of obsolete proof packets.

## 3. Values and control flow

A semantic value links its complete type with the heap, access and duty facts
needed by the language. Each fact has one owner. Do not duplicate it across
syntax witnesses, erased types, frozen packets and independent reconstruction.
Retain lexical interpretations and substitutions where needed by closures and
generic contracts; copying an entire environment for every observation is not
an architectural requirement.

Keep declaration identity, allocation identity and execution context distinct.
Repeated solver visits are not executions. Loops and recursive calls use finite
abstract contexts, fixed points and reusable summaries, not unbounded traces.
Define an approximation order and convergence mechanism for each analysis.
A work quota guards resources; it is not a termination or convergence proof.

Represent normal results, abrupt exits, suspension and control transfers
explicitly. Only an actual normal result enters a normal receiver. Interrupted
argument/default prefixes retain evaluated effects and duties without inventing
a result or entering the callee. A resume request is distinct from the protected
computation's eventual answer; never substitute unit for an unavailable answer.

Shared operations perform construction, receiving, projection, instantiation,
ascription, copying, moving, capture, joining and control/recency transport.
These operations preserve the language's different identity and access rules.
All bindings, operands, defaults, aggregate/storage writes, captures, channel
payloads, effect/resumption inputs, branch results and returns use them.
Do not create another type or permission system for a feature combination.

Capabilities cannot be amplified through restricted handles. Ended loans cannot
be revived by unrelated aliases or resumptions. Duties follow values and control
flow until an actual specified inspection, transfer or cleanup discharges them.
Path joins preserve the correlations required by these rules.

## 4. Compiler, library and runtime

| Owner | Responsibility |
| --- | --- |
| Compiler | Resolution, types/constraints, semantic checks, specialization and lowering |
| Standard library | Ordinary data declarations, collection/iterator algorithms, ordering, formatting and resource/I/O composition |
| Runtime | Allocation/GC, storage, continuations, cleanup, scheduling, host calls and opaque handles |

Standard-library sources use the same declarations, visibility, type checking
and compilation as user sources. Aliases, re-exports and first-class uses resolve
to the same declaration or callable. A public module/function spelling confers
no privilege. The compiler knows only language operations and a small explicit
set of primitive contracts with sealed identities.

Each primitive has one declaration containing its full type scheme, parameter
modes, phase availability, effects, access/duty transitions, termination/budget
behavior and runtime/backend binding. Ordinary implementation difficulty is not
a reason to introduce another primitive. Map/filter/fold, iterator adapters,
sorting and resource/I/O wrappers are ordinary checked bodies wherever these
primitive families express their behavior.

Static execution and native code consume those same elaborated definitions.
Preserve specified callback order, suspension, cleanup and language-event budget
charges through specialization, optimization and CPS. Static phase availability
remains a declaration property; purity alone does not enable static execution.

## 5. Execution and acceptance

Replace the semantic main path in coherent blocks. Preserve useful parser,
module, domain-algorithm, backend and runtime implementations. Do not retain an
obsolete core merely to preserve its internal API, proof layout or test counts.

1. Remove the mandatory certificate/replay architecture and unnecessary proof
   transport. Keep all actual language checks and required backend metadata.
2. Unify declarations, complete types/constraints and typed operations. Route
   calls, closures, generics, defaults and control flow through that model.
3. Complete shared flow analysis, recursion/loop summaries and static execution.
   Delete the replaced type representations, AST execution bridges and adapters.
4. Compile ordinary library bodies and delete their duplicated checker, static,
   backend-generated and runtime algorithms.
5. Complete language behavior and native acceptance across Windows/Linux and
   both pointer layouts where applicable.

Intermediate commits may expose unfinished work, but missing checks or false
rejections are never completion. Track positive and negative language behavior,
changed failure identities and real execution coverage. Preserve corpus cases;
rewrite internal tests when their representation is removed. Unknown,
unimplemented, timeout, crash and empty selection are never passes.

Use focused regression checks during implementation and a full relevant matrix
at coherent boundaries. Avoid repeated full linking without a new reason.
Deterministic inputs/targets produce deterministic diagnostics and IR. Bound
analysis memory/work, distinguish implementation limits from language errors,
and keep compiler work accounting separate from language Div/static events.
