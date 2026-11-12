# Type System Implementation Guide

This is a non-normative guide for implementing the static semantics in
[SPEC](SPEC.md). The specification is the sole source of language requirements.
The pipeline, records, worklists, and milestones below are implementation
suggestions, not additional acceptance conditions or a prescribed compiler API.

Start with [Static Semantics and Type Kernel](SPEC.md#static-semantics-and-type-kernel).
Read each kernel judgment together with the language section it references.
The kernel connects the rules; the feature sections provide their detailed
syntax, eligibility conditions, execution behavior, and diagnostic codes.

## Reading and Implementation Order

A useful first implementation slice is a resolved expression with a known
expected type, an explicit local environment, and no unresolved generic argument.
Expand that slice in the following order:

1. Declaration identities, sorts, well-formed types, and definitional equality.
2. Bidirectional expression checking, normal continuations, and structural joins.
3. Generic evidence, row constraints, patterns, and GADT branch equalities.
4. Anonymous generalization, fixed storage schemas, and callable matching.
5. Authority, provenance, closures, calls, and recursive semantic summaries.
6. Handler boundaries, local discharge, Div, budgets, and phase restrictions.
7. Source annotation validation, interfaces, explanations, and dependency invalidation.

These are milestones, not isolated semantic layers. A record projection already
needs member modes; an early callable representation already needs space for its
complete contract. Implementing a milestone does not certify programs that use
unimplemented obligations from a later one.

For each slice, keep an accepted derivation and a nearby rejected derivation.
Examples are linked in the coverage matrix below. Until a Ril frontend exists,
these are specification cases for manual derivation and independent review.

## Information Carried Through Checking

The following records are a useful decomposition of the contexts and results in
[K-CTX](SPEC.md#static-contexts-and-judgment-forms) and
[K-IFACE](SPEC.md#semantic-interfaces-and-diagnostic-boundaries).
Their names and physical representation are deliberately left to the compiler.

| Information | Useful contents | Keep separate from |
| :--- | :--- | :--- |
| Declaration environment | Stable declaration and scope identities, visibility, application signatures, primitive identities | Display names and import spellings |
| Static binders | Type/constructor, const-value, member-mode, and row binders with their sorts | Runtime storage locations |
| Inference state | Unsolved metavariables, substitutions, dependencies, scope levels, explanation sites | Rigid generic parameters |
| Local equality evidence | Branch-scoped type equations and their derivations | Global substitution of rigid parameters |
| Storage environment | Declared data type, fixed schema, binding mode, initialization state | The current selected object's identity |
| Path facts | Effective access, member modes, possible origins, scope/task ownership, construction history | Requested receiver modes |
| Flow facts | Reachability, normal continuations, stable refinements, invalidation dependencies | Static branch selection |
| Callable contract | Parameter/result shapes and modes, full rows, environment, sources, conditional dependencies | The surface annotation alone |
| Origin relations | Root/contained origins, call-entry selections, aliases, disjointness, output correlations | A union of unrelated source names |
| Static evaluation request | Expression, required inputs, call family, abstract target, compiler budget | Source `div_budget` allowances |
| Diagnostic explanation | Rule, source span, originating declaration, propagation/dependency edges | A type accepted for program use |

In particular, an inferred type and a verified storage schema are different
objects in this design. An assignment checks the existing schema; it does not
rerun the declaration's reception inference to choose a new schema.

The inferred contract is also larger than its source spelling. Anonymous
annotations may be absent, and genuine `via` or callback dependencies can remain
symbolic, while checking still retains the full semantic information.

## Compiler Mainline

The mainline is a dependency graph rather than a mandatory sequence of passes:

```text
declaration identities and application signatures
  -> kind/sort checking and type formation
  -> bidirectional constraints <-> required static evaluation
  -> recursive summaries, access, effects, and phase obligations
  -> normalization and source-contract validation
  -> verified semantic interfaces and explanations
```

An implementation may interleave these operations, cache completed judgments,
or run a worklist over strongly connected components. Its scheduling choices
still need to preserve the evidence and failures described by the specification.

### 1. Resolve Declarations and Application Signatures

Input: source units, import relationships, declaration headers, and lexical scopes.

Output: resolved declaration identities, generic parameter categories, callable
families, primitive registrations, visibility facts, and explicit dependencies.

Resolve the metadata needed by
[angle parsing](SPEC.md#static-type-values-and-type-quotation) before committing
an expression's generic application. Typechecking a candidate parse is not the
selection mechanism. Resolve aliases and re-exports without inventing new
nominal, effect-operation, storage, or primitive identities.

Track module and exact opaque-definition scopes explicitly. A private source
can remain part of checking metadata without becoming accessible source syntax.
Failures here use name, visibility, declaration-context, or committed-syntax
diagnostics, rather than a later generic type mismatch.

### 2. Form Types and Check Sorts

Input: resolved type syntax, the static binder environment, and available evidence.

Output: well-formed type/constructor descriptions, or dependent formation
obligations with explicit prerequisites; see
[K-TYPE](SPEC.md#type-formation-and-binding).

Distinguish a type parameter from a static value parameter and a member-mode
parameter before checking its argument. Check arity, defaults, row tails,
nominal applications, and callable constituent types under the appropriate
sorts. Apply only the specified one-way adaptation to a token value parameter.

Equality work uses [K-EQ](SPEC.md#definitional-equality-and-recursive-types).
Memoizing pairs can help avoid repeatedly traversing nominally recursive types;
it does not make an unguarded transparent alias cycle valid. Required static
computations are evaluation requests, not arbitrary extensional comparisons of
type-producing programs.

### 3. Check Expressions in Both Directions

Input: an expression, local storage/path facts, and an optional expected type.

Output: a checked data type, normal-continuation facts, authority/provenance
information, and obligations from the expression's actual computation.
Use [K-EXPR](SPEC.md#bidirectional-expression-checking),
[K-SUB/K-RECV](SPEC.md#subtyping-reception-and-contract-compatibility), and
[K-JOIN](SPEC.md#structural-joins-and-normal-continuations).

Push an expected type into lambdas, constructors, empty collections, and branch
results where the rules permit. Synthesize from declarations, literals, and
elimination forms. Report an undetermined required argument as `E0344` rather
than selecting an arbitrary type.

Type-producing tails use the dedicated `TypeResult` checking context; different
selected type tokens need no common ordinary token-storage type. A stored token
still has an exact fixed `Type<T>`. Compatible callable branches can retain their
actual contract alternatives without an expected row; explicit closed contracts
continue to check every alternative.

Keep ordinary type compatibility separate from reception authority. An expected
writable type cannot create a writer. A `never` result supplies no normal value,
but the evaluation reaching it can still have effects, writes, or divergence.

### 4. Exchange Evidence with Static Evaluation

Input: required type/meta/const computations whose dependencies are ready.

Output: a complete static value or type, or the specified static failure;
see [K-PHASE](SPEC.md#phase-checking-and-static-evaluation).

Suspend a computation waiting on a required type or static argument and record
which facts can wake it. Do not fill a hole with `never`, use a diagnostic preview
as a type, or repeatedly evaluate an unchanged dependency cycle.

Rigid generic parameters are available symbolic inputs under K-TYPE-SYMBOLIC:
forward-reduce `WrapField<T>` to `.{ field: T }` without enumerating its calls.
Suspend only decisions needing an unknown shape or static value. A well-formed
symbolic interface expression differs from an unsolved metavariable or a
diagnostic preview. Type-producing result contexts also reach return and loop
transfer targets; ordinary token-storage contexts remain exact.

For a named generic definition, use
[K-GEN](SPEC.md#generic-evidence-and-definition-checking) to verify its ordinary
typing obligations under its declared domain. The specified finite token-match evidence
establishes why the `Numeric` example supports arithmetic. A complex arbitrary guard
does not become an inverse type solver; explicit constraints supply missing
evidence. Existing conditional mode/callback/static obligations have their own
specified instantiation boundary.

Static branch selection and branch-local equality evidence are separate.
[K-PAT](SPEC.md#pattern-evidence-and-gadt-branches) makes GADT equations available
throughout their arm without changing a rigid parameter's declaration identity.
Such evidence can justify a check in the arm and still be unavailable after it.

### 5. Solve Recursive Summaries and Authority Obligations

Input: typed operations, call dependencies, actual callable contracts, and the
provenance relationships established so far.

Output: grounded summaries and the remaining obligations for each definition or
admitted family instance; see
[K-CALL](SPEC.md#authority-calls-and-contract-operations) and
[K-FIX](SPEC.md#recursive-summaries-and-grounded-inference).

An SCC worklist is useful for recursive calls, higher-order dependencies, and
state/effect propagation. Positive facts can grow toward a fixed point. Claims
such as disjointness, absence of escape, absence of Div, or required authority use
need their own established evidence; a cycle of declarations is not evidence.

Carry correlations when joining alternatives. If both branches permute the same
two disjoint inputs, a pair of independent source unions loses a valid common
relation. Conversely, unknown array indices cannot establish disjointness.

Freeze the actual call-entry graph at the specified boundary before substituting
root-return selections. Later insertion does not rewrite that entry graph.
Check handlers, cleanup, retained environments, and task boundaries as actual
participants in the same source and authority accounting.

### 6. Normalize and Validate Source Contracts

Input: inferred contracts, completed dependent instances, and written annotations.

Output: accepted complete contracts, or specific missing/excess/incompatible
annotation diagnostics. Written effect/state/source annotations do not seed
operational facts that justify themselves; declared type/sort constraints and
formation premises remain valid assumptions.

Normalize the prescribed state implications and source identities before closed
callable matching. Check concrete parameter modes independently of effect/state
openness. Apply handling and lawful local discharge before deciding the outward
contract; removing an effect does not remove a state or environment dependency.

Validate phase eligibility and materialization after the relevant instantiation,
including nested constituents, opaque summaries, and captured environments.
Check `halt` and budget coverage independently of source spelling and compiler
resource limits. Preserve the distinct outcomes of compiler-budget exhaustion,
source-budget exhaustion, static panic, and an alias cycle.

### 7. Publish Interfaces and Explanations

Input: verified definitions and their complete semantic summaries.

Output: checking interfaces and dependency fingerprints, together with source
completion information and optional human-facing explanations.

Recommended interface fields, following
[K-IFACE](SPEC.md#semantic-interfaces-and-diagnostic-boundaries), are:

| Field group | Information retained |
| :--- | :--- |
| Identity and binding | Declaration/opaque identities, binder sorts, parameter correspondence, visibility boundary |
| Data and storage | Types, nominal instantiations, full member modes, fixed schemas, constituent relationships |
| Callable family | Admitted mode instances, verified constraints, result guarantees, actual open-row dependencies, retained callable alternatives |
| Sources | Root and contained origins, call-entry selections, store/return relations, output correlations |
| State and environments | Writes, independent retention, captures, named-source access, environment ownership |
| Effects and termination | Normalized effects including Div, verified operation footprints, handler-selection dependencies, budget-coverage obligations |
| Conditional obligations | Static/mode/callback conditions, prescribed phase/layout/key/result eligibility, prerequisites and verification boundary |
| Dependencies and explanations | Referenced semantic identities, proof dependencies, originating rules and source spans |

This is a semantic inventory, not a serialized wire format. Dependency tracking
can invalidate a consumer when a relevant guarantee or hidden source changes,
even if the exported surface signature has the same text.

## Surface Constructs, Core Rules, and Verification Cases

The table maps all language areas to an implementation entry point. It does not
replace the normative [Core Rule Coverage](SPEC.md#core-rule-coverage) table.
Multiple surface forms can share a core operation while retaining their distinct
evaluation order, authority, and diagnostic boundaries.

“Existing model” below means a related local Lean model, not a proof of lowering
from that Ril construct. “None” means there is no corresponding full typing model.
Fixture links point to independent specification cases, not executed Ril tests.

| Surface area | Core operation / rule family | Diagnostic focus | Specification cases | Existing model |
| :--- | :--- | :--- | :--- | :--- |
| Names, imports, modules, declaration bodies | Identity/scope resolution; K-CTX, K-TYPE | `E0201`–`E0209`, `E0902`, `E0909` | [Modules](SPEC.md#modules-and-compilation-units), [bodyless declarations](SPEC.md#named-function-declarations-and-contrast-matrix) | Source identities only |
| Literals, operators, numeric conversions, interpolation | Primitive contract checking; K-EXPR, K-SUB | `E0301`, `E0326`–`E0329`, lexical diagnostics | [Expressions](SPEC.md#expressions-and-operators) | None |
| Records, tuples, arrays, maps, sums, nominal/opaque types | Formation, equality, compatibility; K-TYPE, K-EQ, K-SUB | `E0301`, `E0302`, `E0306`, `E0313` | [Equality](SPEC.md#kernel-fixture-equality), [type forms](SPEC.md#types-and-memory-model) | Access schemas; no data-type equality |
| Open records, named row tails, spread and rest | Row evidence and closed structural formation; K-TYPE, K-GEN | `E0210`, `E0212`, `E0306`, `E0344` | [Rows](SPEC.md#kernel-fixture-rows) | None |
| Bindings, assignment, members and indexing | Reception, fixed storage, access and invalidation; K-RECV, K-ANON, K-CALL | `E0402`, `E0501`, `E0502`, `E0520`, `E0535` | [Fixed storage](SPEC.md#kernel-fixture-generalization), [bindings](SPEC.md#declarations-and-bindings) | Finite access/assignment models |
| Blocks, if/match, fallbacks and short-circuiting | Normal continuations and structural joins; K-EXPR, K-JOIN | `E0301`, `E0304`, `E0351`, control-transfer diagnostics | [Joins](SPEC.md#kernel-fixture-joins), [control flow](SPEC.md#control-flow-and-pattern-matching) | Nondeterministic branches, no full expression typing |
| Loops, recursion, return/last/next | Flow fixed points, control targets and Div; K-JOIN, K-FIX | `E0707`, `E0820` | [Control transfers](SPEC.md#control-transfers), [Div](SPEC.md#finite-evaluation-with-div) | Finite CFG provenance; no full loop typing |
| Value tests, patterns, guards and narrowing | Pattern evidence and invalidation; K-PAT, K-EXPR | `E0304`, `E0309`, `E0345`, `E0347` | [Pattern rules](SPEC.md#pattern-syntax-or-patterns-and-exhaustiveness), [narrowing](SPEC.md#flow-sensitive-type-narrowing) | None |
| GADT constructors and matches | Result-equation recovery, arm-local evidence; K-TYPE, K-PAT | `E0301`, `E0354` | [GADT branches](SPEC.md#kernel-fixture-gadt) | None |
| Explicit generics, defaults and type guards | Sort checking, instantiation and definition evidence; K-GEN, K-EQ | `E0306`, `E0316`, `E0317`, `E0320`, `E0340`, `E0344` | [Generics](SPEC.md#kernel-fixture-generics) | None |
| Anonymous functions, aliases and writable callable slots | Generalization, instantiation and fixed storage; K-ANON | `E0301`, `E0344`, `E0407`, `E0534` | [Generalization](SPEC.md#kernel-fixture-generalization) | Resolved finite calls only |
| Arguments, defaults, pipelines and trailing closures | Ordered evaluation, call entry and contract substitution; K-EXPR, K-CALL | `E0314`, `E0405`–`E0412`, `E0534` | [Calls](SPEC.md#kernel-fixture-calls), [defaults](SPEC.md#default-parameters-and-named-arguments) | Call preparation and entry/summary models |
| `via`, `infer`, lexical mode templates and mapped modes | Finite families and dependent reception; K-GEN, K-CALL | `E0412`, `E0527`, `E0528`, `E0550` | [Mode inference](SPEC.md#access-mode-inference-with-via-and-infer) | Access/provenance components only |
| Construction, handoff, clone and derive | History, graph authority and publication; K-RECV, K-CALL | `E0530`, `E0536`, `E0548`, `E0549` | [Handoffs](SPEC.md#verified-storage-handoffs), [derive](SPEC.md#functional-updates-via-derive) | Handoff, identity and Draft models |
| Captures, named state, returns and higher-order contracts | Source substitution, environment creation and matching; K-CALL, K-FIX | `E0510`, `E0529`, `E0534`, `E0545` | [Sources](SPEC.md#state-and-provenance-tracking), [calls](SPEC.md#kernel-fixture-calls) | Provenance and summary models; not full higher-order verification |
| Effects, handlers, parameterized handlers and resume | Resolved dispatch, residual obligations and affine authority; K-CALL, K-FIX | `E0612`, `E0614`, `E0621`, `E0622`, `E0540` | [Handlers](SPEC.md#effect-handlers), [resumption](SPEC.md#affine-resumption-and-delimited-early-abort) | Boundary/resumption models with explicit input premises |
| Scoped resources, cleanup, tasks, parallelism and channels | Lifetime, confinement and boundary eligibility; K-CALL, K-FIX | `E0541`, `E0601`–`E0606`, `E0616`–`E0619` | [Scoped bindings](SPEC.md#scoped-resource-bindings), [concurrency](SPEC.md#structured-concurrency-and-panic-containment) | Lifetime/boundary components; no full concurrency semantics |
| `halt`, Div and source/compiler budgets | Termination contract, coverage and phase evaluation; K-FIX, K-PHASE | `E0811`, `E0820`–`E0822` | [Phase](SPEC.md#kernel-fixture-phase), [budgets](SPEC.md#finite-evaluation-with-div) | Abstract reachability/halting limits; no budget evaluator; no full budget evaluator |
| Type tokens, type/meta functions, typeof and const arguments | Static formation, evaluation and materialization; K-TYPE, K-PHASE | `E0306`, `E0810`–`E0816`, `E0830`, `E0831` | [Phase](SPEC.md#kernel-fixture-phase), [static computation](SPEC.md#compile-time-computation-and-finiteness) | None |
| Reflection, coordinate keys, mapped types and layout | Static primitive contracts and dependent projections; K-TYPE, K-PHASE | `E0323`, `E0341`–`E0343`, `E0356`, `E0358` | [Introspection](SPEC.md#static-introspection), [layout](SPEC.md#compile-time-evaluation-and-layout-queries) | None |
| Foreign interfaces and registered primitives | Trusted/registered boundary contracts; K-TYPE, K-CALL, K-IFACE | `E0902`, `E0909`, boundary-specific authority errors | [External contracts](SPEC.md#external-interface-declarations), [built-ins](SPEC.md#built-in-foundational-operations) | Explicit foreign-conformance premise only |
| Fallible values, tests, initialization and main | Observation obligations, root contexts and interface checks; K-EXPR, K-IFACE | `E0720`, initialization/entry diagnostics | [Results](SPEC.md#mandatory-inspection-of-fallible-results), [entry](SPEC.md#program-entry-point) | None |

## Validation and Existing Proof Boundaries

For a documentation change, review the relevant accepted and rejected cases by
derivation, including their fixture context and required source completion.
Cross-check every new core rule against at least one surface use and a diagnostic
boundary. Check that illustrative elaboration preserves evaluation order and
does not insert authority, copies, allocation, or resource transfers.

The repository's [documentation checker](../scripts/USAGE.md#documentation-validation)
checks Markdown structure, local links, and EBNF consistency. It does not execute
Ril examples, prove the grammar unambiguous, or validate typing and effects.

The [formal runner](../scripts/USAGE.md#formal-verification) builds the existing
Lean project, runs its model fixtures, and audits project declarations. Its
[verification bundle](../formal/RilAccess/Verification.lean) explicitly does not
claim a refinement theorem for an unrestricted language combining every model.
The [finite call model](../formal/RilAccess/Call/Core.lean) leaves recursive
interfaces and general function values as separate proof obligations.

The [provenance analysis](../formal/RilAccess/Provenance/Analysis.lean) is a
flow-insensitive may-source analysis; successful analysis alone does not imply
progress. The [boundary model](../formal/RilAccess/Effects/Boundary.lean) consumes
resolved handler/callback contracts. Neither constitutes a full Ril frontend.
The coverage table identifies these boundaries instead of treating related
abstract models as proofs of source elaboration or complete type soundness.

## References and Deliberate Ril Differences

These primary references inform presentation and implementation techniques.
They are not imported language rules or conformance dependencies.

| Primary reference | Useful technique or presentation | Ril boundary |
| :--- | :--- | :--- |
| [Scala 2.13 specification: Types](https://www.scala-lang.org/files/archive/spec/2.13/03-types.html#relations-between-types) | Separate type equivalence, conformance, and compatibility; describe binders and type constructors explicitly | Ril does not acquire Scala's singleton/literal types, numeric weak conformance, or class hierarchy. Its reception and callable contracts have their own judgments |
| [Rust Reference: Subtyping and variance](https://doc.rust-lang.org/reference/subtyping.html) | State variance rules per type position and distinguish mutable contents from covariant results | Ril uses tracing GC, shared-object identity, its own access/provenance rules, and invariant collection schemas; Rust's lifetime subtyping and collection variance do not transfer |
| [Dunfield and Krishnaswami: Bidirectional Typing](https://arxiv.org/abs/1908.05839) | Separate synthesis from checking and make expected information flow explicit | This suggests organization; it does not supply Ril's inference completeness, anonymous generalization, mode-family, effect, or storage rules |
| [OCaml manual: Generalized algebraic datatypes](https://ocaml.org/manual/5.5/gadts-tutorial.html) | Explain constructor result equations and the local scope of match evidence | Ril requires recovery of constructor-local parameters and has no hidden existential payload parameters. Arm-local equality evidence does not change global rigid identities |
| [Leijen: Koka, Programming with Row-polymorphic Effect Types](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/paper-20.pdf) | Explain latent effects, local state encapsulation, divergence, and their interactions with polymorphism | Ril keeps effects separate from state/provenance, requires exact closed callable rows, and uses its own Div/budget rules; it does not import duplicate effect labels or Koka's termination analysis |

When borrowing an implementation idea, first identify the corresponding Ril
judgment and fixture. If the idea requires a different variance rule, a new
runtime representation, stronger proof search, or another authority mechanism,
it is a language change rather than an implementation detail of this guide.
