# Checking and instantiation contract

The compiler now indexes borrowed source nodes by HIR definition identity and
lowers source types, callable signatures, generic constraints, access binders,
and contract clauses into resolved templates. These templates are checking
inputs. They do not certify type correctness, authority, purity, termination,
static evaluation, or interface compatibility. The driver must not report a
successful full check from their construction alone.

## Required checking roots

Check every definition in every loaded compilation unit, including unused
definitions. Ordinary syntax, resolution, and type compatibility apply in all
branches. Static selection prunes invocation obligations and required authority
uses only after ordinary compatibility has been established.

For a closed type-set parameter, check every promised alternative. For open
type, value, mode, row, and callback parameters, check a symbolic template
under its declared bounds and retain every unresolved requirement. Required
concrete applications must determine all arguments, satisfy those requirements,
and validate their specialized contracts. Runtime reachability cannot excuse
an invalid definition or required instance.

Definition checking, call-site access proof, and code emission are distinct
work items. A finite source call graph does not imply a finite instance graph.
Neither one by itself proves finite runtime execution.

## Recursive instance policy

An instance key contains the defining declaration, normalized type and static
arguments, selected mode parameters, target, and semantic dependency revision.
Source node IDs and process addresses are not type or static-value identity.
Concrete instance reuse requires equality under SPEC's static equivalence.

Check recursive groups through finite equations over declaration-owned
templates. Each recursive edge records its symbolic substitution, source site,
and requirements. A cycle closes only with evidence that:

1. The complete template body has been checked under its symbolic bounds.
2. Every edge preserves the callee's argument sorts, kind arity, schema
   invariance, and declared constraints under substitution.
3. The specialized effect, authority, state/provenance, phase, inspection, and
   termination obligations follow from established premises or remain explicit
   caller requirements.
4. Reusing the summary preserves call-entry origins, retained-source relations,
   output correlations, and construction consumption; it does not freshen the
   group's access binders.

Seeing the same declaration twice establishes none of these facts. In
particular, a growing edge such as `grow<T>` to `grow<[]T>` cannot reuse a
concrete-instance success merely because its declaration matches. A finite
symbolic proof can cover that family only when the four obligations hold for
the substituted family. Growth through static computation or effect identity
retains the corresponding evaluation and contract dependencies.

Possible behavior propagates from actual source operations. Required authority
use must have grounded evidence, and common guarantees must hold on every
retained alternative. Recursion cannot justify its own writable use,
retention, construction eligibility, or termination. The solver must retain
these separate domains, rather than accepting an ungrounded cycle as a proof.
The [Lean model](../formal/RilAccess/Verification.lean) supplies oracles only
for the judgments it models.

Independent outside uses freshen the finite signature. Self and mutually
recursive edges forward the current group's binders. Transparent aliases
forward schema identity. A concrete storage instance retains its selected
schema across assignment: slot replacement cannot replace its access modes.

If symbolic closure or concrete expansion exceeds compiler resources, report
a build failure with the dependency/instantiation chain. Do not invent a
language diagnostic, accept unchecked work, or reinterpret the failure as
`MayDiverge`. Language-level static evaluation still has its separate `E0811`
budget behavior. An alias-normalization cycle uses `E0313`; an executing
recursive type function consumes evaluation steps instead.

Alias reduction exposes one outer type constructor at a time. An unguarded
cycle of alias heads is `E0313`, including growth confined to their arguments.
References behind a product, collection, sum, or distinct nominal/opaque
identity remain finite graph edges instead of causing eager recursive
expansion. A distinct identity alone establishes no physical representation;
layout and materialization queries retain their own obligations.

Before reference execution, every admitted family also needs a finite emission
plan. That plan must cover reachable indirect calls, defaults, handlers,
cleanup, initialization, and adapters. Shared code requires checked layout,
operation, tracing, effect-identity, ABI, and charging compatibility. Runtime
type computation, access-mode selection, or Ril-visible reflection cannot
substitute for static checking. The emission planner and its growing-family
proofs remain implementation work.

## Static roots and caches

Each static root uses its configured positive budget, including certified
finite computations. Nested calls and callbacks spend that root's budget.
Cache a complete root result or failure with its target, initial budget,
dependencies, and diagnostic origin. A warm cache must preserve the cold
evaluation's budget result and source attribution; isolated cached callees
cannot silently supply free charged work to another root.

Static arguments use canonical IEEE bits, preserving zero sign and normalizing
NaNs. Their graph equivalence preserves nominal/opaque and tag identity,
record labels, positional elements, and insertion-ordered map/set contents.
Eligible cyclic graphs use the greatest structural relation; sharing count
and allocation addresses do not distinguish arguments. This differs from
ordinary map-key equality, which ignores map/set insertion order.

## Completion boundary

Resolved templates preserve computation requests as source-expression IDs,
not fabricated type values. `typeof`, projections, mapped schemas, guards,
and type-function calls must be reduced or retain a required symbolic proof
before a concrete use. Optional syntax already identifies the canonical
prelude `Option`, independently of lexical shadowing.

A checked-program result may be constructed only after all required work
items and obligations have succeeded and contracts have converged and been
validated. Versioned interfaces retain the resulting identities, schemas,
call labels/defaults, phase, authority, provenance, effects, inspection, and
termination metadata. Source annotations and erased modifiers must never
replace those proofs. Constraint solving, CTFE, and interface publication are
not implemented by the template-lowering API.
