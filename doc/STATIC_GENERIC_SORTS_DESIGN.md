# Meta function static argument sorts: scalar implementation and extent design

Scalar `n: int` Meta function generics are implemented and verified in the v30
Windows MSVC x86_64 and Linux GNU x86_64 component snapshot. Symbolic array
extents, other Meta value sorts, static keys and higher kinds remain design
only/NI. No shared `ArgumentKey` or public binder-sort extension has been
registered for the proposed extent phase. Root owns those shared contracts
and the independent Result-flow integration.

## Current facilities and gaps

| Facility | Current implementation | Consequence |
| --- | --- | --- |
| `typing::bounds::StaticBinderId` | Canonical declaration name, generic index and private `StaticParameterSort::{Type, ConstInt}`. | Type keys retain their prior encoding; const IDs have a different namespace. |
| `BoundEnvironment` | Ordinary value **types**, Type/row facts, visible const roles, historical const IDs and ID-keyed `ConstIntSelection::{Rigid, Closed}`. | `values: Env` does not identify a generic constant. Visible-role tombstones preserve historical selections and prevent name-based recovery. |
| `effect_identity::StaticBinderSort` | Only `Type`. | Shared argument keys cannot currently represent a rigid const/key/constructor binder. |
| `ArgumentKey::Array` | Length is `Option<String>`; `is_closed()` checks only the element. | Symbolic const lengths need a typed, scoped key and closedness check, not a raw spelling embedded in a string. |
| `Ty::Array` | `Option<usize>` mixes known literal/backing length facts with fixed declarations. | Unknown `[n]T` cannot become ordinary dynamic `[]T`, nor may a backing count become a fixed-type proof. |
| Evaluated `Environment` | Lexical values/declaration IDs plus captured `TypeEnvironment`, including separate const IDs/selections. | Actual closed specialization retains genuine IDs without proving its universal definition from observed values. |
| `TypeEnvironment` | ID-keyed Type/row witnesses and const int selections; named Meta functions use role-aware `enter_named`. | Legacy data/type/effect float, aggregate, key and constructor normalization keeps its existing path. |
| `types::bind_type_arguments_captured` | Named Meta scalar admission dispatches the actual value through existing evaluation and sort checking, then records its real const ID. | Unknown universal consts are not replaced by these actual values. Function generic defaults remain forbidden by their existing diagnostic. |
| `types::value_argument`, `check_sort`, `const_value_expr` | Existing evaluation, sort validation and canonical value reification. | Reuse for actual closed specialization after universal proof; retain original budget roots. |
| Type-function typing | Has `Ty::Constructor(arity)` and kind checks. | A constructor's arity alone is not its semantic identity or a universal application `M<T>`. |
| Ordinary semantic checker | Has `Ty::StaticKey`, static-key argument/check records and constituent projection contracts. | Meta support must retain those membership/permission/Result contracts rather than duplicate them with plain strings. |

## Implemented first stage: scalar const `n: int`

```ril
meta fn size<n: int>() -> int { n }
meta fn forward<n: int>() -> int { size<n>() }
meta let VALUE = size<2>()
meta let NEGATIVE = size<-3>()
meta let FORWARDED = forward<9>()
```

The universal environment gives `n` ordinary unknown `int` under its genuine
const ID. Explicit arguments can select target-sized closed integers or a real
rigid caller const. Missing values reject with `E0344`, wrong sorts with
`E0323`; pointer32 range checking does not use the host pointer width. Mixed
Type/const parameters work without selecting a constant as a Type. Unsupported
symbolic arithmetic, unresolved same-declaration recursive const forwarding
and other Meta value sorts stay NI.

Root consumes `const_binding_views(scope)` as `{name, id, closed: Option<i128>}`.
Universal own binders have no closed scalar; selected specializations can have
one. `mask_const_values` changes only the visible role, and `has_visible_const`
avoids irrelevant scope copies. Local/formal bindings and block/pattern/loop
restoration cannot erase historical IDs or resurrect a shadowed const. The
ordinary Typer and actual evaluator apply the same lexical-role separation.

`const_argument_source` freezes closed arguments as canonical literal syntax
and rigid arguments as genuine internal ID syntax. Closed arguments do not
capture a scope; rigid ones retain the original scope. First-class generic
callable Source typing is still NI. The frozen v25 before probe in
`target/static-const-captured-name-before-v25*` observed that NI, not accepted
misbehavior; the potential deferred raw-name drift is covered by pure tests.

Any const-dependent Type syntax, including `[n]T`, is refused before complete
source/result-context normalization. An actual closed `n` does not bypass this
stage boundary. Signature checks read the callee's actual captured lexical
environment, not a same-spelled caller const. The scalar path supplies no
Result inspection, branch truth, freshness, escape or permission proof.

The v30 library includes eight pure const tests; `static_const_int` passes six
Source groups including both static layouts and positive Core lowering. Its
single native fixture actually checks seven values `2, -3, 9, 7, 6, 2, 4` on
both platforms. Root's const Result-flow fixture is also executed on both hosts
and computes 21 after block/pattern/loop shadows. Its four Source groups include
producer custody and incremental comparisons. The unknown universal-branch
regression permits NI or `E0720`; its Rust pass is only nonauthorization
evidence, not a completed negative language case if NI.

The component logs
`target/const-int-and-dependent-bound-full-source-windows-v30.log` and
`target/const-int-and-dependent-bound-full-source-linux-v30.log` each pass 679
Rust tests across 25 targets (484 library, 195 Source), with one explicit ignore.
Compiler all-target Clippy passes with `-D warnings` in
`target/const-int-and-dependent-bound-clippy-{windows,linux}-v30.log`.
The reports
`target/const-int-and-dependent-bound-native-windows-v30-report.json` and
`target/const-int-and-dependent-bound-native-linux-v30-report.json` each record
17 passing executables, 22 Rust tests, 49 distinct positive sources and 53 entry
jobs, with all 19 CLI/runtime/test-executable hashes unchanged. The v31
workspace format check passes after formatting-only edits; no v31 semantic
rebuild or native run is claimed. These are component results, not full corpus
or compiler completion.

## Next proposed stage: complete `[n]T` extents

The actual const binder syntax is lowercase `n: int`; `[N]T` in architectural
discussion denotes the same kind of symbolic extent, not a PascalCase Type
parameter. Build on scalar literal/closed selection and direct rigid caller
forwarding, adding genuine fixed source dimensions. Broader value
sorts and unsupported symbolic arithmetic remain NI. Unknown ordinary runtime
arguments retain `E0814`; an unsupported symbolic meta expression must not be
misclassified as a known runtime value merely because its evaluator is missing.

The first scalar example above is implemented. The proposed dependent program
below remains NI today:

```ril
meta fn same<T, n: int>(values: [n]T) -> [n]T { values }
meta let PAIR: [2]int = same<int, 2>([7, 9])
```

After the base works, a complete stored `[2]int` source may infer `n = 2`.
A dynamic `[]int` currently holding two items cannot. A fresh literal may receive
an already determined `[2]T` construction context; this first step does not
guess `n` from its backing or uncontextualized cardinality.

### Identity, value and extent representations

The scalar implementation already distinguishes real Type/const IDs, rigid
caller values and target-sized closed selections. Preserve those identities
when adding extent terms; keep Type-only `type_binders` and closed Type
witnesses Type-only. A const value is not a `SourceTypeWitness`.

Array typing needs a real extent representation before a universal signature
`[n]T` can be accepted. The proposed private model distinguishes:

- dynamic declared extent;
- fixed declared extent, whose term is a closed integer or genuine const ID;
- observed value cardinality, usable for a pure `len` value fact but never as a
  fixed declaration or generic argument witness.

Fresh construction receiving may establish a fixed extent only after its actual
syntax/value and the written declared extent are checked. Stored values do not
take that path. Ordinary compatibility, generic selection, return checking and
closed-source construction must distinguish these cases. Keeping symbolic fixed
length as `None` without mandatory separate proof would erase the very condition
this feature needs to preserve.

The initial symbolic integer term algebra can be only `Closed` and `Binder`.
Non-negativity/range of a fixed dimension remains a well-formedness obligation
until selection; `size<-1>()` is already a legitimate scalar specialization.
After extent support exists, using a known negative value as a dimension must
reject with `E0815`; const-dependent dimensions currently remain NI instead.
No host `usize` determines a static
int's range. `[n]T` remains an open source pattern while `n` or `T` is open and
must not be wrapped in a closed source witness.

### Application and capture flow

1. Classify each generic declaration once into Type, const value, static key or
   constructor kind. Register genuine IDs and mask captured same-spelled names.
2. Normalize supplied static arguments according to that declaration's sort.
   Explicit selections retain priority and are checked against the declared
   value sort; `str` supplied for `n: int` is `E0323`.
3. Infer a missing direct const extent only from a full declared fixed source
   expression or a full written result context. Rigid caller extents forward
   their registered ID. Repeated occurrences must agree.
4. Complete Type inference, bound dependencies and shared row equations with
   the selected const terms. Complete-source root checking still validates
   dimensions, modes and qualifications.
5. Actual preparation evaluates each explicit closed argument once in its
   proper caller/default environment, stores the ID-keyed witness, and enters
   the existing Prepared invocation. Its captured environment retains those
   bindings independently of visible-name shadows.

Extend the existing named-Meta role-aware registration rather than changing
legacy sort paths by name. Captured bindings stay rigid; unresolved
same-declaration recursive calls need distinct activation obligations. Continue
the implemented visible-role masking while frozen return/source contexts retain
the original ID. Ordinary same-spelled scalar facts cannot impersonate it.

## Root-owned contracts needed for the extent step

Extent/key/kind changes below are proposed only. Reuse the scalar contracts
already registered; no extra actual-payload vector is required:

| Root/shared surface | Required contract |
| --- | --- |
| Shared static binder sort and declaration metadata | The private Type/ConstInt separation is implemented. Shared keys need their own genuine const-sort support before symbolic extents are admitted; later keys/kinds remain distinct. |
| Type/argument key dimensions | Replace the unscoped length string with a structured closed-or-binder term; `is_closed` includes that term. Type and value keys cannot unify by spelling. |
| Private static `Ty` array extent | Root Result-flow and ordinary Typer agree on dynamic, fixed/symbolic and observed cardinality. Finite shape length queries do not upgrade this extent. |
| `BoundEnvironment` value bindings | Reuse the implemented ID-keyed const selections and lexical masks. Full result contexts already freeze this store. |
| Typed explicit static argument | Preserve implemented sort-directed scalar selection. Infer extents only from complete `actual_schemas` or complete written result source, without an actual-backing vector. |
| Named scope preparation | Reuse the existing solved environment/real owner, including const bindings, for formal contexts and invocation. `ExpectedResult` keeps ordinary and complete-source hints distinct. |
| Root universal environment seeding | Preserve the implemented unknown universal int vs selected closed scalar distinction; ordinary actual parameter shapes cannot replace it. |
| Root symbolic arrays and transfer | Preserve original producer/alias/permission roots under the full symbolic extent. Initial `same` returns its input; unknown finite indexing/iteration proofs may remain NI. |
| Actual evaluated environment | Reuse the implemented const store and `value_argument`/`check_sort` path. Before dependent closure signatures, reconstruct the genuine captured type/const environment as well as ordinary values. |

For scalar data expressions, a symbolic const has ordinary type `int`, but its
static role/ID must remain available to static argument and extent resolution.
It is not an `IntegerConstant`. Root can keep unknown scalar truth as unknown;
`n == 2` cannot be assumed for an unused universal definition merely because the
only observed call supplies 2. A Result created and discarded on another branch
must still reject.

Required first tests include explicit and fixed-schema-inferred `n`, caller
const forwarding with same-spelled distinct binders, complete nested empty
dimensions, dynamic-array refusal despite matching count, inconsistent repeated
dimensions, local/formal shadowing, negative and target32 overflow, and a generic
`[n]T` definition that illegally returns `[]`. Type/context evidence must never
turn that empty implementation into a universal fixed-size proof.

## Following steps: static key `K` and constructor `M`

Static keys need their own value witness, membership domain and symbolic
projection. Infer `K` from an admitted static literal/value or a real caller key
ID, never from ordinary `Ty::String`. `key: K` and `T.(K)` must share that ID;
`[]K` stays a type error. Membership, dynamic availability, sum/GADT projection,
original producer identity and path permissions reuse the ordinary checker's
contracts (`E0323`, `E0814`, `E0337`). Meta computed projection needs a separate
complete transfer path; it is not enabled by merely relaxing Type admission.

Higher-kind support starts with explicit unapplied named constructor arguments,
their canonical declaration/captured environment and checked arity. Universal
`M<T>` needs a symbolic constructor application, not `Ty::Unknown` or a closed
ordinary data witness. Do not infer a unique constructor from an erased expanded
structural result. Constructor applications retain type-function budget and
termination obligations; kind arity alone proves neither termination nor a
fresh independent object graph.

Each future step requires its own atomic contract review, pure tests, pointer32/64
Source/Core gates, independent Result/capability checks, incremental comparisons
and actual Windows/Linux native execution. This design does not claim those
sorts or symbolic extents are implemented by the scalar v30 checkpoint. Do not
modify public `ArgumentKey` alongside another owner's shared-contract batch.
