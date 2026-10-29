# Repository guidance

## Editing restrictions

Do not modify `README.md` or `AGENTS.md` unless the user explicitly requests it.

## Git workflow

Work directly on `main` and commit changes there. Do not create, switch to, or
use other branches unless the user explicitly requests them.

## Ril language semantics

[The Ril specification](doc/SPEC.md) is the canonical reference. Use its
definitions rather than importing meanings from Rust, C++, or other languages.

### Language boundaries

- Ril uses automatic memory management with **tracing garbage collection**.
  It provides no raw pointers, pointer arithmetic, or manual memory management.
  Scoped resource cleanup is separate from GC reclamation. See the
  [abstract machine](doc/SPEC.md#abstract-machine-and-memory-semantics).
- Permissions, provenance and alias tracking, state/capability contracts,
  effect checking, escape/exclusivity checks, and termination judgments are
  **compile-time analyses**. Authority modifiers are erased from runtime
  representations; do not introduce runtime permission objects, dynamic borrow
  checks, or runtime provenance tracking to enforce these static contracts.
  Preserve the contract metadata needed for checking across compilation
  interfaces. See [authority erasure](doc/SPEC.md#array-map-and-tuple-types) and
  [static provenance](doc/SPEC.md#complete-provenance-and-required-annotations).
- Static checking does not eliminate the runtime behavior of actual operations.
  GC, mutation, `clone`, `derive`, effect handlers, scoped cleanup, and
  `Div::budget` charging retain their specified execution behavior.

### Data, bindings, and authority

- **Value / reference types** describe semantics, not a chosen machine layout.
  Values copy; references share managed objects. `str` and `bytes` are value
  types; records, tuples, arrays, maps, sets, and sum instances are reference
  types.
  See [value types](doc/SPEC.md#value-types) and
  [reference types](doc/SPEC.md#reference-types).
- **`let` / `var`** control slot replacement; the access mode controls interior
  permissions. Plain `var` can replace deeply immutable data but cannot mutate
  its referenced contents. `let mut` permits interior writes but not rebinding;
  `var mut` permits both. Member permissions also constrain each access. See the
  [binding matrix](doc/SPEC.md#binding-permissions-and-storage-matrix).
- **Deep immutability** is required for plain `let`, plain `var`, ordinary
  parameters, and default members. Immutable reception cannot implicitly copy,
  freeze, or revoke an existing writer; surviving live/writable origins fail
  checking. See [deep immutability](doc/SPEC.md#deep-immutability).
- **`ref`** is read-only observation, which may remain live as another lawful
  writer changes the object. It does not imply an immutable snapshot or grant
  write authority. See [read-only references](doc/SPEC.md#read-only-reference-bindings).
- **`mut` / `^mut`** distinguish temporary writable parameter access from access
  that may retain a writable alias. `let ^mut` / `var ^mut` explicitly receive
  shared writable data. These modes do not grant missing authority or bypass
  exclusivity; `^mut` does not clone or transfer general ownership. See
  [parameter modes](doc/SPEC.md#parameter-modes-caller-obligations-and-defaults)
  and [retained sharing](doc/SPEC.md#retained-mutable-sharing).
- **Pinned handle** fixes the binding's target; it is not a physical-address
  guarantee or a constraint on GC relocation. See
  [pinned mutable handles](doc/SPEC.md#pinned-mutable-handles).
- **`new`** denotes a verified construction-root contract or an explicit handoff
  of unpublished construction authority. It is not an allocation operator,
  deep copy, or general move. Root freshness alone proves neither whole-graph
  isolation nor immutable-publication eligibility. See
  [return contracts](doc/SPEC.md#return-construction-permissions-and-sources)
  and [construction parameters](doc/SPEC.md#fresh-construction-parameters).

### Contracts and purity

- **Capabilities** such as `&mut`, `&^mut`, `&up`, and `&capture` describe checked
  mutation, retained sharing, external/captured access, and environment creation
  obligations. They are not address-taking operators or runtime capability
  objects. See [state tracking](doc/SPEC.md#state-and-capability-tracking) and
  [state groups](doc/SPEC.md#state-groups-and-captured-layers).
- **Pure** concerns effective outward effects and capabilities. Confined local
  mutation may discharge locally, so purity does not forbid all mutation. Empty
  effect/capability rows do not prove termination. See
  [local purity](doc/SPEC.md#local-mutation-purity-and-local-capability-discharge).
- **`halt`, `Finite`, `MayDiverge`, `never`** have distinct meanings. `halt`
  requires finite computation and outward purity but may still panic. `Finite`
  and `MayDiverge` are static judgments; the latter means finiteness is unproved,
  not that divergence is proved. `never` means no normal continuation, not
  necessarily infinite execution. See
  [termination contracts](doc/SPEC.md#termination-and-halt-contracts).
- **`Div`** is the budget-exhaustion effect, not a general divergence effect.
  `Div::budget` supplies a checked finite-evaluation boundary with runtime
  charging; merely handling exhaustion does not prove arbitrary calls finite.
  See [finite evaluation](doc/SPEC.md#finite-evaluation-with-div).

### Other overloaded terms

- **`clone` / `derive`** perform deep copying / functional update, not trait or
  macro derivation. `clone` isolates a new graph while preserving its internal
  aliases and cycles. `derive` preserves immutable inputs, confines a mutable
  draft, and publishes an immutable result; unaffected immutable regions may
  remain shared. See [copy semantics](doc/SPEC.md#deep-immutability) and
  [functional updates](doc/SPEC.md#functional-updates-via-derive).
- **`scoped`** registers deterministic cleanup on scope exit, including abrupt
  exits, in reverse registration order. It is a resource-lifetime mechanism,
  not manual GC heap deallocation. See
  [scoped resources](doc/SPEC.md#scoped-resource-bindings).
- **`Type<T>`, `<T>`, type functions, and reflection** belong to the static
  domain; `<T>` is a type-token value expression, not type annotation syntax.
  Tokens do not materialize at runtime. `typeof e` checks without evaluating
  `e`; eligible token-free meta results may become ordinary runtime constants.
  See [type tokens](doc/SPEC.md#static-type-values-and-type-quotation) and
  [static computation](doc/SPEC.md#pure-type-functions-and-type-return-privilege).
- **Type declarations** distinguish transparent aliases (`type A = T`), nominal
  wrappers (`type A(T)`), and representation-hiding opaque types
  (`opaque type A = T`). Naming an alias does not create nominal identity. See
  [nominal wrappers](doc/SPEC.md#nominal-type-wrappers) and
  [opaque types](doc/SPEC.md#type-declarations-and-opaque-types).
- **`where`** declares helper items in the specified declaration scope; it is
  not a generic predicate list. Signature `where` admits only local type
  declarations. See [where scopes](doc/SPEC.md#dual-tier-where-invariants).
- **`is`** tests values/tags and does not introduce bindings; it is not a
  general runtime type test. See [value tests](doc/SPEC.md#value-tests-with-is).
- **`Async`** is the effect alias `{Fiber, Concurrent}`, not an async/await
  function-coloring mechanism. `Fiber` covers cooperative suspension and leaf
  I/O; `Concurrent` covers structured task branching and joining. See
  [system effects](doc/SPEC.md#built-in-system-effects).

### Specification examples and executable source

Independent SPEC fixtures may abbreviate named callable annotations under
[document conventions](doc/SPEC.md#document-conventions). Do not copy those
abbreviations into complete source files: named definitions must spell the
prescribed contracts, while anonymous functions retain complete inferred
contracts without mandatory source annotation completion. Omission never
erases an actual obligation. See
[contract inference and completion](doc/SPEC.md#mandatory-contract-inference-and-completion).

