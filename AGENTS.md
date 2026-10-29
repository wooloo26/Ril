# Repository guidance

## Editing restrictions

Do not modify `README.md` or `AGENTS.md` unless the user explicitly requests it.

## Git workflow

Work directly on `main` and commit changes there. Do not create, switch to, or
use other branches unless the user explicitly requests them.

## Ril language semantics

[The SPEC](doc/SPEC.md) is canonical; use Ril definitions rather than other languages' conventions.

| Boundary | Rule |
| --- | --- |
| Memory | Tracing GC; no raw pointers, pointer arithmetic, or manual memory management. Resource cleanup is separate from GC. |
| Static checks | Permissions, provenance/aliasing, capabilities/effects, escape/exclusivity, and termination are compile-time judgments. Erase authority modifiers; preserve checking metadata across interfaces. No runtime permission objects, dynamic borrow checks, or runtime provenance tracking. |
| Permission workflow | Developers specify a computation's starting intent and constraints; the compiler derives permission/provenance propagation, result contracts, and required annotations. Do not require developers to mentally track every intermediate permission state. If inferred contracts do not meet requirements, revise the starting constraints or refactor through verified abstractions that preserve complete provenance and safety checks. |
| Runtime behavior | GC, mutation, copying, functional updates, handlers, cleanup, and `Div::budget` charging still execute as specified. |

### Terminology quick reference

| Term | Ril meaning |
| --- | --- |
| [Value / reference types](doc/SPEC.md#types-and-memory-model) | Values copy, including `str` and `bytes`; records, tuples, arrays, maps, sets, and sum instances share managed objects. |
| [`let` / `var`](doc/SPEC.md#binding-permissions-and-storage-matrix) | Control rebinding. Plain bindings receive deeply immutable data; `let mut` allows interior writes, `var mut` also rebinding. Member permissions still apply. |
| [`ref`](doc/SPEC.md#read-only-reference-bindings) | Read-only, possibly live observation, not a snapshot. Immutable reception cannot freeze surviving writers. |
| [`mut` / `^mut`](doc/SPEC.md#parameter-modes-caller-obligations-and-defaults) | Temporary parameter write access / access allowing retained writers. `let ^mut` and `var ^mut` receive shared writable data; no mode grants missing authority. |
| [Pinned handle](doc/SPEC.md#pinned-mutable-handles) | Fixed binding target, not a physical-address or GC-relocation guarantee. |
| [`new`](doc/SPEC.md#return-construction-permissions-and-sources) | Construction contract or handoff, not allocation, copying, or general move. Root freshness does not prove graph isolation or publication eligibility. |
| [Capabilities](doc/SPEC.md#state-groups-and-captured-layers) | `&mut`, `&^mut`, `&up`, `&capture`: mutation, retained sharing, external/captured access, and environment-creation contracts. |
| [Pure / `halt`](doc/SPEC.md#termination-and-halt-contracts) | Confined local mutation is allowed. Empty effects do not prove termination; `halt` requires finite computation and outward purity, but may panic. |
| [`Finite` / `MayDiverge` / `never`](doc/SPEC.md#termination-and-halt-contracts) | Proven finite / finiteness unproved / no normal continuation. Unproved finiteness is not proved divergence. |
| [`Div`](doc/SPEC.md#finite-evaluation-with-div) | Budget exhaustion, not general divergence. Handling exhaustion alone does not certify arbitrary calls as finite. |
| [`clone` / `derive`](doc/SPEC.md#functional-updates-via-derive) | Isolated deep copy preserving internal aliases/cycles / immutable functional update that may share unchanged regions; no trait derivation. |
| [`scoped`](doc/SPEC.md#scoped-resource-bindings) | Reverse-order scope-exit cleanup, including abrupt exits; not GC heap deallocation. |
| [Type tokens / reflection](doc/SPEC.md#static-type-values-and-type-quotation) | `Type<T>` and `<T>` are static metatypes/tokens, never runtime objects. `typeof e` does not evaluate `e`; eligible token-free meta results may become runtime constants. |
| [Type declarations](doc/SPEC.md#type-declarations-and-opaque-types) | `type A = T`: transparent alias; `type A(T)`: nominal wrapper; `opaque type A = T`: hidden representation. |
| [`where`](doc/SPEC.md#dual-tier-where-invariants) | Scoped helper declarations, not generic predicates; signature `where` permits only type declarations. |
| [`is`](doc/SPEC.md#value-tests-with-is) | Value/tag test without new bindings, not a general runtime type test. |
| [`Async`](doc/SPEC.md#built-in-system-effects) | Effect alias `{Fiber, Concurrent}`: suspension/leaf I/O plus structured task branching/joining; no async/await function coloring. |

SPEC fixtures may abbreviate named contracts; complete source must spell required
named annotations. Anonymous functions retain complete inferred contracts without
mandatory annotation completion. Omission never erases obligations. See
[contract completion](doc/SPEC.md#mandatory-contract-inference-and-completion).
