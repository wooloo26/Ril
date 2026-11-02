# Repository guidance

## Editing restrictions

Do not modify `README.md` or `AGENTS.md` unless the user explicitly requests it.

## Git workflow

Work directly on `main` and commit changes there. Do not create, switch to, or
use other branches unless the user explicitly requests them.

## Ril language semantics

[The SPEC](doc/SPEC.md) is canonical. Use its current definitions and contracts.

| Boundary | Rule |
| --- | --- |
| [Memory](doc/SPEC.md#abstract-machine-and-memory-semantics) | All references are managed; tracing GC reclaims memory. Resource cleanup follows its own scoped contracts. |
| [Static checks](doc/SPEC.md#complete-provenance-and-required-annotations) | Permissions, provenance/aliasing, capabilities/effects, escape/exclusivity, and termination are compile-time judgments. Authority modifiers are erased; interfaces preserve complete checking metadata. |
| [Permission workflow](doc/SPEC.md#mandatory-contract-inference-and-completion) | Developers specify starting intent and constraints; the compiler derives propagation, result contracts, and required annotations with source explanations. Revise starting constraints or use verified abstractions when inferred contracts need to change. |
| [Runtime behavior](doc/SPEC.md#abstract-machine-and-memory-semantics) | GC, mutation, copying, functional updates, handlers, cleanup, and `Div::budget` charging execute under their specified contracts. |

### Terminology quick reference

| Term | Ril meaning |
| --- | --- |
| [Value / reference types](doc/SPEC.md#types-and-memory-model) | Values copy, including `str` and `bytes`; records, tuples, arrays, maps, sets, and sum instances share managed objects. |
| [`let` / `var`](doc/SPEC.md#binding-permissions-and-storage-matrix) | Fixed / replaceable bindings, independent of interior access. Plain receivers require deeply immutable data; writable receivers also follow member permissions. |
| [`ref`](doc/SPEC.md#read-only-reference-bindings) | Read-only observation of an established object; writable origins remain live. Persistent handles require eligible immutable or pinned live origins; parameters use call-time observation. |
| [`mut` / `^mut`](doc/SPEC.md#parameter-modes-caller-obligations-and-defaults) | Parameter write access ending at return / access permitting retained writers. `let mut` receives exclusive writable authority; `let ^mut` and `var ^mut` receive shared writable authority. Every use follows source and alias checks. |
| [Pinned handle](doc/SPEC.md#pinned-mutable-handles) | A fixed binding target providing a stable object root for persistent observation. |
| [`auto`](doc/SPEC.md#permission-inference-with-auto) | Static permission templates: input/member access parameters, dependent `let auto` reception, and inferred `-> auto` results. Selected instances use concrete contracts. |
| [`MemberMode` / `modeof`](doc/SPEC.md#universal-member-mode-projection) | Member modes pair slot replacement with access. `modeof` queries both components; `auto` varies access while `var` is explicit. |
| [`new`](doc/SPEC.md#return-construction-permissions-and-sources) | Construction result/input contract or qualified handoff, preserving object identity and root write authority. Consuming reception checks the complete graph. |
| [Construction qualification](doc/SPEC.md#preserving-local-bindings) | An affine path established by checked initial reception. Handoff ends the source and derived accesses; root privacy and graph eligibility are checked separately. |
| [Capabilities](doc/SPEC.md#state-and-capability-tracking) | `&mut` tracks parameter writes, `&^mut` independent retained sharing, and `&capture` surviving environment creation, after lawful local discharge. |
| [State sources](doc/SPEC.md#state-groups-and-captured-layers) | `&up(sub){...}` names module access; `&up{...}` / `&up(owner){...}` name captured layers. Bare `&up` abstracts a callable type's environment while metadata preserves actual sources. |
| [Return dependencies](doc/SPEC.md#return-construction-permissions-and-sources) | `ref(x)` / `^mut(x)` identify root origins in a formal's call-entry graph. `&return{...}` describes contained dependencies; invocation capabilities are checked separately. |
| [Contract completion](doc/SPEC.md#mandatory-contract-inference-and-completion) | Every function has a complete inferred contract. Named definitions spell prescribed concrete annotations with the specified `auto` exemptions; anonymous source annotations are optional constraints. |
| [Pure / `halt`](doc/SPEC.md#termination-and-halt-contracts) | Purity permits confined local mutation. `halt` requires finite computation and empty outward effect/capability rows after handling and local discharge; panic is a permitted finite outcome. |
| [`Finite` / `MayDiverge` / `never`](doc/SPEC.md#termination-and-halt-contracts) | Proven finite invocation / finiteness unproved / absence of normal continuation. |
| [`Div`](doc/SPEC.md#finite-evaluation-with-div) | Budget-exhaustion effect. `Div::budget` bounds eligible run-time computation; whole-expression finiteness also requires finite cleanup and recovery. |
| [`clone` / `derive`](doc/SPEC.md#functional-updates-via-derive) | Isolated deep copy preserving internal aliases/cycles / immutable functional update through a confined draft, with sharing of unaffected regions permitted. |
| [`scoped`](doc/SPEC.md#scoped-resource-bindings) | Scope-exit resource cleanup in reverse registration order, including abrupt exits, under cleanup eligibility and failure rules. |
| [Type tokens / reflection](doc/SPEC.md#static-type-values-and-type-quotation) | `Type<T>` is an exact static metatype; `<T>` quotes its target. `typeof e` checks without evaluating `e`. Eligible token-free meta results may become run-time constants. |
| [Type declarations](doc/SPEC.md#type-declarations-and-opaque-types) | `type A = T`: transparent alias; `type A(T)`: nominal wrapper; `opaque type A = T`: hidden representation. |
| [`where`](doc/SPEC.md#dual-tier-where-invariants) | Scoped helper declarations. Signature `where` permits types; block `where` permits types, functions, and effects. |
| [`is`](doc/SPEC.md#value-tests-with-is) | Nonbinding value/tag test with expected-value expressions and flow-sensitive refinement. |
| [`Async`](doc/SPEC.md#built-in-system-effects) | Effect alias `{Fiber, Concurrent}`: suspension/leaf I/O plus structured task branching and joining. |

SPEC fixtures may abbreviate compiler-completed named contracts. Complete source
follows named annotation requirements and the specified `auto` exemptions.
All functions retain complete inferred contracts. See
[contract completion](doc/SPEC.md#mandatory-contract-inference-and-completion).
