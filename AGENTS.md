# Repository guidance

## Editing restrictions

Do not modify `README.md` or `AGENTS.md` unless the user explicitly requests it.

## Git workflow

Work directly on `main` and commit changes there. Do not create, switch to, or
use other branches unless the user explicitly requests them.

## Ril distinctions

[SPEC](doc/SPEC.md) is canonical. Keep this guide focused on distinctions that affect interpretation or implementation.

Use `contract` for an interface's specified assumptions and guarantees. Name individual types, permissions, origins, effects, and annotations directly.

| Distinction | Ril meaning |
| --- | --- |
| [Checking / execution](doc/SPEC.md#complete-provenance-and-required-annotations) | Permissions, provenance, effects, and termination are static judgments; interfaces retain checking metadata. Authority modifiers are erased; mutation, copying, handlers, cleanup, and budget charging execute. |
| [Values / shared objects](doc/SPEC.md#types-and-memory-model) | `str` and `bytes` copy by value; records, tuples, collections, and sum instances share objects managed by tracing GC. |
| [Binding / access](doc/SPEC.md#binding-permissions-and-storage-matrix) | `let` / `var` govern slot replacement; access modes govern reachable data. Pinning fixes the binding's target object. Plain reception requires deep immutability; `ref` may observe a live writable origin. |
| [`mut` / `^mut`](doc/SPEC.md#parameter-modes-caller-obligations-and-defaults) | Parameter `mut` grants temporary write access; `^mut` permits retained writers. Local `let mut` receives exclusive writable access; `let ^mut` / `var ^mut` receive shared writable access. |
| [`new` / isolation](doc/SPEC.md#preserving-local-bindings) | Construction qualification comes from checked initial reception. Handoff preserves allocation identity and ends the source path and derived accesses; root privacy and graph separation are independent checks. |
| [`via` / `infer`](doc/SPEC.md#permission-inference-with-via-and-infer) | `via` binds permission parameters and supports dependent local reception; `infer` derives result permissions and provenance while the result data type stays explicit. |
| [Root / contained origins](doc/SPEC.md#return-construction-permissions-and-sources) | `ref(x)` / `^mut(x)` select root origins from the formal's call-entry graph; `&return{...}` records possible contained origins. Root writable return accounts for its retention; writes and extra retention have separate capability annotations. |
| [State / environment creation](doc/SPEC.md#state-and-capability-tracking) | `&mut` records parameter writes, `&^mut` independent retained sharing, and `&capture` surviving environment creation. Local discharge follows actual origins and escape. |
| [`&up` forms](doc/SPEC.md#state-groups-and-captured-layers) | Bare `&up` abstracts a callable environment. `&up{...}` and `&up(sub){...}` identify captured and module sources; their actual identities remain in metadata. |
| [Closed / open callable rows](doc/SPEC.md#callable-contract-matching) | Closed rows require exact normalized effects/capabilities. Effect/capability openness and permission polymorphism are independent. |
| [Inference / source annotations](doc/SPEC.md#mandatory-contract-inference-and-completion) | The compiler derives propagation and required annotations from starting permissions and constraints. Named definitions spell required annotations; anonymous ones may omit them. `via` / `infer` retain their specified details in metadata. |
| [Fixtures / complete source](doc/SPEC.md#document-conventions) | SPEC fixtures may display compiler-completed named signatures; complete source spells the required annotations. |
| [Purity / termination](doc/SPEC.md#termination-and-halt-contracts) | Purity permits confined local mutation; `halt` additionally requires finite computation. `Finite` / `MayDiverge` classify proved / unproved finiteness; `never` describes absence of normal continuation. Finite computation may panic. |
| [`Div` / finiteness](doc/SPEC.md#finite-evaluation-with-div) | `Div` denotes budget exhaustion. `Div::budget` bounds eligible protected computation; whole-expression finiteness also requires finite cleanup and recovery. |
| [`clone` / `derive`](doc/SPEC.md#functional-updates-via-derive) | `clone` isolates a copied graph; `derive` may share unaffected immutable regions after confined draft mutation. Both preserve internal aliases/cycles. |
| [Static types / ordinary data](doc/SPEC.md#static-type-values-and-type-quotation) | `Type<T>` is an exact static metatype; `<T>` is a static type token. `typeof e` checks without evaluating `e`. Eligible token-free meta results may become ordinary constants. |
| [Data type / member mode](doc/SPEC.md#universal-member-mode-projection) | `T.(K)` projects the constituent data type; `modeof T.(K)` queries the declared pair of slot replacement and access. |
| [`where` / generic constraints](doc/SPEC.md#dual-tier-where-invariants) | `where` declares helpers; generic predicates use signature constraints and pipeline guards. Signature helpers are types; block helpers may also be functions or effects. |
| [`is` / binding patterns](doc/SPEC.md#value-tests-with-is) | `is` tests existing values/tags; `match` and guarded bindings introduce payload names. Type patterns match static tokens. |
| [`sub` / executable root](doc/SPEC.md#modules-and-compilation-units) | Library files and inline `sub PascalCase` are `sub`s; the executable root is non-`sub`, unimportable, forbids top-level `pub`, and uses plain `fn main`. Inline `sub` is hermetic: `Super::` reaches enclosing non-mutable items, downward access requires `pub`, mutable static state is never `pub`, and `opaque type` transparency stays in its exact defining scope. |
