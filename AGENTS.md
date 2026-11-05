# Repository guidance

## Editing restrictions

Do not modify `README.md` or `AGENTS.md` unless the user explicitly requests it.

## Git workflow

Work directly on `main` and commit changes there. Do not create, switch to, or
use other branches unless the user explicitly requests them.

## Ril distinctions

[SPEC](doc/SPEC.md) is canonical. Keep this guide focused on distinctions that are easily confused and affect interpretation or implementation. The table summarizes language rules and introduces no additional conformance requirements.

| Distinction | Ril meaning |
| --- | --- |
| [Checking / execution](doc/SPEC.md#complete-provenance-and-required-annotations) | Access modes, provenance, effects, and termination are static judgments; interfaces retain checking metadata. Authority modifiers are erased; mutation, copying, handlers, cleanup, and budget charging execute. |
| [Values / shared objects](doc/SPEC.md#types-and-memory-model) | `str` and `bytes` copy by value; records, tuples, collections, and sum instances have object identity and may be aliased. Their objects are managed by tracing GC; shared-object status grants no shared write authority. |
| [Binding / access](doc/SPEC.md#binding-modes-and-storage-matrix) | `let` / `var` govern slot replacement. Plain bindings hold deeply immutable snapshots. `ref` may observe a live writable origin. Pinning fixes the target object even if its storage moves. |
| [`mut` / `^mut`](doc/SPEC.md#parameter-modes-caller-obligations-and-defaults) | Parameter `mut` grants temporary write access; `^mut` permits retained writers. Local `let mut` uses exclusive writable reception; `let ^mut` / `var ^mut` use shared writable reception. Actual origins and accesses determine exclusivity; `mut` alone does not prove unique ownership. |
| [Authority / reachable use](doc/SPEC.md#reachable-authority-use) | `var` requires reachable slot replacement; `mut` requires writable use; shared local bindings require shared reception and writable use. A `^mut` parameter requires retention beyond temporary call authority; writing alone is insufficient. Declared member schemas have no independent use requirement. |
| [`new` / isolation](doc/SPEC.md#construction-qualified-locals-and-mode-preserving-reception) | Construction qualification comes from checked initial reception. Handoff preserves allocation identity and ends the source path and derived accesses; root privacy and graph separation are independent checks. |
| [`via` / `infer`](doc/SPEC.md#access-mode-inference-with-via-and-infer) | `via` binds access-mode parameters and supports dependent local reception; `infer` derives result access modes and provenance while the result data type stays explicit. |
| [Root / contained origins](doc/SPEC.md#return-construction-access-modes-and-sources) | `ref(x)` / `^mut(x)` select root origins from the formal's call-entry graph; `&return{...}` records possible contained origins. Root writable return accounts for its retention; writes and extra retention have separate state/provenance annotations. |
| [State / environment creation](doc/SPEC.md#state-and-provenance-tracking) | `&mut` records parameter writes, `&^mut` independent retained sharing, and `&capture` surviving environment creation. Local discharge follows actual origins and escape. |
| [`&up` forms](doc/SPEC.md#state-groups-and-captured-layers) | In callable types, bare `&up` abstracts an environment. `&up{...}` and `&up(sub){...}` identify concrete captured and module sources; their actual identities remain in metadata. Named definitions spell their required concrete source obligations. |
| [Closed / open callable rows](doc/SPEC.md#callable-contract-matching) | Closed rows require exact normalized effects and state/provenance obligations. Effect and state/provenance openness and access-mode polymorphism are independent. |
| [Inference / source annotations](doc/SPEC.md#mandatory-contract-inference-and-completion) | The compiler derives propagation and required annotations from starting access modes and constraints. Named definitions spell required annotations; anonymous ones may omit them. `via` / `infer` retain their specified details in metadata. |
| [Fixtures / complete source](doc/SPEC.md#document-conventions) | SPEC fixtures may display compiler-completed named signatures; complete source spells the required annotations. |
| [Purity / termination](doc/SPEC.md#termination-and-halt-contracts) | Purity requires empty outward effect and state/provenance obligations after handling and local discharge; confined mutation remains allowed. `halt` additionally requires finite computation. `Finite` / `MayDiverge` classify proved / unproved finiteness; `never` describes absence of normal continuation. Termination is inferred checking metadata, not a callable type modifier. Finite computation may panic. |
| [`Div` / finiteness](doc/SPEC.md#finite-evaluation-with-div) | `Div` denotes budget exhaustion. `Div::budget` bounds eligible protected computation by charging abstract evaluation events, without promising a wall-clock bound. Whole-expression finiteness also requires finite cleanup and recovery. |
| [`clone`](doc/SPEC.md#deep-immutability) / [`derive`](doc/SPEC.md#functional-updates-via-derive) | `clone` yields isolated `new T` strictly for ordinary shared objects (`T \|> SharedObject`); value types copy by value and reject `clone` (`E0401`). Reception determines whether the copy is writable. `derive` forwards recipe effects, state capture, and termination obligations, publishing an immutable snapshot with updates scoped to selected paths. |
| [Built-ins / signature parity](doc/SPEC.md#built-in-foundational-operations) | Built-ins (`len`, `inner`, `clone`, `derive`) declare exact Ril surface signatures using access templates (`via`/`infer`) and pure type guards (`SharedObject`, `LenTarget`, `Tuple`) without ad-hoc overloading (`E0203`). Monomorphization lowers them to specialized instructions with zero RTTI. |
| [Phase barrier / `<T>`](doc/SPEC.md#pure-type-functions-and-result-restrictions) | Type tokens `<T>` and static pattern matching belong strictly to compile-time `type` functions and `meta` evaluation. Runtime `fn` cannot materialize `<T>` as a value (`E0816`), ensuring complete type erasure and zero runtime reflection overhead. |
| [Static types / ordinary data](doc/SPEC.md#static-type-values-and-type-quotation) | `Type<T>` is an exact static metatype; `<T>` is a static type token. `typeof e` checks without evaluating `e`. Eligible token-free meta results may become ordinary constants. |
| [Data type / member mode](doc/SPEC.md#universal-member-mode-projection) | `T.(K)` projects the constituent data type; `modeof T.(K)` queries the declared pair of slot replacement and access. |
| [`where` / generic constraints](doc/SPEC.md#dual-tier-where-invariants) | `where` declares helpers; generic predicates use signature constraints and pipeline guards. Signature helpers are types; block helpers may also be functions or effects. |
| [`is` / binding patterns](doc/SPEC.md#value-tests-with-is) | `is` tests existing values/tags; `match` and guarded bindings introduce payload names. Type patterns match static tokens. |
| [`sub` / executable root](doc/SPEC.md#modules-and-compilation-units) | Library files and inline `sub PascalCase` are `sub`s; the executable root is non-`sub`, unimportable, forbids top-level `pub`, and requires a non-public ordinary `fn main`. `halt` is allowed on `main` under its usual checks. Inline `sub` is hermetic: `Super::` reaches enclosing non-mutable items, downward access requires `pub`, mutable static state is never `pub`, and `opaque type` transparency stays in its exact defining scope. |
