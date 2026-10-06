# 16. Standard Prelude

This chapter defines all built-in types, constructors, and primitive functions provided by the Ril standard prelude, which are implicitly available in every translation unit without explicit import.

---

## 1. Prelude Types and Constructors

The prelude provides these runtime types and checked static categories:

| Category | Names | Rule |
| --- | --- | --- |
| Scalars | bool, (), never, i8..i64, u8..u64, int=i32, bigint, f32, f64, str, bytes | Existing numeric and storage semantics |
| Tagged families | Option<T> (Some/None), Result<T,E> (Ok/Err) | Finite runtime constructor values; static container/term lifting is checked separately |
| Collections | []T, Map<K,V>, Set<T> | Existing GC and handle permissions |
| Frozen modality | Immut<T> | Legal-domain deep freezing; reference container marker retained |
| Static categories | Type, Record, Row, [halt] type(...) -> R | No runtime layout or Type:Type |

Eq, Refl, Level, Type<u>, rewrite, and accessibility proofs are not core prelude facilities. Erased static index constructor equations and lexical existential witnesses remain available.

---

## 2. Primitive Prelude Functions

The standard prelude root namespace exposes ONLY universally applicable, meta-language operational primitives.

Container-specific mutation and collection manipulation functions (such as `push`, `pop`, `extend`, and `clear` for arrays `[]T`) MUST NOT reside in the standard prelude root namespace. Instead, they are defined within their respective standard library modules (e.g., `ril/array`) and invoked via type-qualified pipeline calls (e.g., `arr !> Array::push(item)`) or block-scoped local imports (`use ril/array::{push, pop}`).

The root runtime prelude provides the following core operational primitives. The fn signatures describe runtime interfaces; sealed primitives have checked halt-admissible operations only on their validated stable domains. This is not an implicit promotion of an ordinary user fn. Static operations have separate Types/Meta interfaces and do not call these runtime functions.

### 2.1 Collection Inspection

```ril
fn len(value: T) -> int
```
- Accepts `str`, `bytes`, arrays (`[]T`), `Map<K, V>`, and `Set<T>`.
- Returns the count of Unicode scalars for `str`, bytes for `bytes`, elements for arrays, and key-value entries for maps and sets.
- Maximum runtime collection capacity is $2^{31} - 1$ ($2147483647$); ordinary operations exceeding this limit trigger runtime panic. Halt operations must establish capacity or use a safe Result interface. len is halt-admissible on immutable scalar snapshots or certified stable collection inputs; a live mutable alias is not a stable input merely because its handle is read-only.

### 2.2 Memory Views and Functional Updates

```ril
fn clone<T>(value: T) -> T
fn clone_immut<T>(value: T) -> Immut<T>
fn move<T>(value: T) -> T
fn produce<T>(base: T, recipe: fn(mut T) -> () &mut) -> T
```

1. `clone(value)`: Constructs a detached, independent deep copy of the object graph, returning a duplicate of type `T` that retains mutability permissions on mutable fields. Scoped resource handles are statically prohibited.
2. `clone_immut(value)`: Constructs an isolated, permanently read-only deep clone of the object graph, returning a deeply normalized `Immut<T>`. Types carrying `&mut`, `&capture`, `&{mut ...}` callables, or scoped resource handles are statically prohibited.
3. `move(value)`: Compiler intrinsic performing affine ownership transfer. Invalidation occurs at the caller's binding, with zero memory copying.
4. `produce(base, recipe)`: Generates an updated immutable value using copy-on-write structural sharing via a mutating draft recipe closure.

### 2.3 Nominal Unwrapping

```ril
fn inner<T, U>(wrapper: T) -> U
```
- Extracts the underlying primitive or compound payload from a single-payload nominal wrapper `T` while preserving original value permissions.

### 2.4 Panic and Assertion Primitives

```ril
fn panic(message: str) -> never
```
- Raises an immediate, deterministic runtime panic, halting normal execution and initiating stack unwinding.

```ril
fn assert(cond: bool, message: str = "assertion failed") -> ()
```
- Compiler intrinsic evaluating a boolean invariant condition. If `cond` evaluates to `true`, yields unit `()`. If `cond` evaluates to `false`, halts execution and triggers a runtime panic with `message`. The compiler MAY accept a compile-time thunk for lazy message formatting.

### 2.5 Error Conversion Helpers

```ril
fn ok_or<T, E>(opt: ?T, err: E) -> Result<T, E> {
    match opt {
        Some(v) -> Ok(v),
        None -> Err(err),
    }
}
```
- Converts an `Option<T>` into a `Result<T, E>` without early return.

## 3. Static Standard Modules

`ril/types` (Types::) and `ril/meta` (Meta::) expose static closure values or sealed static primitives, never fn declarations. Their interfaces use static callable sorts. Bodies use ordinary closures; `[halt] type Name = Expr` may also bind a statically available closure alias or composition result, with inferred results and no left generic header. Interface signatures below are descriptions, not named-fn source syntax.

| Static interface | Callable sort / behavior |
| --- | --- |
| Types::same | halt type(Type,Type) -> bool; canonical graph equality or a neutral result while inputs are abstract |
| Types::literal | halt type(scalar) -> Result<Type,BuildError>; finite admissible literal category |
| Types::fields/elements | halt static descriptor inspection; visibility, known shape and capacity checks, Result for unsupported cases |
| Types::record/tuple | halt type(descriptor sequence) -> Result<Type,BuildError>; validate shape/sort/labels |
| Types::callable_info/rebuild_callable | halt static Result interfaces; preserve modes, binder scope, effects/capabilities and origin identity |
| Types::rewrite_graph | halt type(Type, halt type(Layer) -> Result<Fragment,BuildError>) -> Result<Type,BuildError> |
| Types::edge | halt type(Edge) -> Child; Edge is not a Type or a root Fragment |
| Types::option | halt type(Child,bool) -> Fragment; bool is the inherited frozen context |
| Types::field_fragment | halt type(Field,Fragment) -> FieldFragment; preserve source label and write modifier |
| Types::record fragment overload | halt type([]FieldFragment,bool) -> Result<Fragment,BuildError> |
| Types::keep | halt type(Layer) -> Result<Fragment,BuildError>; retain layer plus transformed child edges |
| Types::optional_fields/readonly_fields | halt type() -> SafePlan; finite certified templates |
| Types::compose | halt type(SafePlan,SafePlan) -> SafePlan; finite first-then-second composition |
| Types::apply_graph | halt type(Type,SafePlan) -> Type; guaranteed well-formed Type output, neutral when unknown |
| Types::require | closed-declaration diagnostic only; not a halt callable, forbidden in all halt contexts |

Descriptor types Layer, Edge, Child, Fragment, Field, FieldFragment, SafePlan and BuildError are static sorts, not runtime data types. Generic symbol placeholders in interface descriptions denote sealed operation schemas over known sorts, not a new universe or permission for runtime generics to take Type. Fields/elements APIs must expose precise Result or known-shape interfaces; unknown input is blocked, never guessed as an atom.

Meta:: supplies certified finite map/filter/fold, split_first, remove_all, tuple operations and safe string parsing/concatenation. Static container schemas provide built-in lifting for known element sorts; arbitrary user sort-polymorphism is not assumed. Exported summaries include relevant output length/source relations and input stability. A halt callback alone supplies no shrinking relation.

BuildError includes duplicate/invalid labels, unsupported shape, sort/kind mismatch, constructor constraints, illegal references, frozen/nominal/binder violations, and CapacityExceeded. Failure returns Err normally; no result is silently discarded. Graph internals use safe compiler storage/counting and cannot introduce hidden language-level panic through worklist overflow.

All static operations obey Chapter 12 callable families and strict provenance. Ordinary static closures can compose these primitives, but their own unmarked status is not inferred away. Resource budgeting is always enforced independently of project lint.

## 4. Validated Graph Inputs

`ril/graph` provides an opaque runtime `Acyclic<T>` package and controlled validating/constructing operations. Validation isolates/freezes the relevant region and returns Result<Acyclic<T>,ValidationError>; it detects cycles in the traversal footprint and preserves a checked stable positive structure. This is ordinary runtime work, not a static type function.

Only controlled constructors/validators produce certificates. Unwrapping/projection interfaces carry the stable-subterm certificate; new function results are not automatically certified subterms. Certificates do not permit negative-recursive callable elimination or unverified callbacks. Scoped resources and stateful payload restrictions follow existing state/freeze rules. A generic halt traversal exposes its admitted domain via this package or an intrinsic positive-inductive classification, not merely Immut<T>.

## 5. Application-Oriented Type Examples

Core examples SHOULD use application records, IDs, tagged configuration/protocol values, serializers, collections, and versioned APIs. There is no built-in Peano Nat family or proof prelude. Users may define ordinary recursive enums when useful, but no such enum is required to use generics, associated members or integer/static-index type functions.

```ril
type UserId(str)
type User = { id: UserId, name: str }
type Page<T> = { items: []T, total: int }
type WirePacket<version: int>(bytes)
let packet: WirePacket<{1}> = WirePacket(b"payload")

type PickFields<T: Record, Keys> where Keys <: keyof T = {
    [key in keyof T if key in Keys]: T[key],
}
type UserSummary = PickFields<User, "id" | "name">
```

This illustrates implicitly erased schema parameters, a nominal protocol-version identity and a constrained mapped schema. The version tag alone does not validate encoding; a runtime parser/constructor performs any domain checks.
