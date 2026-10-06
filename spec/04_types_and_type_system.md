# 04. Types and Type System

This chapter defines application data types, static sorts, finite recursive type graphs, equality, subtyping, inference, finite static indices, and existential packages. Runtime effects and state capabilities retain Chapters 10 and 11 semantics.

---

## 1. Types, Sorts, and Stages

### 1.1 Runtime Types and Static Descriptions

`Type` classifies compile-time descriptions of runtime data types. It is a static sort, not a runtime type and not an element of itself. `Record` bounds finite non-dependent structural record descriptions; `Row` classifies finite rows. `Type<u>`, `Level`, and universe arithmetic are not part of the core.

Generic type/value parameters are implicitly compile-time-only; no explicit erasure modifier is used. Runtime generics accept runtime types. A runtime `fn<T>(x: T) -> T` cannot be instantiated with `T = Type`. Runtime function declarations and function types MUST NOT accept or return static sorts. Static computations are declared using `type Name = \parameters -> body`, optionally prefixed by `halt`; they do not use `fn` (Chapter 12).

Static callable sorts use `[halt] type(S1, ..., Sn) -> R` with a mandatory result sort, e.g. `halt type(Type) -> Type` or `halt type(Type) -> bool`. Missing `-> R` is rejected. Callable declarations infer their closure result and do not repeat a declaration return arrow. Their parameters belong only to the closure, with no separate generic header.

Standard arrays, tuples, Option, Result, and descriptor records/ADTs admit static sort lifting: `[]Type`, `?Type`, and `Result<Type, str>` are static-only containers, not ordinary runtime generic instantiations. An ordinary static payload makes the enclosing descriptor static-only. The `opaque type Item` member binder is a dedicated exception: it binds subsequent runtime fields and is not a stored static payload, so its package can remain a runtime type.

No operation reifies a static sort as Type. `type[Type]` and `typeof(type[int])` are rejected. `typeof` reads the static type of a runtime data expression without executing it or lifting its runtime contents.

### 1.2 Parameters and Constraints

Erased generic parameters MAY be runtime type parameters, finite static value indices, row parameters, effect parameters, or state capability parameters. `F<_>` and `F<_, _>` declare arity only, not a halt promise. A halt context needs a certified constructor domain or an explicit guarantee such as `F: halt type(Type) -> Type` before invoking F. Explicit static callable sorts distinguish total and unrestricted constructors.

```ebnf
WhereClause ::= "where" Constraint { "," Constraint }
Constraint  ::= TypeExpression ( "=" | "<:" ) TypeExpression
              | Identifier "lacks" PlainStringLiteral
```

Constraints follow from declared assumptions and concrete arguments. The compiler MUST NOT search for implicit implementations or arbitrary mathematical proofs. A kind-polymorphic constructor of unknown variance is invariant. Type-function result equality does not generally determine its inputs.

### 1.3 Static Availability and Family Separation

Static inputs come from type parameters, erased index witnesses, type literals, immutable static bindings, and static computations. Ordinary runtime let bindings are not static merely because they are read-only.

Runtime callables and static callables are distinct sorts with no cross-family coercion or invocation. `halt fn` executes only certified runtime callables; `halt type` executes only certified static callables. Sealed primitives and data constructors have stage-specific checked operations. Signature and annotation elaboration is a separate static operation, with the strict halt boundary specified in Chapter 12; it is not a runtime invocation of a type function.

---

## 2. Type Identity, Recursion, and Reduction

### 2.1 Guarded Regular Type Graphs

Transparent recursive schemas are supported:

```ril
type Tree<T> = { value: T, children: []Tree<T> }
type Node = { name: str, mut next: ?Node }
```

Every cycle in a recursive declaration SCC MUST pass through a data constructor layer (record, tuple, array, or tagged payload). Alias forwarding and unreduced computation do not guard a cycle. Recursive rows cannot grow indefinitely.

Representation-relevant parameters on recursive back-edges MUST be original parameters or fixed finite permutations. Growing applications such as `type Grow<T> = { next: ?Grow<[]T> }` are rejected in this revision, including nominal forms that would require unbounded representation specialization. Indexed nominal ADTs have a narrow erased-index exception (Chapter 06): recognized strict subindices may vary without changing the family's finite representation or driving structural reflection.

Metadata graphs are finite; runtime values of a graph type can still contain cycles. Metadata regularity does not certify runtime induction.

### 2.2 Definitional Equality

Equality includes alpha-renaming, transparent aliases, checked computational reduction, canonical static index terms, and structural graph comparison. Record labels, payloads, type-member binders/write modifiers, and frozen markers participate; field order, alias names, and default expressions do not.

Recursive structural graphs are compared by constructor-respecting paired-node coinductive checks, not infinite expansion or an arbitrary depth cutoff. Nominal nodes compare declaration identity and canonical/symbolic arguments. Opaque representation remains hidden outside its module. Type functions cannot dynamically declare fresh nominal identities.

Unresolved applications remain neutral and compare by congruence. Matching has three outcomes: match, disjoint, or blocked. An unknown input MUST NOT fall into a default arm merely because a preceding pattern cannot yet be decided. Known constructors with unknown children MAY retain a known outer structure and blocked child computations.

Ordinary type computations are evaluated only when needed and under finite implementation resource budgets. A successful normalized result must be a well-formed type. Budget exhaustion or static failure yields no type; it does not authorize an arbitrary result or prove divergence. Only halt computations carry a normal-termination guarantee. The halt dependency boundary is preserved through aliases, imports, reflection, and caches (Chapter 12).

Runtime equality, function extensionality, arbitrary algebraic identities, and proof rewriting do not establish type equality. The core has no Eq/Refl/rewrite proof system.

---

## 3. Subtyping and Variance

Ril defines a reflexive, transitive subtyping relation $A \lt : B$ governed by the following normative rules:

### 3.1 Primitive and Literal Subtyping

1. **Bottom Type**: The type `never` is the bottom of the subtyping lattice: for all types $T$, $\text{never} \lt : T$.
2. **Literal Types**: A literal type is a subtype of its corresponding primitive:
   - `"hello" <: str`
   - `42 <: int`
   - `true <: bool`
3. **Homogeneous Literal Unions**: A union of literal types is ordered by set inclusion:
   - `"a" | "b" <: "a" | "b" | "c" <: str`
4. **Prohibition of Arbitrary Untagged Unions**: Untagged union types `A | B` between distinct non-literal types (including but not limited to `int | str`, `User | Admin`, or `str | fn() -> str`) MUST be rejected as compile-time static errors. A union type expression `T_1 | T_2 | ... | T_n` SHALL be valid if and only if all constituents $T_i$ are literal types inhabiting the identical underlying primitive type (e.g., `"a" | "b"` or `1 | 2 | 3`). Heterogeneous data SHALL be represented exclusively via tagged sum types.
5. **No Implicit Numeric Coercion**: Primitive numeric types (`i8`..`i64`, `u8`..`u64`, `f32`, `f64`) are mutually distinct. There is NO implicit widening or subtyping between different numeric types. `int` and `i32` are identical aliases.
6. **Prohibition of Intersection Types and Nominal Unwrapping**: Ril provides no intersection types and no implicit nominal unwrapping.

### 3.2 Record Subtyping and Row Polymorphism

1. **Closed Records**: Closed records do NOT exhibit width subtyping. A record `{ name: str, id: int }` is NOT a subtype of `{ name: str }`. Extra fields are rejected to guarantee deterministic layout and prevent unintentional data slicing.
2. **Open Row Parameters (`..`)**: To accept records with additional fields, parameter types MUST specify an anonymous open row `{ name: str, .. }` (desugared to a fresh row parameter `<R: Row> { name: str, ..R }`).
3. **Partial Row Completion in Returns (`.._`)**: Return types MAY specify `{ name: str, .._ }`, which requires the specified fields while inferring the remaining row tail from the returned expression into a concrete closed record type.
4. **Depth Subtyping & Invariance**:
   - Read-only fields are covariant: if $T \lt : U$, then `{ x: T } <: { x: U }`.
   - Mutable fields (`mut`) are strictly invariant: `{ mut x: T }` and `{ mut x: U }` are compatible if and only if $T \equiv U$.

### 3.3 Function and Callable Variance

For function types:

$$
f_1 = \text{fn}(A) \to B \ @\mathcal{E}_1 \ \mathbin{\And}\mathcal{S}_1, \quad f_2 = \text{fn}(C) \to D \ @\mathcal{E}_2 \ \mathbin{\And}\mathcal{S}_2
$$

The formal subtyping relation satisfies:

$$
f_1 \lt : f_2 \iff C \lt : A \land B \lt : D \land \mathcal{E}_1 \subseteq \mathcal{E}_2 \land \mathcal{S}_1 \sqsubseteq \mathcal{S}_2
$$

- Parameters are **contravariant**. Shared read-only parameter views (`x: T`) are contravariant in input positions.
- Return types are **covariant**.
- Algebraic effects are **covariant by set inclusion** ($\mathcal{E}_1 \subseteq \mathcal{E}_2$).
- Mutable parameter locations (`mut x: T`) are strictly **invariant**.
- State capabilities are **covariant under capability subsumption** across the capability preorder lattice ($\mathcal{S}_1 \sqsubseteq \mathcal{S}_2$, where `mut` $\sqsubset$ `^mut`): a function guaranteeing localized parameter mutation is a valid subtype of a function permitted retained mutable sharing (`fn(P) -> R &mut <: fn(P) -> R &^mut`, where `P` contains identical mutable parameters). Retained mutable sharing `&^mut` and closure capture `&capture` represent orthogonal lattice dimensions and SHALL NOT subsume or abstract into each other (`&^mut` does not subtype `&capture`, nor `&capture` subtype `&^mut`).
- For the same external binding identity `x`, read access is subsumed by mutation, which is subsumed by named retained sharing: `&{x}` $\sqsubset$ `&{mut x}` $\sqsubset$ `&{^mut x}`. A callable carrying `&{^mut x}` MAY hide `x` only behind an interface retaining both `&capture` and anonymous `&^mut`; hiding the name MUST NOT erase the sharing hazard or origin summary (Chapter 11, §6). Distinct binding identities cannot be substituted merely because their value types agree.

### 3.4 Data-Parameter Variance

Variance of data parameters across generic types follows positive and negative positions in visible definitions:
- A type parameter occurring exclusively in positive (output/read-only) payload positions is **covariant**.
- A type parameter occurring in negative (input) positions is **contravariant**.
- In-place mutation, static indices, type matching, and unknown or hidden constructor variance impose strict **invariance**.

### 3.5 Collection Variance

1. **Read-Only Collections**: Immutable array views (`[]T`) are covariant: if $T \lt : U$, then `[]T <: []U`. Consequently, an empty array of bottom types `[]never` can initialize any `[]T`.
2. **Writable Collections**: Writable locations and mutable arrays are strictly invariant. A read-only collection view CANNOT be cast, coerced, or upgraded to a writable collection.

### 3.6 Deep Immutability (`Immut<T>`)

`Immut<T>` is a checked deep-freezing modality with no extra runtime wrapper representation. Its legal domain excludes scoped resources and prohibited stateful or capability-bearing payloads (Chapters 05 and 11).

1. Immutable scalar types normalize: `Immut<int>` is identical to `int`; the same applies to bool, other numeric scalars, str, bytes, unit, and never.
2. Reference constructors MUST retain a frozen marker at every reference layer. Payloads are recursively normalized and field write permissions removed, but freezing the container itself MUST NOT be erased. In particular, `Immut<[]int>` is NOT identical to `[]int`: the latter may be a live view of an array with writable aliases.
3. Idempotence holds: `Immut<Immut<T>>` is identical to `Immut<T>`. Covariance holds on the modality's legal domain. Well-formed frozen types satisfy Shareable under the existing capability restrictions.
4. Frozen arguments remain admissible at ordinary read-only parameter positions. There is no implicit upgrade from an unfrozen view to a frozen value.
5. A mapped type that removes `mut` changes a type description; it neither freezes an existing value nor establishes Shareable. Reflection and rebuilding MUST preserve frozen markers.
6. Freezing does not establish acyclicity or inductive well-foundedness; `clone_immut` preserves object cycles.

---

## 4. Type Inference and Generalization

Ril employs bidirectional local type inference combined with a strict **value restriction** on generic generalization:

### 4.1 Value Restriction on Generalization

A generic variable not free in the typing environment is generalized into a polymorphic type $\forall \alpha. T$ if and only if its initializing expression is **syntactically non-expansive**:
1. **Non-Expansive Expressions**:
   - Literals (integers, strings, booleans, unit).
   - Named functions and closure expressions (`\x -> ...`).
   - Immutable records, tuples, or constructors composed exclusively of non-expansive expressions.
2. **Expansive Expressions (Generalization Prohibited)**:
   - Mutable variable bindings (`let mut`).
   - Mutable collection initializations (arrays, maps).
   - Function application expressions (`f(x)`).
   - Expressions capturing external mutable state.

An expansive expression is inferred as a monomorphic type variable and MUST NOT be generalized into a polymorphic scheme.

### 4.2 Generic Body Checking and Public Export Invariants

1. **Body Checking Under Declared Constraints**:
   A generic function or type body is checked strictly under its declared parameters and `where` constraints. Instantiation at call sites cannot repair a body that fails to typecheck under its generic signature.
2. **Prohibition of Unresolved Variables in Public Declarations**:
   A public declaration (`pub`) CANNOT contain unresolved monomorphic type variables.
3. **Explicit Annotations for Complex Typing**:
   Higher-rank callable arguments, polymorphic recursion, and ambiguous constructor applications require explicit type annotations or explicit generic arguments.
4. **Generic Mutable Parameters (`mut T`)**:
   A generic `mut T` parameter accepts a writable location of type `T`. Its body MAY replace that location with another value of type `T`, but reassignment CANNOT change static indices in its static type.
5. **Polymorphic Storage**:
   A mutable location MAY store an explicitly checked polymorphic callable value, but does not generalize its own unresolved variables.

---

## 5. Finite Static Indices and Existential Packages

### 5.1 Static Indices

Indices MAY be integers, booleans, strings, finite enum terms, or finite stable inductive constructor terms. Concrete applications use statically available constants or completed static results; lexical erased witnesses can remain symbolic. Runtime object references, live reads, floating-point indices, and arbitrary runtime let values are not index domains.

Constructor equations and canonical/symbolic terms provide finite GADT refinement. General dependent functions or records over runtime field values, arbitrary equality transport, and mathematical theorem search are outside the core. An index whose computation needs an ordinary type function is forbidden in a halt declaration's elaboration even if that application previously succeeded.

### 5.2 Opaque Associated Type Members

```ril
type EncoderBox = {
    opaque type Item,
    value: Item,
    encode: fn(Item) -> bytes,
}

fn encode_int(value: int) -> bytes { bytes(str(value)) }
let number_encoder: EncoderBox = .{
    Item: type[int],
    value: 42,
    encode: encode_int,
}

fn encode_box(box: EncoderBox) -> bytes {
    let .{ value, encode } = box
    encode(value)
}
```

An opaque type member binds a runtime type for later value/operation fields of its record or struct variant. Each construction supplies a statically available Type choice and checks all dependent fields against that same choice. The type witness is implicitly compile-time-only; it is not a stored runtime Type value and does not make EncoderBox static-only. Erasure does not promise that packaging, adapters or normal GC layout information have no runtime cost.

Opening/destructuring a package introduces a lexical abstract witness shared by its fields. Projections from the same stable package binding retain that correlation; listing Item in a record pattern binds the abstract witness, not a runtime field. The concrete representation is unavailable to generic consumers. Distinct openings are not identified without a checked common witness, and witnesses cannot escape separately from their values/operations; a package may be repacked.

The member cannot be mut, reassigned, given a default/representation initializer, or reflectively inspected as a concrete type. Constructing or projecting a Type witness does not lift arbitrary runtime data into the static stage. Module-level `opaque type Token = str` instead has one declaration identity and a fixed module-private representation; it does not select a different hidden type for each value.

Opening a mutable package root MUST bind one current package value before projecting dependent fields. Replacing that root does not make a prior opening's witness equal to the replacement's witness. Spreading or repacking fields preserves their checked common witness; explicitly changing Item requires rechecking every dependent field.

Packages with opaque type members are not ordinary Record rows. Row mapping, runtime record iteration and general graph rewriting do not open or delete their type binders. Types::/SafePlan preserve such packages as atoms. Reflection can report the public abstract member declaration, never its hidden concrete choice.

Generic record-key operations retain the compiler-checked correlation `key: keyof T` with `value: T[key]`; this special eliminator is not arbitrary runtime dependent typing.
