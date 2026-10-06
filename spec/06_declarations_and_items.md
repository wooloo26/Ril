# 06. Declarations and Items

This chapter specifies the syntax and semantics of declarations in Ril, including variables, record schemas, mapped types, algebraic data types (ADTs), indexed constructors (GADTs), nominal wrappers, and opaque types.

---

## 1. Top-Level Declarations and Items

A Ril module consists of a sequence of top-level item declarations:

```ebnf
Item ::= LetDecl | FunctionDecl | SumTypeDecl | NominalDecl
       | OpaqueDecl | TypeBindingDecl | EffectDecl | EffectAliasDecl
       | ModuleDecl | UseDecl | TestDecl
```

---

## 2. Variable Bindings (`let`, `let mut`, and `let scoped`)

Variable bindings introduce identifiers associated with values or mutable storage locations:

```ebnf
LetModifier ::= "scoped" | "view"
LetDecl     ::= [ "pub" ] "let" [ LetModifier ] Pattern [ ":" TypeExpression ] [ "=" Expression ] [ "else" Block ]
```

### 2.1 Initialization Rules

1. **Immutable Bindings (`let`)**:
   - An immutable binding MUST be initialized at declaration time (`let x = expr`). Omitting an initializer for an immutable binding is a compile-time static error.
   - An immutable binding CANNOT be reassigned after initialization.
2. **Mutable Bindings (`let mut`)**:
   - A mutable binding (`let mut x: T`) MAY omit its immediate initializer if an explicit type annotation is supplied.
   - The compiler performs **definite assignment analysis**: every code path MUST assign to an uninitialized mutable variable before its first read. Reading an uninitialized variable is a compile-time rejection.
3. **Module-Level Mutable Export Prohibition**:
   - Exporting a mutable module-level binding (`pub let mut`) is **strictly PROHIBITED** and MUST be rejected at compile time. Shared mutable state across module boundaries MUST be encapsulated using algebraic effects, parameter passing, or capability instances (`&capture`).
   - Private module-level mutable variables (`let mut`) are permitted but MUST be initialized with pure constant expressions without side effects.
4. **Scoped Bindings (`let scoped` and `let scoped mut`)**:
   A `scoped` binding associates a system resource handle or dynamic resource with the enclosing lexical block scope. Upon exiting the block (via sequential termination, early `return`, error propagation `?`, `break`/`continue`, effect abort, or runtime panic unwinding), the resource's deterministic cleanup handler is automatically executed in strict Last-In, First-Out (LIFO) order.
5. **Scoped Initialization and Scope Restrictions**:
   - A `scoped` binding MUST be initialized at declaration time (`let scoped x = expr` or `let scoped mut x = expr`). Omitting the initializer is a compile-time static error.
   - A `scoped` binding MUST NOT appear at module scope (`pub let scoped` or top-level `let scoped`). Scoped bindings are strictly restricted to local block scopes; module-level declaration is a compile-time static error.
6. **Live View Bindings (`let view`)**:
   An explicit `let view` binding establishes a read-only live view over an existing reference object handle (see [§05 (Memory Model and Storage)](05_memory_model_and_storage.md#51-live-views)). It strips all write capabilities from the handle while observing subsequent mutations to the underlying heap object. A `let view` binding MUST be initialized at declaration time and CANNOT be combined with `mut` or `scoped`.

---

## 3. Record Schemas and Structural Records

Record schemas declare structural definitions for structured, field-addressed data:

```ebnf
RecordType      ::= "{" [ RecordTypeEntry { "," RecordTypeEntry } [ "," ] ] "}"
RecordTypeEntry ::= RecordTypeField | OpaqueTypeMember | MappedTypeField | RecordTypeSpread | RowTail
RecordTypeField ::= [ "mut" ] Identifier ":" TypeExpression [ "=" Expression ]
OpaqueTypeMember ::= "opaque" "type" Identifier
RecordTypeSpread::= "..." TypeExpression
RowTail         ::= ".." [ Identifier | "_" ]
```

### 3.1 Schema Declarations and Defaults

1. **Default Field Values**: Fields MAY declare default value expressions (`role: str = "guest"`).
   - Defaults MUST be strictly pure expressions: they CANNOT invoke algebraic effects, mutate state, or perform I/O.
   - Defaults evaluate in declaration order and MAY reference previously evaluated fields of the same record.
2. **Option Field Defaults**: Any omitted field whose static type is an `Option` (`?T`) automatically defaults to `None` if no explicit default is supplied.
3. **Closed vs. Open Schemas**:
   - Closed records require exact field matching; unknown fields are statically rejected.
   - Schema composition via type spread (`type Extended = { ...Base, extra: T }`) copies all fields, types, and defaults from `Base`, with later fields shadowing earlier matching labels.
4. **Target-Typing of Record Literals**:
   When the target record schema is uniquely known from context (e.g., variable annotation, return type, or parameter type), the schema prefix MAY be omitted (`let u: User = .{ id: 1, name: "Alice" }`).

### 3.2 Associated Type Members and Recursive Records

```ril
type EncoderBox = {
    opaque type Item,
    value: Item,
    encode: fn(Item) -> bytes,
}
type Tree<T> = { value: T, children: []Tree<T> }
```

OpaqueTypeMember binds the chosen type for subsequent fields without a runtime Type slot. Construction supplies `Item: type[ConcreteType]`; opening the package keeps value and operation types correlated under an abstract lexical witness (Chapter 04). It is allowed in record schemas and struct variants only, without mut, defaults, local representation or generic header. Constructor-local generic parameters remain an alternative for hidden payload types in positional variants.

Recursive structural records obey constructor guarding and regularity checks. They use managed references without explicit boxing; possible runtime cycles do not certify halt recursion.

---

## 4. Mapped Types and Field Indexing

Mapped types generate new record schemas by transforming fields of an existing non-dependent record schema:

```ebnf
MappedTypeField ::= [ "mut" ] "[" Identifier "in" "keyof" TypeExpression
                   [ "if" Expression ] [ "as" Expression ] "]" ":" TypeExpression [ "=" Expression ]
```

```ril
type Source = { mut name: str, count: int = 1 }
type ReadonlyFields<T: Record> = { [k in keyof T]: T[k] }
type WritableFields<T: Record> = { mut [k in keyof T]: T[k] }
type Prefixed<T: Record> = { [k in keyof T as "field_" + k]: T[k] }
```

### 4.1 Key Extraction (`keyof T`) and Indexed Projection (`T[k]`)

1. **`keyof T`**: Denotes the finite string-literal union of a non-dependent record's field labels, or `never` for an empty record.
2. **`T[k]`**: Denotes the payload type selected by a stable key `k: keyof T`. For `value: T`, runtime indexing `value[key]` has static type `T[key]`.
3. **Dynamic Record Update**:
   `record = .{ ...record, [key]: replacement }` updates an existing record entry where `key` is known to exist and `replacement` has type `T[key]`.

### 4.2 Mapped Type Invariants

1. **Default Immutability**: Mapped fields are immutable by default, regardless of whether the source field was `mut`. An explicit `mut` modifier on the mapped field declaration is required to produce writable fields.
2. **Removal of Inherited Defaults**: Mapped schemas strip away all inherited default field values from the source schema.
3. **Static Filtering and Renaming**:
   The optional `if` condition and `as` name expressions are pure static expressions over the implicitly erased key variable. In halt declarations, every dependency must be halt-admissible; ordinary static contexts permit ordinary type computation under compiler budgets. If renaming produces duplicate labels, declaration elaboration fails. A halt builder with uncertain label uniqueness must instead return a checked Result; a compilation error is not a halt callable's normal return.

---

## 5. Sum Types (Algebraic Data Types) and GADTs

Sum types represent tagged disjoint unions of distinct variants:

```ebnf
SumTypeDecl   ::= [ "pub" ] "type" Identifier [ GenericParameters ] [ WhereClause ]
                  "{" VariantDecl { "," VariantDecl } [ "," ] "}"
VariantDecl   ::= Identifier [ GenericParameters ]
                  [ "(" VariantFields ")" | "{" StructFields "}" ] [ "->" TypeExpression ]
VariantFields ::= VariantField { "," VariantField } [ "," ]
VariantField  ::= Identifier ":" TypeExpression | TypeExpression
StructFields  ::= StructFieldEntry { "," StructFieldEntry } [ "," ]
StructFieldEntry ::= RecordTypeField | OpaqueTypeMember
```

### 5.1 Variant Construction and Target-Typing

1. **Variant Forms**:
   - Unit variants: `Quit`
   - Positional tuple variants: `Write(str)`
   - Structural record variants: `Move { x: int, y: int }`
2. **Target-Typing**: When the outer sum type is known from context, the type qualification prefix MAY be omitted (`let msg: Message = Move.{ x: 10, y: 20 }`).
3. **First-Class Constructors**: Single-payload positional variants act as first-class constructor functions (`Message::Write` has type `fn(str) -> Message`).
4. **Recursive Data Without Boxing**: Recursive sum types use GC-managed references; no manual indirection types are required.

### 5.2 Typed Payload Constructors

Constructor-local generics are implicitly compile-time-only, and explicit result equations can constrain the application's type parameter:

```ril
type ConfigValue<T> {
    Text(str) -> ConfigValue<str>,
    Count(int) -> ConfigValue<int>,
    Enabled(bool) -> ConfigValue<bool>,
}

fn read_text(value: ConfigValue<str>) -> str {
    match value { Text(text) -> text }
}
```

The result type excludes Count/Enabled here, so matching Text is exhaustive. This is constructor/type refinement, not user-supplied mathematical proof.

1. Type/static-index parameters scope later payload types and result equations; ordinary runtime payload values do not enter arbitrary type computation.
2. Constructor-local hidden types remain local to match arms unless repacked. For example `type Encodable { Pack<T>(T, fn(T) -> bytes) }` pairs an unknown payload with its operation without an explicit erasure modifier.
3. Finite constructor equations refine indices and eliminate impossible cases. A recognized strict subindex may vary on a recursive payload only when index erasure leaves one finite representation and does not drive layout/reflection; no automatic theorem search is implied.

---

## 6. Nominal Wrappers and Opaque Types

### 6.1 Nominal Single-Payload Wrappers

A single-payload nominal wrapper isolates an underlying type into a distinct nominal type:

```ebnf
NominalDecl ::= [ "pub" ] "type" Identifier [ GenericParameters ] "(" VariantFields ")" [ WhereClause ]
```

```ril
type UserId(str)
type RequestId(str)
```

1. **Operator Encapsulation**: Nominal wrappers do NOT inherit arithmetic operators (`+`, `-`) or relational comparisons (`<`, `>`). Applying arithmetic operators directly to nominal wrappers is a compile-time static error.
2. **Unwrapping via `inner`**: The prelude function `inner(wrapper)` extracts the underlying primitive or compound value with its original type and access permissions.
3. **Equality**: Homogeneous equality (`==`, `!=`) is supported and compares inner values.
4. **Prohibition of Implicit String Interpolation**: Single-payload nominal wrappers do NOT implicitly unpack in string templates. Formatted string interpolation requires explicit unwrapping via `inner(wrapper)` (e.g., `"{inner(uid)}"`). Directly embedding a nominal wrapper in string interpolation without `inner()` is a compile-time static error (`NominalInterpolationRequiresInnerError`).

### 6.2 Opaque Types

```ebnf
OpaqueDecl ::= [ "pub" ] "opaque" "type" Identifier [ GenericParameters ] [ WhereClause ] "=" TypeExpression
```

1. **Module Privacy**: An opaque type introduces a nominal type whose underlying representation is visible ONLY within its defining module.
2. **Encapsulation Guarantees**: Outside the defining module, clients CANNOT construct, destructure, or access fields of an opaque type, nor invoke `inner()` on it. All operations MUST be mediated through functions exported by the defining module.

---

## 7. Type Aliases (`type Name = T`)

Type aliases introduce transparent synonyms for existing type expressions:

```ebnf
TypeBindingDecl ::= [ "pub" ] [ "halt" ] "type" Identifier
                    [ GenericParameters ] [ WhereClause ] "=" TypeBindingInitializer
TypeBindingInitializer ::= TypeExpression | Expression
```

1. **Structural Equivalence**: A type alias does not introduce a distinct nominal type. Its valid normalized description is interchangeable with the target; this does not erase the halt admissibility of dependencies used to elaborate it.
2. **Compile-Time Representation**: Aliases normalize on demand to finite regular graphs or neutral computations. Recursive aliases are not infinitely unfolded. They incur no extra runtime representation overhead.
3. **Contrast with Nominal Wrappers**: Unlike nominal wrappers (`type UserId(str)`), type aliases preserve all operators, methods, and structural properties of the target type.


## 8. Static Callable Bindings

```ebnf
TypeBindingDecl ::= [ "pub" ] [ "halt" ] "type" Identifier
                    [ GenericParameters ] [ WhereClause ] "=" TypeBindingInitializer
TypeBindingInitializer ::= TypeExpression | Expression
```

Direct type/sort descriptions create aliases. An expression producing a static callable creates a type-function binding, with ordinary inferred parameter/result sorts. A callable binding MUST NOT have a left-hand generic header: its parameters belong to the closure. Generic headers remain available for ordinary data schemas, aliases, ADTs and constructor-kinded erased parameters, not for static callable bindings.

```ril
halt type Box = \T: Type -> type[{ value: T }]
type IntBox = Box(type[int])

halt type SameBox = Box
type Mapper = type(Type) -> Type
type Normalize = \T: Type, simplify: Mapper -> {
    let next = simplify(T)
    if Types::same(T, next) { T } else { Normalize(next, simplify) }
}
```

A callable initializer need not be a syntactic lambda: aliases and composition results are allowed if they are statically available callable values of the static family. `halt` requires a certified halt value and halt-admissible initializer dependencies; an unmarked binding forgets the halt guarantee and cannot regain it merely because initialization succeeded. Runtime fn values are not static initializers.

Static functions use ordinary parenthesized calls everywhere, including annotation expressions, callbacks and intermediate callable values. `Box<...>` and `Box::<...>(...)` are not callable-binding invocation forms. `type BoxSchema<T> = { value: T }` retains the distinct data/schema constructor application `BoxSchema<int>`.

Erased constructor-kinded parameters such as F<_> retain their constructor application F<T>. A static callable can be exposed through a constructor-kinded parameter only with matching arity/sorts and preserved admissibility; this is an erased constructor interface, not a second direct-call spelling for a callable binding. Static callable-sort parameters use normal calls F(T).

### 8.1 Recursive Binding and Initialization

Direct lambda initializers (possibly parenthesized) introduce prebound recursive static items. Their bodies can refer to themselves and other direct-lambda items in scope; signatures, result sorts and halt progress are jointly checked by SCC. Only item names receive recursive visibility. Let captures remain lexical, immutable and statically available; later/uninitialized captures cannot be read.

Non-lambda callable initializers are evaluated in lexical initialization order. They cannot eagerly refer to themselves or cyclic/forward-uninitialized callable values. Composition and aliasing do not invent a new recursion mechanism. Unresolved sorts are rejected rather than fixed by a convenient later call.

```ril
halt type Pair = \U: Type, T: Type -> type[(T, U)]
type P = Pair(type[str], type[int])
-- halt type Bad<U> = \T: Type -> type[(T,U)] -- reject double parameter groups
```

The closure grammar, delimiters and result inference remain ordinary. Static callable annotations always include their result arrow, just as runtime fn annotations do; no optional-return-arrow rule needs special lambda parentheses.

### 8.2 Implicit Compile-Time Positions

Generic parameters and constructor-local type/index parameters have implicit erasure. Static type-function values and opaque member witnesses have no ordinary runtime value representation. Ordinary parameters/fields remain runtime data and cannot be marked for erasure. Move a static index to a generic parameter, e.g. `type WirePacket<version: int>(bytes)` or `fn process<version: int>(packet: WirePacket<{version}>)`.

Erasure never deletes required evaluation of an ordinary runtime argument. A runtime value cannot become a static index merely because an implementation could optimize it away. No explicit erasure marker participates in equality, variance or callable reflection.
