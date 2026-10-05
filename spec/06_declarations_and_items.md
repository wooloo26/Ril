# 06. Declarations and Items

This chapter specifies the syntax and semantics of declarations in Ril, including variables, record schemas, mapped types, algebraic data types (ADTs), indexed constructors (GADTs), nominal wrappers, and opaque types.

---

## 1. Top-Level Declarations and Items

A Ril module consists of a sequence of top-level item declarations:

```ebnf
Item ::= LetDecl | FunctionDecl | SumTypeDecl | NominalDecl
       | OpaqueDecl | TypeAliasDecl | EffectDecl | EffectAliasDecl
       | ModuleDecl | UseDecl | TestDecl
```

---

## 2. Variable Bindings (`let` and `let mut`)

Variable bindings introduce identifiers associated with values or mutable storage locations:

```ebnf
LetDecl ::= [ "pub" ] "let" Pattern [ ":" TypeExpression ] [ "=" Expression ] [ "else" Block ]
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

---

## 3. Record Schemas and Structural Records

Record schemas declare structural definitions for structured, field-addressed data:

```ebnf
RecordType      ::= "{" [ RecordTypeEntry { "," RecordTypeEntry } [ "," ] ] "}"
RecordTypeEntry ::= RecordTypeField | MappedTypeField | RecordTypeSpread | RowTail
RecordTypeField ::= [ "mut" | "erased" ] Identifier ":" TypeExpression [ "=" Expression ]
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

### 3.2 Dependent Records and Existential Packages

1. **Dependent Fields**: Later field types in a record schema MAY reference preceding immutable stable fields:
   ```ril
   type Event<P: Record> = { kind: keyof P, payload: P[kind] }
   ```
2. **Existential Packages**:
   Erased type fields allow bundling abstract types with implementations:
   ```ril
   type Package = { erased Item: Type, value: Item }
   let p: Package = .{ Item: int, value: 42 }
   ```
   Opening an existential package introduces an abstract type identity distinct from all other instances.

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
3. **Halting Filtering and Renaming**:
   The optional `if` condition and `as` name expressions are pure halting expressions over the erased key variable. If the `as` expression causes two distinct source keys to map to the identical string label, compilation MUST fail with a duplicate label collision error.

---

## 5. Sum Types (Algebraic Data Types) and GADTs

Sum types represent tagged disjoint unions of distinct variants:

```ebnf
SumTypeDecl   ::= [ "pub" ] "type" Identifier [ GenericParameters ] [ WhereClause ]
                  "{" VariantDecl { "," VariantDecl } [ "," ] "}"
VariantDecl   ::= Identifier [ GenericParameters ]
                  [ "(" VariantFields ")" | "{" StructFields "}" ] [ "->" TypeExpression ]
VariantFields ::= VariantField { "," VariantField } [ "," ]
VariantField  ::= [ "erased" ] Identifier ":" TypeExpression | TypeExpression
StructFields  ::= RecordTypeField { "," RecordTypeField } [ "," ]
```

### 5.1 Variant Construction and Target-Typing

1. **Variant Forms**:
   - Unit variants: `Quit`
   - Positional tuple variants: `Write(str)`
   - Structural record variants: `Move { x: int, y: int }`
2. **Target-Typing**: When the outer sum type is known from context, the type qualification prefix MAY be omitted (`let msg: Message = Move.{ x: 10, y: 20 }`).
3. **First-Class Constructors**: Single-payload positional variants act as first-class constructor functions (`Message::Write` has type `fn(str) -> Message`).
4. **Recursive Data Without Boxing**: Recursive sum types use GC-managed references; no manual indirection types are required.

### 5.2 Indexed Constructors (GADTs)

A variant MAY declare constructor-specific erased parameters, named dependent payload binders, and an explicit return type:

```ril
type Vec<T, n: Nat> {
    Nil<T> -> Vec<T, Nat::Zero>,
    Cons<T, n: Nat>(head: T, tail: Vec<T, n>) -> Vec<T, {Nat::Succ(n)}>,
}
```

1. **Named Payload Binders**: Named payload binders in constructors are in scope for subsequent payload types and the return type index equations.
2. **Existential Parameter Scoping**: Constructor-local generic parameters remain local to match arms unless repackaged into existential wrappers.
3. **Pattern Refinement**: Pattern matching on indexed constructors refines static type indices, eliminating impossible variant branches from exhaustiveness requirements.

---

## 6. Nominal Wrappers and Opaque Types

### 6.1 Nominal Single-Payload Wrappers

A single-payload nominal wrapper isolates an underlying type into a distinct nominal type:

```ebnf
NominalDecl ::= [ "pub" ] "type" Identifier [ GenericParameters ] "(" VariantFields ")" [ WhereClause ]
```

```ril
type Meters(f64)
type Seconds(f64)
```

1. **Operator Encapsulation**: Nominal wrappers do NOT inherit arithmetic operators (`+`, `-`) or relational comparisons (`<`, `>`). Applying arithmetic operators directly to nominal wrappers is a compile-time static error.
2. **Unwrapping via `raw`**: The prelude function `raw(wrapper)` extracts the underlying primitive value with its original type and access permissions.
3. **Equality**: Homogeneous equality (`==`, `!=`) is supported and compares inner values.
4. **Transparent String Interpolation**: Single-payload wrappers over primitives automatically format as their inner value in string templates without calling `raw()`.

### 6.2 Opaque Types

```ebnf
OpaqueDecl ::= [ "pub" ] "opaque" "type" Identifier [ GenericParameters ] [ WhereClause ] "=" TypeExpression
```

1. **Module Privacy**: An opaque type introduces a nominal type whose underlying representation is visible ONLY within its defining module.
2. **Encapsulation Guarantees**: Outside the defining module, clients CANNOT construct, destructure, or access fields of an opaque type, nor invoke `raw()` on it. All operations MUST be mediated through functions exported by the defining module.

