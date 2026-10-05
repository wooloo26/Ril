# 16. Standard Prelude

This chapter defines all built-in types, constructors, and primitive functions provided by the Ril standard prelude, which are implicitly available in every translation unit without explicit import.

---

## 1. Prelude Types and Constructors

The following types and constructors are defined in the prelude and reside in the root namespace:

```
┌──────────────────┬───────────────────────────┬─────────────────────────┐
│ Category         │ Type Names / Signatures   │ Description             │
├──────────────────┼───────────────────────────┼─────────────────────────┤
│ Primitives       │ `bool`, `unit ()`, `never`│ Foundational types      │
│ Signed Integers  │ `i8`, `i16`, `i32`, `i64` │ Two's-complement signed │
│                  │ `int` (alias for `i32`)   │ Default integer type    │
│                  │ `bigint`                  │ Arbitrary-precision     │
│ Unsigned Integers│ `u8`, `u16`, `u32`, `u64` │ Unsigned integers       │
│ Floating-Point   │ `f32`, `f64`              │ IEEE 754 binary32 / 64  │
│ Text and Bytes   │ `str`, `bytes`            │ UTF-8 text, byte buffer │
│ Option Family    │ `type Option<T> {`        │ Optional presence       │
│                  │ `  Some(T), None`         │ Shorthand syntax: `?T`  │
│                  │ `}`                       │                         │
│ Result Family    │ `type Result<T, E> {`     │ Fallible computations   │
│                  │ `  Ok(T), Err(E)`         │                         │
│                  │ `}`                       │                         │
│ Inductive Nat    │ `type Nat {`              │ Inductive Peano naturals│
│                  │ `  Zero, Succ(Nat)`       │                         │
│                  │ `}`                       │                         │
│ Propositional Eq │ `type Eq<A, a: A, b: A> {`│ Proof of definitional   │
│                  │ `  Refl<A, x: A> ->`      │ equality                │
│                  │ `    Eq<A, x, x>`         │                         │
│                  │ `}`                       │                         │
│ Collections      │ `Map<K, V>`, `Set<T>`     │ First-class hash maps   │
│ Modality Types   │ `Immut<T>`                │ Deep immutability family│
│ Kinds and Bounds │ `Type<u>`, `Level`,       │ Universe classification │
│                  │ `Record`, `Row`           │ and row bounds          │
└──────────────────┴───────────────────────────┴─────────────────────────┘
```

---

## 2. Primitive Prelude Functions

The standard prelude root namespace exposes ONLY universally applicable, meta-language operational primitives.

Container-specific mutation and collection manipulation functions (such as `push`, `pop`, `extend`, and `clear` for arrays `[]T`) MUST NOT reside in the standard prelude root namespace. Instead, they are defined within their respective standard library modules (e.g., `ril/array`) and invoked via type-qualified pipeline calls (e.g., `arr !> Array::push(item)`) or block-scoped local imports (`use ril/array::{push, pop}`).

The standard prelude provides exactly eight core operational functions:

### 2.1 Collection Inspection

```ril
fn len(value: T) -> int
```
- Accepts `str`, `bytes`, arrays (`[]T`), `Map<K, V>`, and `Set<T>`.
- Returns the count of Unicode scalars for `str`, bytes for `bytes`, elements for arrays, and key-value entries for maps and sets.
- Maximum capacity is $2^{31} - 1$ ($2147483647$); operations exceeding this limit MUST trigger a runtime panic.

### 2.2 Memory Views and Functional Updates

```ril
fn snapshot<T>(value: T) -> Immut<T>
fn move<T>(value: T) -> T
fn produce<T>(base: T, recipe: fn(mut T) -> () &mut) -> T
```

1. `snapshot(value)`: Constructs an isolated, permanently read-only deep clone of the object graph, returning a deeply normalized `Immut<T>`. Types carrying `&mut`, `&capture`, `&{mut ...}` callables, or scoped resource handles are statically prohibited.
2. `move(value)`: Compiler intrinsic performing affine ownership transfer. Invalidation occurs at the caller's binding, with zero memory copying.
3. `produce(base, recipe)`: Generates an updated immutable value using copy-on-write structural sharing via a mutating draft recipe closure.

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
