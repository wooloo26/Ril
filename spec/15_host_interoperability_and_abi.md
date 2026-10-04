# 15. Host Interoperability and ABI

This chapter specifies foreign host contracts (`decl`), boundary bridging modules (`.d.ril` and `.ril.ts`), numeric value mappings, byte representations, TypedArray adapters, and asynchronous promise integration for JavaScript and Native targets.

---

## 1. Foreign Host Contracts (`decl`)

The `decl` item establishes strongly typed interfaces to external host systems:

```ebnf
HostDecl ::= "decl" PlainStringLiteral ( HostItem | "{" { Separator } [ HostItem { Separators HostItem } [ Separators ] ] "}" )
HostItem ::= HostFunctionDecl | HostTypeDecl | HostValueDecl
```

```ril
decl "node:crypto" {
    type Hash
    fn createHash(algorithm: str) -> Hash @Io
    fn randomBytes(size: int) -> bytes @Io
}
```

1. **Host Types**: Opaque types declared under `decl` represent foreign handles managed by the host environment.
2. **Host Functions**: Functions declared under `decl` omit implementation bodies; implementations are linked from host libraries or compiled boundary modules.
3. **Purity Restrictions on Host Declarations**:
   - A host declaration CANNOT be marked `halt`.
   - Host declarations CANNOT manufacture propositional equality proofs (`Eq`) or synthesize trusted erased evidence.
4. **Lossless Option Invariant**:
   Where the ordinary nullable JavaScript mapping would lose constructor distinctions (as with nested Options `??T`), an explicit adapter MUST define a lossless representation; falling back to untyped `any` is strictly prohibited.

---

## 2. JavaScript / TypeScript Boundary Architecture

For JavaScript targets, Ril uses contract-driven boundary derivation:

```
┌─────────────┐       derives        ┌──────────────┐       generates       ┌─────────────┐
│   .d.ril    │ ───────────────────> │   .ril.ts    │ ───────────────────>  │    .mjs     │
│ Host Schema │                      │ Bridge Stubs │                       │ Output ESM  │
└─────────────┘                      └──────────────┘                       └─────────────┘
```

1. **Boundary Validation**: The derived `.ril.ts` bridge module enforces incoming type checks, numeric boundary constraints, and error mappings.
2. **Standard ESM Linkage**: Exported and imported symbols use standard ECMAScript Module (ESM) conventions.

---

## 3. Numeric and Byte Boundary Mappings

When values cross the boundary between Ril and JavaScript, conforming implementations MUST adhere to the following strict conversion rules:

| Ril Type | JavaScript / TypeScript Type | Boundary Conversion and Validation Invariant |
| :--- | :--- | :--- |
| `i8`, `u8`, `i16`, `u16`, `i32` / `int`, `u32` | `number` | MUST be a finite integer within the declared type's range. `-0` normalizes to `0`. Out-of-range values or fractional numbers MUST trigger a runtime panic. |
| `i64`, `u64` | `bigint` | MUST be a JavaScript `bigint` within the declared bit-width range. |
| `bigint` | `bigint` | Maps directly to any JavaScript `bigint`. |
| `f32` | `number` | Maps to IEEE 754 binary32 representation, including NaN, signed zeros, and signed infinities. |
| `f64` | `number` | Maps directly to IEEE 754 binary64 representation. |
| `bytes` | `Uint8Array` | Importing copies host bytes into an immutable Ril buffer. Exporting copies Ril bytes into a detached `Uint8Array`. Storage is NEVER shared live across the boundary. |

### 3.1 Anti-Coercion Invariant

Host boundary crossings **MUST NEVER silently truncate, wrap, or coerce** invalid values. Any representation mismatch, fractional float passed to an integer parameter, or range violation MUST trigger an immediate runtime panic at the boundary.

### 3.2 Safe Integer Conversion from `number`

When a host JavaScript `number` is supplied to an `i64`, `u64`, or `bigint` parameter via bridge adapters, the host number MUST satisfy `Number.isSafeInteger(val)` (residing between $-(2^{53}-1)$ and $2^{53}-1$). Values outside this safe range MUST be rejected with a boundary panic.

### 3.3 Array and Collection Boundaries

1. **Copying Semantics**: Passing arrays (`[]T`) across the boundary copies elements into detached collections in both directions. JavaScript code CANNOT mutate Ril array memory via aliases, and Ril cannot observe ongoing JavaScript mutations.
2. **Numeric TypedArray Adapters**:
   Explicit boundary conversions map between Ril numeric arrays and JavaScript TypedArray instances, copying elements into detached storage while enforcing identical scalar checks:

| Ril Array Type | JavaScript TypedArray Equivalent | Notes |
| :--- | :--- | :--- |
| `[]i8` | `Int8Array` | Elements validated in $[-128, 127]$ |
| `[]u8` | `Uint8Array` | Elements validated in $[0, 255]$ |
| `[]i16` | `Int16Array` | Elements validated in $[-32768, 32767]$ |
| `[]u16` | `Uint16Array` | Elements validated in $[0, 65535]$ |
| `[]i32` / `[]int` | `Int32Array` | Elements validated in $[-2^{31}, 2^{31}-1]$ |
| `[]u32` | `Uint32Array` | Elements validated in $[0, 2^{32}-1]$ |
| `[]i64` | `BigInt64Array` | Elements mapped to 64-bit signed BigInt |
| `[]u64` | `BigUint64Array` | Elements mapped to 64-bit unsigned BigInt |
| `[]f32` | `Float32Array` | Elements mapped to IEEE 754 binary32 |
| `[]f64` | `Float64Array` | Elements mapped to IEEE 754 binary64 |

`bigint` has no fixed-width TypedArray mapping and copies as arrays of BigInt.

---

## 4. Asynchronous Promise Mapping (`@Async`)

When exporting or calling asynchronous functions across host boundaries:
1. **Exported Async Functions**: A Ril function declared with the `@Async` effect that returns static type `T` exports to JavaScript as a function returning a native `Promise<T>`.
2. **Synchronous Functions**: Functions without `@Async` return `T` directly as synchronous values.
3. **Promise Rejections**: A host Promise rejection or thrown JavaScript exception triggers a runtime panic in the Ril abstract machine, unless the `.ril.ts` boundary adapter explicitly catches and maps the rejection to a declared `Result<T, E>`.
