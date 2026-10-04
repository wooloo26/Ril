# 01. Conformance and System Architecture

This chapter defines the scope, foundational execution model, target platform requirements, and runtime failure contracts of the Ril programming language.

---

## 1. Scope and Target Platforms

A conforming Ril implementation compiles source text into executable code targeting at least one of the two standard targets:

1. **Native Binaries**: Executable machine instructions (or object files linked into native executables) interacting directly with native operating system environments.
2. **ECMAScript / JavaScript Modules**: Standard ECMAScript 2020+ modules (`.js` / `.mjs`) accompanied by authoritative TypeScript declaration interfaces (`.d.ts`).

### 1.1 Dual-Target Uniformity Invariant

A fundamental design invariant of Ril is **semantic target equivalence**:
- Any valid Ril program that does not invoke target-specific host declarations (`decl`) MUST produce the exact same observable output, bit-level numeric calculations, floating-point IEEE 754 representations, and control flows on both Native and JavaScript targets.
- A compiler MUST NOT introduce target-dependent conditional divergence in language primitives, integer widths, wrapping behavior, string indexing, or error propagation.

---

## 2. Abstract Machine and Execution Model

The Ril abstract machine operates as an expression-oriented reduction system over a heap-allocated store and a frame-based call stack.

### 2.1 Value vs. Store Locations

1. **Value Types**: Primitive booleans (`bool`), fixed-width integers (`i8`..`i64`, `u8`..`u64`), arbitrary-precision integers (`bigint`), IEEE 754 floating-point numbers (`f32`, `f64`), unit (`()`), and immutable UTF-8 strings (`str`) and byte buffers (`bytes`) are passed and copied by value. An immutable copy of `str` or `bytes` MAY share backing memory internally via copy-on-write or slice descriptors, provided no mutation can be observed.
2. **Reference Types**: Compound data structures—tuples, records, arrays (`[]T`), maps (`Map<K, V>`), sets (`Set<T>`), sum type variants, and closures—are allocated within the managed heap. Variables storing compound structures hold managed references.
3. **Garbage Collection**: Reclaiming unreferenced heap objects is automatic and managed by garbage collection (GC). Programs do not contain explicit memory deallocation or lifetime annotations.

### 2.2 Program Entry Point

A standalone Ril executable program begins execution at the root function `pub fn main`:

```ebnf
EntryPoint ::= "pub" "fn" "main" "(" [ "args" ":" "[]" "str" [ "=" "[" "]" ] ] ")" [ "->" TypeExpression ] { ContractArgument } Block
```

1. The entry point MUST be declared as `pub fn main`.
2. It MAY accept an optional command-line argument vector `args: []str = []`.
3. If a return type is specified, it MUST be `()` or `Result<(), str>` (or a compatible error type).
4. If `main` declares algebraic effects (such as `@Io`), those effects MUST be handled by the default host runtime harness provided by the platform launcher.

---

## 3. Static Rejection vs. Dynamic Panics

The specification strictly segregates program faults into two mutually exclusive tiers:

```
┌────────────────────────────────────────────────────────────────────────┐
│                        Ril Failure Taxonomy                            │
├───────────────────────────────────┬────────────────────────────────────┤
│ Compile-Time Rejection            │ Deterministic Runtime Panic        │
│ (Static Error)                    │ (Runtime Panic)                    │
├───────────────────────────────────┼────────────────────────────────────┤
│ • Syntax / Grammar invalidity     │ • Fixed-width integer overflow     │
│ • Type and universe mismatch      │ • Integer division or modulo by 0  │
│ • Mutability & handle violations  │ • Numeric downcast out-of-range    │
│ • Unused mut / Redundant mut      │ • Array / string index out of bounds│
│ • Missing capability (&^mut, @E)  │ • Assertion failure (`assert`)     │
│ • Unused fallible Result          │ • Explicit `panic(message)`        │
│ • Escaping defer control flow     │ • Map compound assign on missing key│
└───────────────────────────────────┴────────────────────────────────────┘
```

### 3.1 Compile-Time Rejection (Static Errors)

A conforming compiler MUST reject any translation unit containing static errors during compilation and MUST NOT emit executable artifacts. Compile-time rejections are deterministic and independent of execution environment or optimization level.

### 3.2 Deterministic Runtime Panics

When a runtime operation encounters an irrecoverable invariant violation, the abstract machine raises a **runtime panic**:

1. **Panic Mechanics**: A panic immediately halts normal sequential execution in the current evaluation frame and initiates stack unwinding.
2. **Deterministic Unwinding**: During unwinding, all registered `defer` cleanup handlers active in scopes being exited MUST execute in strict Last-In, First-Out (LIFO) order.
3. **Panic Aggregation**: If a panic is raised while executing a `defer` handler during an ongoing unwinding process, the new panic MUST be captured and attached as a suppressed cause to the primary panic.
4. **Host Boundary Behavior**:
   - On **Native targets**, an uncaught panic terminates the process with a non-zero exit code and diagnostic crash report detailing the panic message and unwinding trace.
   - On **JavaScript targets**, an uncaught panic raises a native `Error` exception containing the formatted panic message and stack trace.

---

## 4. Diagnostics and Error Reporting

A conforming compiler SHOULD provide high-fidelity diagnostic reports for all compile-time rejections:
- Exact source coordinate (file path, 1-indexed line number, 1-indexed column number).
- Relevant span markers indicating the erroneous expression or declaration.
- An explanatory diagnostic message identifying the rule violation (e.g., `"cannot assign to immutable binding"`, `"unused fallible Result must be handled or propagated"`).
