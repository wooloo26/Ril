# 01. Conformance and System Architecture

This chapter defines the scope, foundational execution model, target platform requirements, and runtime failure contracts of the Ril programming language.

---

## 1. Scope and Target Platforms

A conforming Ril implementation SHALL compile source text into executable machine code targeting native platforms:

- **Native Binaries**: Executable machine instructions (or object files linked into native executables via LLVM, Cranelift, C, or native machine instructions) interacting directly with native operating system environments.

### 1.1 Semantic Determinism Invariant

A fundamental design invariant of Ril is **strict semantic determinism**:
- Any valid Ril program MUST produce strictly deterministic observable output, bit-level numeric calculations, floating-point IEEE 754 representations, and control flows.
- A compiler MUST NOT introduce target-dependent or environment-dependent conditional divergence in language primitives, integer widths, wrapping behavior, string indexing, or error propagation.

---

## 2. Abstract Machine and Execution Model

The Ril abstract machine operates as an expression-oriented reduction system over a heap-allocated store and a frame-based call stack.

### 2.1 Value vs. Store Locations

1. **Value Types**: Primitive booleans (`bool`), fixed-width integers (`i8`..`i64`, `u8`..`u64`), arbitrary-precision integers (`bigint`), IEEE 754 floating-point numbers (`f32`, `f64`), unit (`()`), and immutable UTF-8 strings (`str`) and byte buffers (`bytes`) SHALL be passed and copied by value. An implementation MAY share backing memory internally for immutable `str` or `bytes` via copy-on-write or slice descriptors, provided that no mutation is observable.
2. **Reference Types**: Compound data structures—tuples, records, arrays (`[]T`), maps (`Map<K, V>`), sets (`Set<T>`), sum type variants, and closures—SHALL be allocated within the managed heap. Variables storing compound structures SHALL hold managed references.
3. **Garbage Collection**: Reclamation of unreferenced heap objects SHALL be automatic and managed by garbage collection (GC). Conforming Ril programs SHALL NOT contain explicit memory deallocation primitives or manual lifetime annotations.

### 2.2 Program Entry Point

A standalone Ril executable program begins execution at the root function `pub fn main`:

```ebnf
EntryPoint ::= "pub" "fn" "main" "(" [ Identifier ":" "[]" "str" [ "=" "[" "]" ] ] ")" [ "->" TypeExpression ] { ContractArgument } Block
```

1. The entry point MUST be declared as `pub fn main`.
2. It MAY accept an optional command-line argument parameter of type `[]str` (conventionally named `args`).
3. If a return type is specified, it MUST be `()` or `Result<(), str>`.
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
│ • Mutability laundering (E0520)   │ • Numeric downcast out-of-range    │
│ • Mut-mut / read-mut (E0523/E0524)│ • Array / string index out of bounds│
│ • Unused mut / Redundant mut      │ • Assertion failure (`assert(...)`)│
│ • Missing capability (E0510, @E)  │ • Explicit `panic(message)`        │
│ • Unused fallible Result          │ • Map compound assign on missing key│
│ • Scoped handle escape (E0720-722)│                                    │
└───────────────────────────────────┴────────────────────────────────────┘
```

### 3.1 Compile-Time Rejection (Static Errors)

A conforming compiler MUST reject any translation unit containing static errors during compilation and MUST NOT emit executable artifacts. Compile-time rejections are deterministic and independent of execution environment or optimization level.

### 3.2 Deterministic Runtime Panics

When a runtime operation encounters an irrecoverable invariant violation, the abstract machine raises a **runtime panic**:

1. **Panic Mechanics**: A panic SHALL immediately halt normal sequential execution in the current evaluation frame and SHALL initiate deterministic stack unwinding.
2. **Signature Purity (No `@Panic` Effect)**: Runtime panics are not algebraic effects and SHALL be strictly excluded from function signatures. A conforming compiler MUST NOT require or accept `@Panic` effect annotations on callable items (`InvalidEffectAnnotationError`).
3. **Absence of Synchronous Catching**: A conforming runtime SHALL NOT provide any mechanism to intercept, catch, or suppress panics within a synchronous evaluation frame.
4. **Deterministic Unwinding**: During unwinding, all active scoped resource cleanup handlers (`let scoped` / `let scoped mut`) in scopes being exited MUST execute in strict Last-In, First-Out (LIFO) order (reverse declaration order).
5. **Panic Aggregation**: If a panic is raised while executing the cleanup handler of an active scoped resource binding during an ongoing unwinding process, the new panic MUST be captured and attached as a suppressed cause to the primary panic.
6. **Structured Concurrency Isolation**: In concurrent execution, a panic occurring in a child task SHALL be contained at the enclosing structured `nursery` boundary, yielding a `TaskResult::Panicked` resolution on task joins without terminating the supervising process.
7. **Uncaught Panic Behavior**:
   An uncaught panic SHALL terminate the process with a non-zero exit code and MUST emit a diagnostic crash report detailing the panic message and unwinding trace.

---

## 4. Diagnostics and Error Reporting

A conforming compiler SHOULD provide high-fidelity diagnostic reports for all compile-time rejections:
- Exact source coordinate (file path, 1-indexed line number, 1-indexed column number).
- Relevant span markers indicating the erroneous expression or declaration.
- An explanatory diagnostic message identifying the rule violation (e.g., `"cannot assign to immutable binding"`, `"unused fallible Result must be handled or propagated"`).
