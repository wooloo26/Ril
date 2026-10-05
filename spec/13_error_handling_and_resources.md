# 13. Error Handling and Resources

This chapter specifies error handling constructs, typed propagation, fault masking prevention, LIFO scoped resource cleanups (`let scoped`), and scoped handle escape analysis.

---

## 1. Core Sum Types: `Option` and `Result`

The standard prelude provides two foundational error-handling sum types:

```ril
type Option<T> { Some(T), None }    -- syntactic shorthand: ?T
type Result<T, E> { Ok(T), Err(E) }
```

### 1.1 Option Shorthand (`?T`)

1. Prefix `?T` represents `Option<T>`.
2. Repeated prefixes represent nested option layers: `??str` is `Option<Option<str>>`. Each layer preserves distinct `Some(None)` versus `None` constructor representations without auto-flattening.

### 1.2 Safe Navigation (`?.` and `?[]`)

1. **Member Navigation (`obj?.field`)**:
   If `obj` evaluates to `Some(record)`, accesses `.field` and wraps in `Some`; if `None`, short-circuits and evaluates to `None`.
2. **Safe Index Navigation (`arr?[index]`)**:
   Safe element lookup returning `Option<T>`, evaluating to `None` on out-of-bounds indices.

### 1.3 Operational Failure Categories and Evaluation Tracks

Failure evaluation is governed by three operational categories:

1. **Deterministic Runtime Panics**:
   - Raised by fixed-width integer overflow, integer division/modulo by zero, out-of-bounds indexing `arr[i]`, assertion failure `assert`, out-of-range downcasts `u8(256)`, or explicit `panic`.
   - **Signature Purity**: Runtime panics SHALL NOT be declared in function signatures. An effect annotation named `Panic` is a compile-time static error (`InvalidEffectAnnotationError`).
   - **Synchronous Frame Isolation**: Runtime panics SHALL NOT be intercepted or caught within synchronous evaluation frames.
   - **Unwinding and Boundary Containment**: Panics initiate stack unwinding with deterministic LIFO execution of active `let scoped` cleanups, and are contained at structured concurrency boundaries (`nursery`), evaluating to `TaskResult::Panicked`.
2. **Domain Recoverable Errors (`Result<T, E>` and `?T`)**:
   - Represented as ordinary sum type values. Discarding or ignoring fallible `Result` expressions is prohibited by compile-time Anti-Fault Masking (§2.4).
3. **Dual-Track Evaluation Rules**:
   - **Assertive Track**: Direct operations (`arr[i]`, `a / b`, `u8(n)`) evaluate directly or raise a runtime panic upon precondition violation.
   - **Safe Total Track**: Total operations (`arr?[i]`, `a /? b`, `ril/conv::try_u8(n)`) evaluate safely to `?T` or `Result<T, E>`.
   - **Inherent Total Primitives**: Map key lookup `map[k]` evaluates to `?V`; collection slicing `c[start..end]` clamps index bounds to `[0, len(c)]` and evaluates to a sub-slice (or `[]` when $start \ge end$ or indices fall outside collection bounds); floating-point division evaluates to `inf` or `NaN` per IEEE 754 without panicking.

---

## 2. Postfix Error Propagation (`?`)

```ril
fn load_config(path: str) -> Result<Config, AppError> {
    let file = open_file(path)?
    let raw = read_content(file)?
    let cfg = parse_config(raw) ? AppError::Parse
    Ok(cfg)
}
```

### 2.1 Unwrapping and Early Return

1. **Result Propagation**:
   - When applied to `expr: Result<T, E>`, if `expr` evaluates to `Ok(v)`, it unwraps to `v`.
   - If `expr` evaluates to `Err(e)`, the operator early-returns from the enclosing function or closure with `Err(mapped_e)`.
   - The enclosing callable's declared return type MUST be a `Result` whose error type can represent `mapped_e`.
2. **Option Propagation**:
   - When applied to `expr: ?T` (or `Option<T>`), if `expr` evaluates to `Some(v)`, it unwraps to `v`.
   - In an enclosing callable returning `?U` (or `Option<U>`), if `expr` evaluates to `None`, the operator immediately early-returns `None`.
   - In an enclosing callable returning `Result<U, E>`, unmapped `?` is statically rejected; callers MUST provide an error mapper or constructor via the Option-to-Result bridge (§2.3).

### 2.2 Same-Line Error Mapping

```ril
let port = text |> parse_number ? \err -> ConfigError.{ field: "port", cause: err }
let data = id |> query_db ? AppError::Database -- variant constructor as mapper
```

- When an expression or constructor immediately follows `?` on the same physical line, it acts as an error mapper.
- **Line-Breaking Rule**: The error mapper MUST appear on the same physical line as `?`. An intervening newline terminates the operator as an unmapped postfix unwrap.

### 2.3 Option-to-Result Bridge

Within a function returning `Result<T, E>`, applying `?` to an `Option` expression `opt: ?T` bridges the absence to an error:

```ril
let user = find_user(id) ? DbError.{ code: 404 }
let lazy = find_user(id) ? \-> DbError.{ code: 404 } -- lazy evaluation
```

- If `opt` evaluates to `Some(val)`, it yields `val`.
- If `opt` evaluates to `None`, it early-returns `Err(error_expr)` from the enclosing function.

### 2.4 Unused Result Enforcement (Anti-Fault Masking)

> **Normative Rule**: Any expression yielding `Result<T, E>` MUST NOT be discarded as an uninspected non-tail expression or via a semicolon. Discarding a fallible `Result` via a wildcard pattern (`let _ = fallible()`) is a **compile-time static error**.

Callers MUST explicitly handle errors via `?` propagation, `match` decomposition, or recovery closures.

---

## 3. Fallback Expressions (`??`)

The right-associative binary operator `??` unwraps fallible or optional values with fallback recovery:

```ebnf
FallbackExpr ::= PipelineExpr [ "??" FallbackExpr ]
```

### 3.1 Option Fallback

Applied to `opt: ?T`, the right-hand operand MAY be a raw fallback expression of type `T` or a supplier:
```ril
let port = config["port"] ?? 8080
```

### 3.2 Result Fallback: Error-Consuming Closure Requirement

> **Normative Rule**: When applied to `res: Result<T, E>`, the right-hand operand **MUST be an error-consuming closure `\err -> ...`** that evaluates to a recovery value of type `T`.

```ril
let res: Result<str, str> = Err("offline")
let bad = res ?? "default"          -- STATIC ERROR: raw value fallback on Result
let ok  = res ?? \_err -> "default" -- VALID: explicit error-consuming closure
```

Supplying a non-closure right-hand operand to a `Result` fallback is a compile-time static error (`InvalidResultFallbackError`).

### 3.3 Prohibition of Control Flow Transfer in `??` (Strict Value Semantics)

> **Normative Rule**: The `??` operator is strictly a value-coalescing expression operator. Embedding control flow transfer expressions (`return`, `break`, `continue`) as the right-hand operand of `??` is a **compile-time static error** (`IllegalControlTransferInFallbackError` [`E0710`]).

```ril
-- Ill-formed (compile-time static error [E0710]):
-- let user = find_user(id) ?? return Err("not found")
-- let count = parse_num(s) ?? return 0

-- Well-formed alternatives:
-- 1. Postfix error propagation:
let user = find_user(id) ? "not found"

-- 2. Structured divergence:
let Some(user) = find_user(id) else {
    Logger::warn("User {id} not found")
    return Err("not found")
}
```

Control flow transfer expressions SHALL NOT appear as operands of `??`.

---

## 4. Scoped Resource Cleanups (`let scoped`)

The `let scoped` declaration binds a managed system resource to a lexical variable while associating its lifetime directly with the enclosing block:

```ebnf
ScopedLetDecl ::= "let" "scoped" Pattern [ ":" TypeExpression ] "=" Expression
```

```ril
fn process_file(path: str) -> Result<(), AppError> {
    let scoped handle = open_file(path)?
    let scoped mut buffer = allocate_buffer(1024)
    
    -- Both resources are deterministically released when the scope exits
    write_data(mut buffer, handle)?
    Ok(())
}
```

### 4.1 LIFO Cleanup Order

Multiple `let scoped` bindings declared in the same lexical block execute their associated cleanup handlers in strict **Last-In, First-Out (LIFO)** reverse order of declaration (in the example above, `buffer` is released before `handle`).

### 4.2 Trigger Conditions

The cleanup handler of an active `let scoped` binding MUST execute upon any exit from its defining lexical block:
- Normal sequential completion of the block;
- Early function return (`return`);
- Early error propagation via `?`;
- Loop control transfers (`break`, `continue`);
- Effect handler early abort without resumption;
- Deterministic runtime panic unwinding.

### 4.3 Syntactic and Lexical Constraints

1. **Mandatory Initializer**: A `let scoped` declaration MUST provide an immediate initializer expression (`= Expression`). Omitting the initializer is a compile-time static error.
2. **Lexical Confinement**: `let scoped` declarations are confined to local blocks, function bodies, and loop iterations. Declaring a scoped binding at the module top level (`pub let scoped` or top-level `let scoped`) is a **compile-time static error**.
3. **Loop Iteration Scoping**: When declared inside a loop body (`while`, `for`, `loop`), the resource binding is scoped to the individual iteration. The cleanup handler executes at the end of each iteration, preventing resource exhaustion across long-running loops.
4. **Mut-Modifier Compatibility**: `let scoped mut` introduces a mutable scoped handle. It adheres strictly to the Definite Mutation Invariant (must undergo at least one reachable write operation).

### 4.4 Panic Aggregation

If a panic is raised inside a resource's cleanup routine during panic unwinding, the runtime captures the secondary panic and attaches it as a suppressed error to the primary panic.

---

## 5. Scoped Handle Checking and Escape Analysis

Ril strictly segregates ordinary GC-managed records from low-level **system resource handles** (e.g., file descriptors, OS sockets, native device handles):

### 5.1 Static Origin Identity
System resource handles carry static origin identities traced from their instantiating primitives.

### 5.2 Locking on Scoped Binding
Once a resource handle is bound via `let scoped` (or `let scoped mut`), the handle and **all aliases/views sharing its origin identity** become **permanently locked to that lexical scope** (`LockedToScope(L)`).

### 5.3 Must-Bind Affine Obligation
> **Normative Rule**: Any expression yielding a system resource handle introduces an **affine obligation**. The consuming code MUST satisfy one of two mutually exclusive obligations:
> 1. **Immediate Scoped Binding**: Bound via `let scoped` in the local lexical frame, transferring lifetime management to the block's deterministic cleanup stack; OR
> 2. **Immediate Caller Transfer**: Evaluated as the function's return expression (e.g., `return expr` or tail expression), transferring the affine obligation to the caller frame.

**Static Rejections**:
- Discarding a resource handle expression as an uninspected non-tail expression (`open_file(p)?` on its own line or followed by a semicolon) is a **compile-time static error**.
- Discarding a resource handle via wildcard pattern (`let _ = open_file(p)?`) is a **compile-time static error**.
- Binding a resource handle to an ordinary unscoped binding (`let h = open_file(p)?`) without returning it is a **compile-time static error** (`UnscopedResourceHandleError` [`E0720`]).

### 5.4 Anti-Retention Sharing Law
> **Normative Rule**: A locked scoped handle CANNOT be retained in memory beyond its defining lexical scope:
1. **Outer Structures**: A locked handle CANNOT be stored into outer-scope records, arrays, maps, or module-level variables.
2. **Retained Mutable Sharing Prohibition (`&^mut` / `&{^mut var}` Conflict)**: Passing a locked handle to any parameter or function that introduces retained mutable sharing (`&^mut`), or retaining a writable alias to a locked external handle through `&{^mut var}`, is a **compile-time static error** (`ScopedHandleRetainedSharingViolation` [`E0721`]). Naming or abstracting the origin does not relax its scope lock.
3. **Clone and Immutability Prohibition**: Passing a scoped handle or any type enclosing a scoped handle to `clone` or `clone_immut` is a **compile-time static error** (`ScopedHandleCloneViolation` [`E0723`]).
4. **Local Views**: Read-only aliases (`let view = scoped_h`) inherit the locked origin identity and expire when the scope exits.

### 5.5 Closure Isolation Law
> **Normative Rule**: Any closure that captures a locked scoped handle (or any projection of it) is strictly confined to that handle's scope:
1. **Prohibition in Escaping Closures (`&capture`)**: A closure capturing a locked scoped handle CANNOT be returned from the function, CANNOT be stored into outer heap data structures, and CANNOT satisfy an escaping closure type (`&capture`). Violations are statically rejected (`EscapingScopedClosureError` [`E0722`]).
2. **Permitted Downward Funargs**: Passing a closure capturing a scoped handle downward as an argument to a synchronous higher-order function that executes within the same lexical scope is fully permitted.

### 5.6 Ordinary Records
Records and structures that do not contain system resource handles follow standard GC rules and MAY escape without restriction.
