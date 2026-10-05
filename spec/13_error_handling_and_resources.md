# 13. Error Handling and Resources

This chapter specifies error handling constructs, typed propagation, fault masking prevention, LIFO resource cleanups (`defer`), and scoped handle escape analysis.

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

1. When applied to `expr: Result<T, E>`, if `expr` is `Ok(v)`, it unwraps to `v`.
2. If `expr` is `Err(e)`, the operator early-returns from the enclosing function or closure with `Err(mapped_e)`.
3. The enclosing callable's error type MUST be capable of representing the returned error.

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

> **Normative Rule**: Any expression yielding `Result<T, E>` MUST NOT be discarded as an uninspected statement expression. Discarding a fallible `Result` via a wildcard pattern (`let _ = fallible()`) is a **compile-time static error**.

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

> **Normative Rule**: When applied to `res: Result<T, E>`, the right-hand operand **MUST be an error-consuming closure `\err -> ...`** or a diverging control transfer statement (`return`, `panic`, `break`, `continue`).

```ril
let res: Result<str, str> = Err("offline")
let bad = res ?? "default"        -- STATIC ERROR: raw value fallback masks error
let ok  = res ?? \_err -> "default" -- VALID: explicit error acknowledgment
```

Raw value fallbacks on `Result` types are statically rejected to guarantee that error payloads cannot be silently ignored without explicit syntactic acknowledgment.

---

## 4. Resource Cleanup (`defer`)

The `defer` statement schedules a cleanup expression to execute when the enclosing lexical block scope exits:

```ebnf
DeferStmt ::= "defer" Expression
```

```ril
let handle = open_file("data.txt")?
defer close_file(handle)
-- handle is guaranteed to be closed when scope exits
```

### 4.1 LIFO Execution Order

Multiple `defer` statements in the same scope execute in strict **Last-In, First-Out (LIFO)** reverse registration order.

### 4.2 Trigger Conditions

A deferred cleanup MUST execute upon any exit from the enclosing lexical block:
- Normal sequential completion of the block;
- Early function `return`;
- Early error propagation via `?`;
- Loop control transfers (`break`, `continue`);
- Effect handler aborts without resumption;
- Runtime panic unwinding.

### 4.3 Prohibition of Escaping Control Transfers

To preserve transactional cleanup integrity:
- Statements within a `defer` block MUST NOT transfer control outside that `defer` block.
- Using `return`, `?`, or `break`/`continue` targeting an outer loop enclosing the `defer` is a **compile-time static error**.
- Internal loops nested entirely within a `defer` block MAY use `break` and `continue` to manage their internal iterations.

### 4.4 Panic Aggregation

If a panic is raised inside a `defer` expression while unwinding a previous panic, the runtime system captures the secondary panic and attaches it as a suppressed error to the primary panic.

---

## 5. Scoped Handle Checking and Escape Analysis

Ril distinguishes between ordinary GC-managed records and low-level **system resource handles** (e.g., file descriptors, OS sockets):

1. **Origin Identity**: System resource handles carry static origin identities.
2. **Locking on Defer Registration**:
   Once a resource handle is passed to a cleanup function inside a `defer` statement (e.g., `defer close_file(h)`), all aliases of that handle's origin become **locked to the enclosing scope**.
3. **Prohibition of Escape**:
   A locked handle CANNOT be returned from the function, stored into outer records, captured into escaping closures, or passed to `snapshot`. Attempting to escape a locked handle is a compile-time static error.
4. **Ordinary Records**:
   Records that do not contain resource handles follow standard GC rules and MAY escape without restriction.
