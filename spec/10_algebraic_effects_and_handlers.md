# 10. Algebraic Effects and Handlers

This chapter specifies the declaration, propagation, handling, and runtime execution semantics of algebraic effects in Ril.

---

## 1. Effect Declarations and Nominal Isolation

An effect declaration introduces a nominal capability consisting of one or more abstract operations:

```ebnf
EffectOpDecl     ::= Identifier ":" FunctionType
EffectOperations ::= EffectOpDecl { "," EffectOpDecl } [ "," ]
EffectDecl       ::= [ "pub" ] "effect" Identifier [ GenericParameters ] "{" EffectOperations "}"
EffectAliasDecl  ::= [ "pub" ] "effect" Identifier "=" "{" [ EffectItems ] "}"
```

```ril
pub effect Config { get: fn(str) -> str }
pub effect Clock { now: fn() -> i64 }
pub effect AppFx = {Config, Clock}
```

### 1.1 Nominal Isolation and Anti-Hijacking Invariant

1. **Fully Qualified Identity**: An effect is identified globally by its fully qualified canonical module path (e.g., `app::services::Config`).
2. **Visibility Scoping**:
   - Effects adhere to module visibility rules (`pub` vs. private).
   - An unexported private effect CANNOT be named, intercepted, or handled outside its defining module or lexical scope. This prevents accidental or malicious effect hijacking by external libraries.

### 1.2 Effect Set Aliases

`effect SetName = { Effect1, Effect2, ... }` defines a named alias for an unordered set of effects. In effect annotations, `@SetName` expands to all constituent effects. Effect aliases MAY reference other effect aliases, but circular definitions are statically prohibited.

---

## 2. Effect Annotations and Purity Invariants

```ebnf
EffectItem     ::= QualifiedName
EffectItems    ::= EffectItem { "," EffectItem } [ "," ]
EffectArgument ::= "@" ( QualifiedName | "{" [ EffectItems ] "}" )
```

1. **Explicit Annotation Requirement on Named Functions**:
   - Named functions (`fn`, both `pub` and private) that directly invoke effect operations MUST explicitly declare those effects in their signatures (`@Effect` or `@{E1, E2}`).
   - An unannotated named function is **strictly pure**: attempting to invoke an algebraic effect within an unannotated `fn` is a compile-time static error.
2. **Closure Inference**:
   Closures automatically infer all algebraic effects invoked within their bodies.
3. **Higher-Order Forwarding**:
   Higher-order functions forward callback effects automatically without manual signature annotations.

---

## 3. Effect Handlers (`with` and `resume`)

The `with` expression installs an algebraic effect handler, intercepting operations within its delimited scope and discharging them from the outer function signature:

```ebnf
HandlerArm  ::= QualifiedName "(" [ PatternList ] ")" "->" Expression
HandlerSpec ::= "{" HandlerArm { "," HandlerArm } [ "," ] "}" | HandlerArm
WithExpr    ::= "with" HandlerSpec
```

```ril
let greeting = {
    with Config::get(key) -> resume("Production")
    fetch_greeting()
}
```

### 3.1 Handler Execution, Typing, and Effect Discharge

1. **Block Scope and Static Type**:
   `with HandlerSpec` is a primary expression evaluating to the unit value `()`. When placed within a block, it establishes the active handler for all subsequent items and expressions in the remainder of that enclosing block. Formally, this is equivalent to delimiting the subsequent block body under the handler.
2. **One-Shot Resumption (`resume`)**:
   - Inside a handler arm for operation `op: fn(A) -> B`, `resume` has static type `fn(B) -> T_block`, where `T_block` is the return type of the enclosing handled block.
   - Resumptions in Ril are **strictly one-shot (affine)**: invoking `resume` multiple times, storing `resume` into heap structures, or allowing `resume` to escape the handler arm is statically prohibited.
3. **Handler Arm Typing Invariants**:
   - Each handler arm expression `e_arm` MUST evaluate to a subtype of the handled block return type: `type(e_arm) <: T_block`.
4. **Early Abort Without Resumption**:
   If a handler arm evaluates to a value without invoking `resume`, the handled block immediately aborts and evaluates directly to that arm's value. Scopes exited by the abort MUST execute the cleanup handlers of all active `scoped` resource bindings in strict LIFO order (reverse order of declaration). Bindings declared syntactically after the aborted operation point were never evaluated and are not executed.
5. **Effect Discharge Theorem (Full Coverage Invariant)**:
   A nominal algebraic effect `Eff` is discharged (eliminated) from the enclosing function's effect signature `@Eff` if and only if **all operations declared by `Eff` are intercepted by the handler**. Partial coverage of operations does NOT discharge the nominal effect from the signature; unintercepted operations remain required.
6. **Control Transfers Within Handler Arms**:
   - `return` and `?` expressions within a handler arm retain their enclosing function or closure targets.
   - `break` and `continue` retain their enclosing lexical loop targets.
   - Panics raised within handler arms trigger standard panic unwinding.
7. **Nested Handlers and Fallthrough**:
   Nested handlers form a dynamic dispatch stack. Inner handlers evaluate first and shadow outer handlers for matching operations; unhandled operations fall through to outer handlers.
8. **Outer Dispatch Within Arms**:
   Operations performed inside a handler arm are dispatched to outer enclosing handlers on the stack, NEVER recursively to the arm itself.

---

## 4. Built-in Effects: `@Async`, `@Div`, and `Fuel`

### 4.1 Asynchronous Execution and Structured Concurrency (`@Fiber`, `@Concurrent`, `@Async`)

Ril models asynchronous computation and concurrency through first-class algebraic effects without dedicated invocation keywords or monadic wrapper types:

1. **Layered Effect Hierarchy**:
   - **`@Fiber` (Low-Level Primitives)**: Declares fiber-level execution control (`yield: fn() -> ()`, `park: fn() -> ()`, `unpark: fn(FiberId) -> ()`, `checkpoint: fn() -> ()`). Handled by runtime schedulers.
   - **`@Concurrent` (High-Level Structured Concurrency)**: Declares structured concurrency operators (`fork`, `join`, `race`, `both`, `sleep`). Handled by nurseries and concurrent blocks.
   - **`@Async`**: A standard effect alias representing `{Fiber, Concurrent}` or general suspendable asynchronous computation.
2. **Ordinary Call Syntax**:
   - Calling an asynchronous function uses standard invocation syntax (`let data = fetch(url)`).
   - Return types are uncolored (e.g., `str` rather than `Promise<str>`).
   - Higher-order functions (e.g., `map`, `filter`) forward asynchronous effects automatically without specialized variants.
3. **Structured Concurrency and the Nursery Invariant**:
   - All concurrent child tasks MUST be spawned within a lexical nursery or structured scope:
     $$\forall c \in \text{Children}(N), \quad \operatorname{Lifetime}(c) \subseteq \operatorname{Lifetime}(N) \subset \operatorname{Lifetime}(\text{Frame}_{\text{parent}})$$
   - The enclosing nursery block MUST NOT exit until all child tasks have resolved (completed, cancelled, or failed).
   - **Lifetime Safety**: Because child task lifetimes are strictly bounded by the nursery, child tasks MAY borrow parent frame variables and observe parent `let scoped` resources provided that borrowed bindings satisfy `Shareable` and carry zero active mutable handles in sibling tasks.
4. **Delimited Early Abort and Cascading Cancellation**:
   - Cancellation is driven by the algebraic effect handler's Early Abort semantics (returning without invoking `resume`).
   - In competitive constructs (`race`, `timeout`), winning branches resume execution while losing branches have their continuations discarded.
   - Discarding a suspended continuation MUST trigger deterministic LIFO cleanup of all `let scoped` bindings in the aborted fiber stack.
5. **Pluggable Schedulers as Handlers**:
   - Runtime schedulers (such as multi-core work-stealing schedulers) and test harnesses (such as deterministic virtual-time mock schedulers) are implemented as ordinary effect handlers intercepting `@Fiber`.
6. **Affine One-Shot Resumption**:
   - Delimited resumptions (`resume`) in Ril are strictly one-shot (affine). Re-invoking an active `resume` or allowing a `resume` continuation to escape its handler arm MUST be rejected at compile time.

### 4.2 Divergence Tracking (`@Div`) and Fuel Masking

The built-in `@Div` effect tracks potential non-termination (loops and general recursion):
1. **Private Inference**: Private functions and closures infer `@Div` automatically from loop constructs and unproven recursion without mandatory annotations.
2. **Public Boundary Enforcement**: At public module boundaries (`pub fn`), a function containing unhandled divergence MUST explicitly declare `@Div`, be proven terminating as a `halt fn`, or be masked via `Fuel`. An unannotated `pub fn` with unhandled divergence is rejected.
3. **Fuel Masking**:
   `with Fuel::limit(steps) -> fallback` handles potential divergence, bounding execution steps and masking the `@Div` effect from the enclosing function's public signature.
