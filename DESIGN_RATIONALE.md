# Ril Language Design Rationale and Defensive Principles

> **Status**: Informative / Non-Normative Companion to the Ril Language Specification.  
> **Target Audience**: Language implementors, compiler engineers, runtime architects, and advanced language researchers.  
> **Normative Companion**: For the authoritative, compiler-facing normative rules, consult [`SPECIFICATION.md`](SPECIFICATION.md).

---

## 1. Failure Model & Error Semantics

### 1.1 The Midori Defect vs. Recoverable Error Delineation

A fundamental insight popularized by Joe Duffy's work on the Midori operating system error model—and reinforced by the development of modern systems like Rust and Swift—is the strict separation between two entirely different classes of failure:

1. **Defects (Bugs / Invariant Violations)**: An assumption made by the programmer has failed. Examples include integer division by zero, indexing beyond array bounds, integer overflow on fixed-width types, failure of an internal assertion (`assert`), and explicit assertion of unreachability (`panic()`).
2. **Domain Recoverable Errors (Environmental Failures)**: An anticipated condition in the external world has failed. Examples include a network socket timing out, a configuration file missing from disk, or user input failing to parse as valid JSON.

In many historical languages (such as Java, C++, and Python), these two categories are conflated into a single hierarchical mechanism: exceptions (`throw` / `try` / `catch`). This conflation is an architectural anti-pattern with catastrophic consequences:
- Programmers attempt to "catch" runtime defects (such as `NullPointerException` or `IndexOutOfBoundsException`) midway through a complex operation, leaving heap objects in partially mutated, corrupted, or incoherent states.
- System resources leak or become deadlock-prone because recovery logic cannot safely anticipate every intermediate state of a corrupted frame.

Ril enforces an unbreachable wall between these domains:
- **Domain Recoverable Errors** are represented as values of algebraic sum types (`Result<T, E>` and `Option<T>` / `?T`). They are visible, typed, checked by the compiler, and subject to Anti-Fault Masking rules that prohibit silently ignoring them.
- **Defects** trigger **Deterministic Runtime Panics**. Panics immediately halt normal sequential evaluation, invoke LIFO cleanups for deterministic resource reclamation, and unwind the execution stack.

### 1.2 The Catastrophe of `@Panic` and Java Checked Exceptions

During the early design of Ril, an intuitive proposal arose: *Since Ril features an expressive algebraic effect system (`@Effect`), why not model panics as an effect—e.g., `@Panic`?*

Ril strictly and deliberately rejects this proposal. The justification rests on the lessons of Java's checked exceptions:
- **Pervasive Signature Pollution**: Almost every basic programming construct is theoretically capable of panicking: integer addition `+` (overflow), array access `arr[i]` (out-of-bounds), division `/` (zero divisor), map access, or basic assertions. If panicking were an algebraic effect, virtually **every function in the entire language** would require `@Panic` in its signature.
- **Erosion of Purity**: The distinction between pure functions and effectful functions would collapse. Higher-order functions like `map`, `filter`, and `fold` would either need duplicate variations or complex effect-polymorphic annotations just to account for possible arithmetic defects.
- **Misaligned Incentives**: Faced with signature pollution, developers routinely resort to blanket swallowings (`try { ... } catch (Exception e) {}`), re-introducing fault masking and defeating the purpose of static type checking.

Therefore, **Ril asserts as a foundational invariant that Bug Panics are not algebraic effects**. There is no `@Panic` effect. An algebraic effect handler cannot intercept or resume a panic. Panics represent defects in program logic that must be diagnosed and eliminated, not handled as business logic.

### 1.3 Why Synchronous Frame Catching is Omitted

Ril provides **zero syntax for catching a panic within synchronous evaluation frames** (there is no `catch_panic` or `try/catch` construct).

When a bug occurs in synchronous code (for instance, an array index out of bounds inside an algorithm), the local frame's invariants are broken. Attempting to catch the panic inside the same synchronous thread and continue execution on corrupted data leads to:
1. **Incoherent State**: Structs or records that were halfway through mutation remain in broken intermediate states.
2. **Security Vulnerabilities**: Undetected memory corruptions, infinite loops, and logic bypasses.

The only safe boundary for containing a defect panic is an **isolated concurrent execution domain**. In Ril, this boundary is the structured concurrency `scope`. A worker task forked inside a scope evaluates in isolation; if it panics, the scope catches the panic, unwinds the failed task's `let scoped` resources, cooperative-cancels sibling tasks, and reports `TaskFault::Panicked` to the supervising frame. The supervisor can then restart the subsystem, fail over, or reject the external request with an HTTP 500 status code, without corrupting the supervisor's own memory.

### 1.4 Dual-Track Partial Operations: Assertive vs. Safe Total

Many elementary operations are mathematically *partial functions*—functions that are undefined for certain inputs. For example:
- Indexing: $f(\text{array}, i)$ is undefined when $i \ge \text{len}(\text{array})$.
- Division: $f(a, b)$ is undefined when $b = 0$.
- Numeric downcasting: $f(n)$ is undefined when $n \gt 255$ for `u8`.

Instead of forcing a single awkward compromise across the language, Ril establishes a **Dual-Track Operational Architecture**:

| Track | Syntactic Form | Semantic Assumption | Failure Mode | Use Case |
| :--- | :--- | :--- | :--- | :--- |
| **Assertive Track** | `arr[i]`, `a / b`, `u8(n)` | Caller guarantees preconditions hold ($b \ne 0, i \lt \text{len}$). | Raises immediate Bug Panic upon breach. | Performance-critical inner loops, mathematically proven algorithms. |
| **Safe Total Track** | `arr?[i]`, `a /? b`, `ril/conv::try_u8(n)` | Input validity is uncertain; environmental input. | Evaluates total result into `?T` or `Result<T, E>`. | Boundary input validation, configuration parsing, untrusted payloads. |

This dual-track model satisfies both ergonomics and safety: developers are never forced to unwrap safe optionals when an invariant has already been proven, yet they have first-class syntax (`/?`, `?[]`) to safely inspect uncertain domain values.

### 1.5 Floating-Point and Collection Boundary Pragmatism

1. **Floating-Point Division by Zero**: Under IEEE 754 standards, floating-point division by zero is mathematically well-defined: $1.0 / 0.0 = +\infty$, $-1.0 / 0.0 = -\infty$, and $0.0 / 0.0 = \text{NaN}$. Panicking on floating-point zero division would break scientific computing libraries, graphics engines, and numerical convergence algorithms. Therefore, Ril conforms strictly to IEEE 754: floating-point `/` never panics.
2. **Collection Slicing (`c[start..end]`)**: Unlike single-element indexing `arr[i]` (which expects a specific element to exist and panics if absent), sub-slice extraction represents a sub-window. Clamping slicing bounds to $[0, \text{len}(c)]$ and yielding an empty slice `[]` when $\text{start} \ge \text{end}$ eliminates off-by-one fencepost panics in string parsing and stream buffer processing without masking single-element logic bugs.
3. **Map Key Lookup (`map[k]`)**: A map is conceptually an associative dictionary where absence of a key is a routine domain condition rather than a program bug. Hence, `map[k]` evaluates directly to `?V` (Option), requiring explicit unwrapping via `??` or `?`.

### 1.6 Ergonomics of Zero-Payload Success: Unit Constructor `Ok()` vs. `Ok(())` Noise and Nullary Tag Confusion

In algebraic error systems (`Result<T, E>`), fallible operations performing pure side effects (flushing a stream, committing a transaction, updating a cache) return no domain payload on success, naturally inhabiting `Result<(), E>`.

Historically, languages like Rust treated `Ok` strictly as a unary constructor function (`fn(T) -> Result<T, E>`), forcing developers to construct values via `Ok(())` (the "smiley face" idiom) and match them via `match res { Ok(()) -> ... }`. This syntax introduced severe ergonomic friction:
- **Visual Noise & Ceremony**: Repetitive `Ok(())` tails in thousands of functions, early returns, and match arms.
- **The Semicolon Statement Hazard**: Omitting or appending a trailing semicolon after `Ok(());` in block-expression languages inadvertently discards the value into `()`, triggering confusing type mismatch diagnostics.
- **The Failed Rust RFC 2107 ("Ok-wrapping") Roadblock**: Proposals to implicitly wrap block return values into `Ok(expr)` were rejected because they destroyed explicit, local control flow reasoning (reviewers could not determine if a return statement constructed a fallible `Result` without inspecting the function signature) and created insurmountable ambiguities with nested `Result<Result<T, E>, E>`.

However, attempting to eliminate parentheses entirely by permitting bare `Ok` introduces cognitive and semantic hazards:
1. **Confusion with Pure Nullary Tags (`None`)**: A nullary variant like `None` in `type Option<T> { Some(T), None }` is a pure zero-field tag that never accepts payloads; writing `None()` is a syntax error. Conversely, `Ok` in `Result<T, E>` is a parameterized data constructor. Allowing bare `Ok` masks whether a payload was accidentally omitted and makes parameterized constructors look deceptively like zero-field tags.
2. **First-Class Function Ambiguity in Synthesis Mode**: When `Ok` is passed to higher-order functions (`[1, 2] |> Array::map(Ok)`), bare `Ok` denotes the unapplied constructor function `fn(T) -> Result<T, E>`. Allowing bare `Ok` to also evaluate to a `Result<(), E>` value created expression ambiguity, forcing the compiler to reject `let x = Ok` in unconstrained Synthesis Mode (`E0301`).

Ril resolves this tension through **Constructor-Tuple Equivalence at $n = 0$ (`Ok()`)**:
1. **Outer Parentheses Absorb the Unit Tuple**: Under the equivalence $\text{Variant}(T_1, \dots, T_n) \equiv \text{Variant}((T_1, \dots, T_n))$, supplying zero arguments inside constructor parentheses $C()$ corresponds directly to the 0-element unit product `()`. Outer constructor parentheses absorb the inner unit tuple, producing clean `Ok()` with zero double-parentheses noise.
2. **Strict Boundary between Tags and Constructors**:
   - **Pure Nullary Tags**: Zero-field variants declared without payloads (`None`, `Active`, `Red`) NEVER take parentheses (`None`).
   - **Data Constructors**: Constructors carrying payloads ALWAYS take parentheses: `Some(x)`, `Ok()`, `Ok(x)`, `Ok(a, b)`.
3. **Deterministic Synthesis & First-Class Clarity**:
   - `let x = Ok()` unambiguously synthesizes `Result<(), _>`, requiring no speculative guessing or type annotations.
   - Bare `Ok` is cleanly preserved as the first-class constructor function (`fn(T) -> Result<T, E>`).
4. **Pattern Matching Symmetry**: In pattern matching, `match res { Ok() -> ..., Err(e) -> ... }` mirrors value construction with perfect symmetry. *(See §4.10 for the general treatment across all arities $n \ge 0$).*

### 1.7 Hermetic Scoped Cleanups and Double-Fault Containment

Resource management in modern systems programming faces a classic dilemma: how to guarantee reliable cleanup during unwinding without risking cascade failures.

Ril addresses this through **Hermetic Scoped Cleanups and Double-Fault Escalation**:
1. **The Fallacy of "Pure" Destructors**: In languages with strict purity tracking, requiring cleanup handlers to be mathematically pure (`is_pure`) is unworkable: closing operating system handles, returning database connections to pools, and recording audit entries inherently require side effects and state mutations (`&mut`). Under Ril's Commit-on-Write memory model (§9.3), physical mutations performed by `on_close` remain permanently committed.
2. **Prohibition of Control Transfers and Divergence (`E0616`, `E0617`)**: While state mutations are permitted, algebraic effects (`@Effect`) and infinite loops (`@Div`) are strictly forbidden inside cleanup closures. Permitting unhandled algebraic effects during unwinding would require finding handlers on stack frames that are actively being destroyed or attempting resumption into dismantled activation records. Prohibiting `@Effect` and `@Div` guarantees that unwinding always proceeds deterministically to completion.
3. **Double-Fault Escalation**: If an unhandled panic occurs inside an `on_close` handler while the stack is already unwinding from a prior panic, attempting secondary unwinding would risk infinite recursion and deadlock. Ril enforces strict **Double-Fault Escalation**: inside structured scopes, the child task resolves immediately to `TaskFault::DoubleFaultFatal(DoubleFaultInfo)` carrying dual diagnostic payloads; in unsupervised frames, the process halts immediately to prevent data corruption.

---

## 2. Aliasing, Mutability, and The Law of Exclusivity

### 2.1 Zero-Tolerance Static Rejection of Mutability Laundering

In languages with reference semantics and mutable state, a notorious class of bugs stems from **mutability laundering**: taking a reference that was passed as read-only, and by means of reassignment, pattern matching, closure capture, or container injection, recovering write permissions to the underlying data.

Ril's philosophy for professional developers mandates that **non-mut parameters and read-only handles can never be upgraded to mutable handles under any circumstances**. Rather than relying on dynamic runtime checks, the Ril compiler enforces **Monotonic Degradation**:

$$
\text{Mut} \succ \text{ReadOnly} \succ \text{None}
$$

Permissions can degrade, but never upgrade. The compiler provides a closed static diagnostic closure (`E0520` through `E0531`) covering:
- Assigning read-only to `let mut`, passing read-only handles to `mut` parameters, or mutating through view (`E0520`).
- Destructuring read-only records into `mut` fields (`E0521`).
- Injecting read-only objects into mutable arrays or records (`E0522`).
- Spreading read-only records into mutable variables (`E0525`).
- Mutating a collection while iterating over it in `for` (`E0526`).
- Declaring unused `let mut` bindings or unused `mut` parameters (`E0527`).
- Returning read-only parameter references into caller `let mut` bindings (`E0528`).
- Over-annotating declarations beyond minimal required capabilities (`E0529`).
- Passing types with active capabilities or scoped handles to `clone` or `clone_immut` (`E0530`: neither clonable nor freezable).
- Creating a live view over an immutable binding (`E0531`).

### 2.2 Cross-Argument Disjointness vs. Borrow Checker Complexity

Rust achieves memory safety through affine types and lifetime annotations (`'a`, `'b`), demanding significant cognitive overhead from application developers. Swift enforces safety through the dynamic and static **Law of Exclusivity**.

Ril targets high-level and mid-level application software. It eliminates the cognitive overhead of lifetime annotations while retaining mathematical aliasing safety by enforcing **Cross-Argument Disjointness at Call Sites**:

$$
\forall i \in \mathop{\mathrm{MutArgs}},\quad \forall j \ne i,\quad \mathop{\mathrm{Path}}(a_i) \cap \mathop{\mathrm{Path}}(a_j) = \emptyset
$$

If a function call passes `mut a` and `mut b`, or `mut a` and read-only `b`, the compiler statically inspects the origin root paths. If they alias the same memory location, compilation fails immediately with `E0523` (Mut-Mut Conflict) or `E0524` (Read-Mut Hazard). This delivers aliasing safety without requiring developers to write complex lifetime bounds.

The same checks include external captures of callees and callbacks. A variable's absence from the explicit argument list does not make its storage disjoint from a mutable argument.

### 2.3 Live Views: Heap Observability Without Type-Level Contagion

Ril explicitly distinguishes between immutable bindings (`let`) and live read-only views (`let view`):
- **Immutable Bindings (`let x = expr`)**: Bind an immutable value or standalone object handle. For scalar value types, `let` performs an independent copy; for fresh records or frozen structures, it establishes a detached, read-only binding.
- **Live Views (`let view v = handle`)**: When a developer writes `let view v = handle` against an existing mutable heap reference:
  - The handle `v` itself loses write permission. The developer cannot write `v.field = value` (`E0520`).
  - However, `v` remains an active **Live View** into the underlying GC-managed heap object. If the holder of `mut handle` modifies the object, subsequent reads through `v` dynamically observe the updated values.
  - **Mutable Root Invariant**: A live view can ONLY observe an active mutable root (`let mut` handle or `mut` parameter). Creating a `let view` over an immutable `let` binding is rejected under `E0531: ImmutableTargetViewError`. Because an immutable `let` has no mutations to observe, converting it into a `view` would counterproductively downgrade an unrestricted pure value into a concurrency-confined handle.
  - **Concurrency Isolation**: Because a live view aliases an underlying mutable heap record, passing a live mutable view across a concurrent task boundary is strictly prohibited (`E0601: CrossThreadDataRaceHazardError`).

**Why Ril rejects "View Contagion" (Type-Level Contagion)**:
If creating a view changed the type of `x: User` into `View<User>` or `&User`, then:
1. Every function in the language would need two versions: one accepting `User` and one accepting `View<User>`.
2. Standard collection types (`[]User`) could not store views without wrapper allocation.
3. Ergonomics would degrade severely.

In Ril, a view's static type remains $T$. The immutability constraint is enforced strictly at the **binding and handle level** via the keyword modifier `view`. If an application requires a permanently frozen, mathematically immutable object that is completely immune to concurrent or future mutations and safe to transfer across concurrency boundaries, it calls `clone_immut(x)`, which returns a deeply normalized `Immut<T>`. Conversely, if it requires an independent, mutable duplicate to modify without mutating the original, it calls `clone(x)`.

### 2.4 Named External Retained Sharing

External state and retained sharing are separate dimensions: `&{mut counter}` permits mutation of an external origin, while `&{^mut counter}` additionally discloses establishing another writable access path that survives a call or closure publication boundary. Copying an integer value does not share its variable cell; publishing a closure that mutates that cell can. Merely mutating already-shared state does not introduce a new sharing obligation.

The name identifies shared source storage, not the container receiving it. Origin identities survive aliases and indirect calls. Hiding a private origin behind a callable interface retains both `&closure` and anonymous `&^mut`; the hazard cannot disappear through abstraction. Local discharge checks captured origins and retention destinations as well as explicit arguments, so local arguments cannot disguise retention of global state.

#### 2.4.1 Surviving Write Path Counting vs. Encapsulated Factory Closures

The definition of retained mutable sharing is strictly rooted in the count of persistent, independent surviving write paths ($\ge 2$):
1. **Encapsulated Private Allocation ($1$ Write Path)**: When a factory function constructs a fresh mutable record and exports it solely within an escaping closure, the factory stack frame terminates upon return. No other handle to that storage cell survives anywhere in the program. Because surviving write paths $= 1 < 2$, there is no aliasing conflict. The callable retains `&closure` and the factory declares `&capture` (§7.4), but annotating `&^mut` is statically rejected as excessive (`E0529`).
2. **Dual Escape ($\ge 2$ Write Paths)**: If the factory simultaneously returns both the closure and the object handle, the caller receives multiple independent write paths to the same underlying record. This constitutes retained mutable sharing and mandates `&^mut`.
3. **Storage Origin Invariance under Intermediate Forwarding**: Aliasing an external global or borrowed parameter inside an intermediate local binding (`let mut forwarded = external_origin`) before capturing it does not launder the capability obligation. Ril's escape analysis tracks transitive storage origins rather than local lexical variable names: the identity of `forwarded` resolves directly to `external_origin`. Because `external_origin` survives outside the frame, publishing the closure establishes $\ge 2$ surviving write paths. Omitting `&^mut` or `&{^mut ident}` triggers `E0510`.

### 2.5 Transactional Derivation and Path-Wise Copy-on-Write (`derive`)

#### 2.5.1 The Cost of Manual Functional Updates
In purely functional languages or languages with reference semantics, updating deeply nested records poses a severe ergonomics and performance dilemma:
1. **Full Deep Copying (`clone(x)`)**: Copying an entire object graph to modify one leaf field incurs $O(N)$ allocation overhead, defeating cache locality and overwhelming the memory subsystem.
2. **Manual Field Spreading / Lenses**: Manually reconstructing parent records (`.{ ...base, field: ... }`) is verbose, error-prone, and clutters domain code with boilerplate lenses.
3. **Mutability Laundering Hazard**: Directly handing out mutable references into an immutable data graph violates Monotonic Degradation (§2.1).

Ril resolves this via `derive(base, recipe)`. By synthesizing a local copy-on-write proxy `next`, developers write imperative in-place mutation syntax (`next.path.field = value`), while the compiler and runtime translate path access into path-wise copy-on-write with maximum structural sharing: unmodified subtrees preserve identical pointer addresses with `base`.

#### 2.5.2 Transactional Abort-Safety vs. Software Transactional Memory (STM)
Software Transactional Memory (STM) achieves transaction isolation by maintaining optimistic read/write sets, collision detection, and multi-version undo logs. This incurs severe runtime overhead and requires rollback logic for mutated memory locations.

`derive` delivers zero-cost **Transactional Abort-Safety** without STM or undo logs:
- **Base Invariant**: `base` is permanently immutable; no write instruction ever touches `base`.
- **Ephemeral Draft Proxy**: Mutations inside `recipe` operate on newly allocated path-copied nodes accessible only through `next`.
- **All-or-Nothing Commit Point**: The derived object graph is only committed and frozen into an immutable value upon normal return of `derive`.
- If execution unwinds early—whether via delimited algebraic effect abort (§9.3) or runtime panic (§1.4)—the activation frame of `recipe` is popped. The proxy `next` loses its root, and the partially allocated path nodes are reclaimed by the tracing GC.

#### 2.5.3 Reconciliation with the Commit-on-Write Invariant (§9.3)
Section 9.3 establishes that Ril memory is Commit-on-Write: *physical memory mutations are never rolled back*.

Discarding in-flight proxy nodes does not contradict Commit-on-Write:
1. The physical writes to newly allocated nodes on `next` *did* physically commit to heap memory; they are not reversed or zeroed out by an undo journal. They simply become unrooted and dead when `next` is dropped upon unwinding.
2. Any physical mutations executed on external reachable state (such as appending to an audit log or updating an external mutable variable cell via `&mut`) remain permanently committed.
3. Because `E0607` (`DerivedProxyEscapeError`) statically forbids `next` from escaping or being stored in external containers, partial derivations cannot leak into surviving scopes.

### 2.6 The Three-Tier Mutability Architecture: Orthogonalizing Reassignment and Interior Mutation (`let`, `let mut`, `var`)

#### 2.6.1 The Historical Conflation Trap: Rust vs. Java/Kotlin
In programming language design, two historical paradigms dominated mutable variable declarations, both exhibiting fundamental semantic flaws:
1. **The Rust Conflation Trap (`let mut`)**: Rust merges slot reassignability and interior mutability into a single keyword `mut`. In Rust, declaring `let mut x = ...` simultaneously grants permission to rewrite the storage slot (`x = ...`) and to mutate through references (`&mut x`). While sound under exclusive ownership, it leaves developers unable to express "pinned mutable handles"—variables intended to be mutated in-place whose identity must never be rebound. Furthermore, it creates cognitive friction when interacting with reference types vs. scalar primitives.
2. **The Java/Kotlin Shallow Immutability Trap (`val` / `final`)**: In Java, Kotlin, and Swift, `val` / `final` / `let` only governs variable slot reassignment (`x = ...`). The mutability of the referenced object is entirely detached from the binding, leading to dangerous "shallow immutability" illusions: a developer writes `val list = ArrayList()` assuming immutability, yet can freely mutate elements in place, defeating data-race freedom and deterministic sharing.

#### 2.6.2 Ril's Orthogonal Three-Tier Taxonomy
Ril resolves both traps by establishing an orthogonal, three-tier capability hierarchy:

| Binding Form | Variable Reassignment (`x = ...`) | In-Place Mutation (`x.f = ...`, `x !> ...`) | Semantic Classification | Mental Model |
| :--- | :---: | :---: | :--- | :--- |
| **`let`** | ❌ Rejected (`E0501`) | ❌ Rejected (`E0520`) | Immutable Binding | Constant value, frozen snapshot |
| **`let mut`** | ❌ Rejected (`E0502`) | ✅ Permitted | **Pinned Mutable Handle** | Fixed heap buffer, collection, closure handle |
| **`var`** | ✅ Permitted | ✅ Permitted | **Reassignable Variable** | Loop counter, accumulator, dynamic cursor |

#### 2.6.3 The Empirical Validation: 100% Pinned Handle Alignment
An exhaustive empirical audit of all reference objects, collections, and closures across the Ril specification confirmed a striking design invariant: **100% of reference handles declared `let mut` already behaved strictly as pinned handles**. In industrial codebase practice, developers almost never reassign a heap buffer (`buf = new_buf`) or connection handle; they mutate its contents in place. Declaring `let mut` as a pinned handle aligns static compiler enforcement with real-world developer intent.

#### 2.6.4 Guaranteed Pointer Stability for Live Views (`let view`)
Ril's memory model features Live Views (`let view v = target`, §4.5), which allow live, read-only observation of an active mutable heap root without data races or wrapper boxing.
- If `target` were reassignable (`var target = ...`), writing `target = other_obj` would sever the association, causing `v` to point to a detached, stale heap instance.
- By establishing that `let view` targets MUST be pinned mutable roots (`let mut` handles or borrowed `mut` parameters), the compiler guarantees absolute pointer stability without lifetime annotations or runtime borrow counting.

#### 2.6.5 Static Value Type Rejection (`E0402`) & Parameter Symmetry (`E0403`)
1. **Value Types Reject `let mut` (`E0402`)**: Value types (§3.1) have copy-by-value semantics and possess zero interior mutable fields. A pinned handle that rejects reassignment on a value type (`let mut i = 0`) has zero legal modifying operations, creating a dead-end binding. Ril catches this at the declaration site via `E0402: ValueTypePinnedMutError`, guiding developers to declare mutable scalars as `var count = 0`.
2. **Borrowed Parameter Symmetry**: A function parameter `mut p: T` (§7.2) borrows the caller's storage for in-place mutation. Reassigning `p = new_obj` inside the callee would merely overwrite the local register and mislead callers. Therefore, `mut p` is definitionally a pinned mutable handle, perfectly mirroring local `let mut`. Declaring `var` in function signatures is statically rejected (`E0403`).

---

## 3. Algebraic Effects, Concurrency, and Function Colorlessness

### 3.1 The Red/Blue Function Problem and Effect Handlers

In languages with `async`/`await` (such as JavaScript, Python, C#, and Rust), functions become "colored":
- An `async` function returns `Promise<T>` or `Future<T>`.
- A synchronous function cannot call an `async` function without awaiting or using an executor.
- Higher-order functions like `Array.prototype.map` cannot seamlessly accept `async` closures without generating an array of promises `Promise<U>[]`.

Ril eliminates function coloring through **Algebraic Effects**:
- An asynchronous function has return type $T$ (uncolored), accompanied by an effect annotation `@Concurrent` or `@Fiber`.
- Callers invoke the function with standard call syntax: `let data = fetch(url)`.
- Standard combinators (`map`, `filter`) require no specialized async duplicates. By the **Automatic Effect Forwarding Theorem**, higher-order functions transparently forward whatever effects their closure arguments invoke.

#### 3.1.1 Least-Privilege Effect Annotation: Leaf `@Fiber` vs. Compound `@Async`

`@Async` is formally defined as an effect alias:
$$\text{@Async} \equiv \{\text{Fiber}, \text{Concurrent}\}$$

This bundling provides seamless ergonomics for high-level application workflows that simultaneously perform suspendable I/O and coordinate concurrent child tasks (such as racing, timeouts, and structured fan-out).

However, granting `@Async` to leaf I/O routines (such as low-level socket readers or timer waits) constitutes an authority escalation: a leaf utility function could covertly fork detached background tasks without caller consent. By separating `@Fiber` from `@Concurrent`:
1. **Principle of Least Privilege**: Leaf I/O functions declare strictly `@Fiber`. Holding `@Fiber` allows cooperative suspension (`Fiber::park()`, `Fiber::yield()`) but strictly lacks task-forking authority (`@Concurrent`).
2. **Preservation of Single-Fiber Invariants**: Because a `@Fiber`-only function cannot branch into concurrent tasks, local mutation handles (`&mut`) and live views remain strictly thread-confined and immune to cross-thread data race hazards (`E0601`).

#### 3.1.2 Decoupling Scheduling Quantum from Data Generation (Separation of Fiber and Yield)

In languages such as Python and JavaScript, the `yield` keyword is overloaded to serve two conflicting roles: producing values in generator streams (`yield item`) and yielding execution control to the runtime scheduler.

Ril rejects this conflation:
1. **Eliminating Handler Hijacking**: If scheduling and data emission shared the same effect, an ambient stream consumer `with Yield::emit(...)` could inadvertently capture runtime scheduler time-slicing yields, causing scheduler starvation.
2. **Untyped Scheduler vs. Typed Payload**: `@Fiber` operates at the untyped machine-state level (declared as `yield() -> ()` within `eff Fiber`), merely swapping instruction pointers and CPU register frames. Conversely, value streaming carries domain data of type $T$.
3. **Freestanding Purity**: Streaming functions annotated with `eff Yield<T>` are ordinary algebraic effects. They can be compiled, linked, and executed in freestanding embedded targets without dragging in a fiber runtime or thread scheduler.
4. **Push vs. Pull Semantics**: Under Ril's affine resumption and no-escape invariant (`E0611`), `eff Yield<T>` evaluates as a zero-cost in-situ **push stream**. External pull iterators (`Iterator<T>`) are cleanly constructed via compiler state-machine lowering or dedicated fiber channels without compromising handler encapsulation.

### 3.2 Structured Concurrency Scopes as Defect Containment Domains

Unstructured concurrency (`go func()`, background thread detached spawning, dangling Promises) is the leading source of resource leaks, orphan goroutines, and race conditions.

Ril unifies all concurrent execution under **Structured Concurrency**:

$$
\forall c \in \text{Children}(S), \quad \mathop{\mathrm{Lifetime}}(c) \subseteq \mathop{\mathrm{Lifetime}}(S) \subset \mathop{\mathrm{Lifetime}}(\text{Frame}_{\text{parent}})
$$

A parent scope cannot exit until all child tasks finish. If a child task panics, the scope guarantees that:
1. Sibling tasks are immediately cancelled via delimited Early Abort.
2. All `let scoped` resource handles inside cancelled fibers execute their cleanup handlers in strict LIFO order.
3. No orphan tasks remain executing in the background.

#### 3.2.1 Zero-Cost Structured Concurrency: Intrusive Child-Stack Scopes and the Synchronous Unwind-Barrier

In unstructured runtimes (e.g. Go goroutines or Node.js Promises), task control blocks, synchronization semaphores, and closures must be allocated on the heap because child task lifetimes may arbitrarily outlive the parent call frame.

Under Ril's structured lifetime invariant $\mathop{\mathrm{Lifetime}}(c) \subseteq \mathop{\mathrm{Lifetime}}(S) \subset \mathop{\mathrm{Lifetime}}(\text{Frame}_{\text{parent}})$, metadata never escapes the lexical scope. Ril translates this mathematical guarantee into a **Zero-Heap Fast Path**:
1. **Intrusive Child-Stack Descriptors**: The parent activation record hosts an $O(1)$ `Scope` descriptor containing only an intrusive doubly-linked list head (16–24 bytes). When `s.fork` is invoked, the `TaskNode` tracking block is allocated directly within the child fiber's own stack frame. Dynamic fan-out loops (`for item in items { s.fork(...) }`) scale arbitrarily without requiring dynamic heap allocation.
2. **Synchronous Scope Unwind-Barrier**: If a panic occurs in the parent frame while child fibers are executing concurrently, releasing the parent stack frame immediately would lead to catastrophic stack-use-after-free corruption when child tasks access the parent `Scope` descriptor. Ril enforces a Synchronous Unwind-Barrier: on panic or early abort, the unwinder marks the scope cancelled and pauses at the frame boundary until all children reach a terminal state (`active_count == 0`) and complete their `let scoped` LIFO cleanups. Only then is the parent stack memory reclaimed.
3. **Quiescent Result Rendezvous**: Child return values $T$ are stored in an inline slot within the child's stack frame, remaining valid in a quiescent state until transferred to the parent via `task.join()` or discarded during scope unwinding. Structured concurrency thus achieves zero-cost abstraction without GC overhead.

### 3.3 Concurrency Boundary Safety via Capability Tracking: Direct DRF-SC Without Marker Traits

In mainstream languages such as Rust (`Send`/`Sync`) and Swift (`Sendable`), compilers rely on nominal marker traits or protocols to classify types that can safely cross concurrent boundaries. This necessity arises because their type systems lack first-class capability tracking on individual callables and values, requiring nominal markers to constrain generic parameters and type declarations.

Ril introduces no nominal marker traits, tags, or ad-hoc concurrency classifications. Concurrency safety—specifically Data-Race Freedom under Sequential Consistency (DRF-SC)—is governed directly by structural value semantics and the **Capability Tracking System**:
- **Zero-Capability Invariant for Cross-Boundary Transfer**: Pure values, immutable records, and frozen `Immut<T>` values carry zero mutable capabilities. They are inherently data-race free and can safely cross concurrent task boundaries (`scope.fork`, `Parallel::map`) without wrapper types or marker trait implementations.
- **Direct Static DRF-SC Enforcement**: Concurrency boundaries directly inspect capability requirements. Any closure or captured payload carrying active mutable capabilities (`&mut`, `&^mut`, `&{mut var}`) or live views over mutable roots is rejected at compile time under `E0601: CrossThreadDataRaceHazardError`.
- **First-Class Effect Signatures**: Algebraic effect operations are ordinary callable signatures (`fn(Args) -> Ret @Effects &Capabilities`), tracking in-place mutation (`&mut`) directly where required without imposing artificial restrictions or marker trait requirements.
- **Conceptual Minimality and Orthogonality**: Concurrency safety is an inherent static property derived from capability tracking and value immutability, rather than a nominal trait bolted onto type definitions. Type definitions remain lean, APIs avoid marker trait clutter, and developers reason about thread safety through familiar capability rules.

### 3.4 Effect Confinement at Concurrent Boundaries: Why Algebraic Effects Cannot Cross Tasks

Mainstream effect systems in single-threaded research languages (e.g., Koka, Eff) assume a single continuous execution stack. In a multi-core, systems-level language with structured concurrency like Ril, permitting algebraic effects to cross concurrent task boundaries introduces fundamental hazards:

1. **Destruction of Zero-Cost Stack Scopes**: Ril child fibers execute with stack-allocated `TaskNode` tracking blocks on independent fiber stacks (§9.5.2). If a child fiber could invoke an effect intercepted by a handler on the parent stack, the runtime would require cross-fiber delimited continuations, allocating frame descriptors on the heap and destroying the Zero-Heap Fast Path.
2. **Delimited Early Abort Across Threads**: If an ambient parent handler intercepts an effect from a child task and executes an early abort (returning without `resume`), unwinding the parent stack while the child continues executing would violate the Synchronous Scope Unwind-Barrier. Conversely, attempting to asynchronously cancel the child from the parent handler introduces non-deterministic thread coordination.
3. **Orthogonal Symmetry with DRF-SC**: Just as Boundary Capability Confinement (`E0601`) guarantees that mutable memory handles cannot cross task boundaries to eliminate data races, Concurrent Task Effect Confinement (`E0615`) guarantees that control transfers cannot cross task boundaries to eliminate cross-thread continuation hazards. Child tasks communicate exclusively through structured value channels (`task.join()`, channels), never via synchronous ambient effect invocations.

---

## 4. Syntax Ergonomics and Deliberate Omissions

### 4.1 File-as-Module by Default and Predictable Namespaces

Modern developers spend significant time maintaining redundant boilerplate when languages require explicit module wrappers around every file.

Ril establishes **File-as-Module by Default**:
- Every `.ril` file is automatically an independent compilation unit named after its path stem.
- Items marked `pub` at the file root constitute the module's public interface; unmarked declarations remain strictly private to the file (`E0201`).
- Source files require zero wrapping boilerplate. Local, block-scoped helper imports (`use module::{item}`) allow localized scoping inside functions without global namespace pollution.

### 4.2 First-Class Operation Records vs. Ad-Hoc Typeclasses and Coherence

Languages with implicit typeclass or trait instance resolution (Haskell, Scala, Rust) suffer from:
- **Orphan Rule Restrictions**: Strict limits on where trait implementations may be declared.
- **Coherence Conflicts**: Ambiguity when multiple libraries provide conflicting implementations for the same type.
- **Hidden Execution**: Calling `x < y` can invoke arbitrary complex user code without visual indication at the call site.

Ril intentionally omits implicit typeclass resolution in favor of **Explicit Operation Records**:
```ril
type Order<T> = { compare: fn(T, T) -> Ordering }
let int_order: Order<int> = .{ compare: compare_int }
```
Passing protocols explicitly provides total predictability, eliminates coherence bugs, and keeps the language's semantics completely transparent to developers.

### 4.3 Unified Lexical Scope vs. Dual-Namespace Complexity

Programming languages diverge significantly in how they organize namespaces:
- **TypeScript**: Values and types share names but inhabit dual namespaces (e.g., `class Foo` declares both a value constructor and an instance type; `import type` was introduced specifically to resolve ambiguous compiler emissions).
- **Rust**: Types, values, and macros inhabit distinct namespaces (`struct Foo; fn Foo() {}` can legally coexist in the same module scope), requiring complex path disambiguation rules (`::Foo` as a type vs `Foo()` as a function) and complicated macro expansion hygiene.

Ril rejects dual-namespace complexity in favor of a **Unified Lexical Identifier Namespace**:
- In any lexical scope (module, block, or pattern), an identifier refers unambiguously to exactly one entity: a value, a type, a module, or an effect.
- Declaring a type `type User = ...` and a function `fn User() ...` in the same scope triggers an immediate duplicate declaration error (`E0203: DuplicateDeclarationError`).
- This design provides profound advantages:
  1. **Trivial Tooling and Refactoring**: Renaming an identifier never leaves a "shadow" type or function behind.
  2. **Predictable Import/Export**: `use module::Item` imports the symbol directly without needing `type` modifiers or disambiguators.
  3. **Zero Ambiguity in First-Class Types**: Because types are first-class values in static type computation, treating types and values under a single unified scope is mathematically necessary and syntactically consistent.

### 4.4 Segregation of Static Records `{}` and Dynamic Collections `[...]`

Dynamic script languages (JavaScript, Lua, Python) historically conflated structural records with associative hash maps (`{}` serving as both struct and dictionary). This resulted in well-documented design failures: prototype pollution, lack of arbitrary key types, performance degradation requiring complex engine inline caches, and the eventual re-introduction of separate `Map` types.

Ril establishes strict syntactic and conceptual segregation between compile-time static records and runtime dynamic collections:
1. **Bracket Delimiters Enforce Absolute Clarity**:
   - Curly braces `{}` denote **Compile-Time Structural Records**: fields are identifiers, memory is contiguous with zero-overhead offset lookup, and field access is strictly identifier dot-access `r.field`. Dynamic string indexing (`r["key"]` or `r.("key")`) is strictly prohibited.
   - Brackets `[...]` denote **Runtime Dynamic Collections**: linear arrays `[]T` / `[1, 2, 3]` and associative maps `[K: V]` / `["k": v]` / `[:]`. Keys can be arbitrary hashable types, and map lookup `m[k]` evaluates to `?V` under the totality principle.
   - `Set<T>` integrates seamlessly via `Set.[1, 2, 3]` and contextual `[1, 2, 3]`.
2. **Elimination of Anonymous Open Rows**:
   - Anonymous open rows (`{ id: int, .. }`) created the false illusion of a runtime "rest" dictionary capture while disallowing field access.
   - Ril replaces them with **Named Row Tail Polymorphism (`..R`)** strictly for generic pipeline type preservation (`fn with_ts<R>(r: { ..R }) -> { ts: int, ..R }`), and **Type-Precise Pattern Destructuring (`let .{ id, ..rest } = u`)** where `rest` is a fully typed, accessible static sub-record.
3. **Type-Level Symmetry via Dot Projection (`T.field`, `T.(K)`)**:
   - In conformity with the strict segregation between compile-time records and dynamic collections, Ril prohibits bracket string indexing on record types (`User["id"]`). Record fields are identifiers, not strings.
   - Field types of static records are extracted symmetrically via dot projection (`User.id`).
   - For inferred anonymous record instances, direct value access `typeof expr.field` or parenthesized type projection `(typeof expr).field` maintains complete orthogonality.
   - In mapped schema computations (`[K in keyof T]`), computed key projections use `T.(K)` to unambiguously distinguish evaluated type parameters from literal field names, preserving complete consistency across value and type spaces.
4. **Product Types vs. Generic Container Parameter Extraction**:
   - **Product Types (Records & Tuples)**: Possess statically fixed shapes and physical memory offsets. Member extraction in both value and type space uniformly employs dot syntax (`u.id` / `User.id` for records; `coords.0` / `Coords.0` for tuples).
   - **Generic Containers (Arrays & Maps)**: Are parameterized collections without named internal fields. Inventing magical pseudo-properties (`Arr.elem`, `Map.key`) would erroneously conflate product field offsets with generic type arguments.
   - **Modular Extraction without Prelude Pollution**: Instead of magical dot properties or global prelude bloat, type extraction for collections is cleanly modularized: `ril/array` exports `type Elem<[]T> = T`, while `ril/map` exports `type Key<[K: V]> = K` and `type Value<[K: V]> = V`. Pure type functions can also directly deconstruct collection shapes via compile-time pattern matching (`match M { [K: V] -> type<V> }`).

### 4.5 The Necessity of Nominal Wrappers & Universal Single-Type Packaging

Structural typing provides maximum ergonomics for data-transfer objects (DTOs) and ad-hoc records, but pure structural typing introduces severe vulnerabilities in domain modeling:
1. **Primitive Obsession & ID Conflation**: Without nominal typing, distinct domain identifiers (`UserId`, `OrderId`, `ProductId`) share the same scalar type `int`, allowing disastrous call-site argument swaps that compile silently.
2. **Coincidental Shape Collision**: A 2D point (`Point2D { x, y }`), a direction vector (`Vector2D { x, y }`), and a complex number (`Complex { x, y }`) share identical field definitions. In pure structural systems, an operation expecting a spatial location can erroneously accept a displacement vector or complex number without static diagnostics.

Ril introduces **Nominal Type Wrappers** as zero-cost compile-time domain boundaries:
- **Zero Runtime Overhead**: In native machine code, a nominal wrapper is completely transparent—it occupies the exact same memory layout and registers as its underlying type without wrapper allocation or pointer indirection.
- **Universal Single-Type Packaging (`type Name(TypeExpr)`)**: Rather than inventing pseudo-parameter lists for multi-field wrappers, Ril strictly defines nominal wrappers as packaging a single underlying `TypeExpression`. A multi-field nominal wrapper is simply a wrapper over a structural record: `type Point2D({ x: f64, y: f64 })`, or an anonymous tuple: `type Coord(int, int)` (definitionally equivalent to `type Coord((int, int))` under Constructor-Tuple Equivalence §4.10).
- **Absolute Syntactic Symmetry**:
  - Declaration: `type Name(Type)`
  - Construction: `Name(Value)` (e.g. `UserId(1001)`, `Point2D(.{ x: 1.0, y: 2.0 })`, `Coord(10, 20)`)
  - Unwrapping: `Name(Pattern)` (e.g. `let UserId(raw) = uid`, `let Point2D(.{ x, y }) = pt`, `let Coord(x, y) = c`) or uniform prelude `inner(wrapper)`.

### 4.6 Opaque Types: Module-Bound Zero-Cost Abstraction

While Nominal Type Wrappers (`type W(T)`) require explicit wrapping (`W(v)`) and unwrapping (`inner(w)`) everywhere, certain domain invariants (such as cryptographically validated session tokens, authenticated IDs, or parser state handles) require a different ergonomics profile:

1. **Internal Transparency vs. External Opacity**:
   - Inside the defining module, implementing algorithms need direct, zero-ceremony access to the underlying representation (`str`, `int`, `[]u8`) without writing boilerplate unwrapping at every intermediate arithmetic or indexing step.
   - Outside the module, client code must be strictly prohibited from forging instances or bypassing validation constructors.

2. **Explicit Operation Exposure via Functions and Pipelines**:
   - In alignment with modern pragmatic languages (OCaml, Hack, Go), capabilities and transformations are exposed explicitly via ordinary functions (`pub fn reveal(t: Token) -> str`) and fluent pipeline operators (`token |> reveal()`). This maintains total predictability, eliminates implicit operator leaking, and leaves library authors in complete control of their public API surface.

3. **Zero Runtime Boxing and Preserved Invariant Security**:
   - Unlike structural records that live on the managed GC heap, an `opaque type` over a scalar value type (`int`, `str`, `bool`) remains a zero-overhead scalar in memory. When stored in collections (`[]Token`, `[Token: User]`), it incurs zero heap wrapper allocations.
   - External callers are strictly prohibited from penetrating the boundary via `inner()` or pattern deconstruction (`E0308`), ensuring invariants cannot be breached from client code.

### 4.7 Unit Nominal Types (`type Marker`) as Zero-Sized Domain Witnesses

In type-driven domain modeling, developers frequently require unforgeable compile-time witnesses (typestate markers, capability tokens, authorization witnesses) that carry zero runtime data:
- Prior designs required awkward packaging over unit tuples: `type Marker(())` or single-case enums `type Marker { Marker }`.
- Ril establishes **Unit Nominal Types (`type Marker`)** as first-class citizens. Omitting the parenthesized underlying type expression defines an isolated nominal identity with a 0-byte memory layout (zero-sized type / ZST).
- In accordance with Ril's **Unified Lexical Identifier Namespace** (§4.3), `Marker` serves simultaneously as the type name in type contexts and the canonical zero-sized value in expressions (`let m = Marker`). In pattern matching, `Marker` serves as a nullary variant selector within multi-variant `match` expressions (`match event { Marker -> ... }`).
- **Nominal Isolation**: Nominal markers are strictly distinct from structural `()`. A function returning `Result<Marker, E>` requires `Ok(Marker)` and rejects `Ok()`, preserving complete domain encapsulation and preventing accidental representation leakage.

### 4.8 Prohibition of Vacuous Bindings (`E0309`): Preventing Zero-Variable Destructuring Anti-Patterns

A `let` statement universally signals the introduction of local variable bindings into the enclosing lexical scope. Applying `let` to patterns that introduce **zero variable bindings** represents a severe syntactic and cognitive anti-pattern:
1. **The Variable Naming Cognitive Trap**: In Ril, variables are strictly `snake_case`, while types and constructors are `PascalCase`. If `let Marker = m` were permitted, developers migrating from Python, JavaScript, or Go would naturally misread it as declaring a new local variable named `Marker`. Silently accepting the statement without binding any variable creates immediate downstream confusion when the developer attempts to reference `Marker` as a variable on subsequent lines.
2. **Semantic Nullity of Zero-Field Destructuring**: `type UserId(int)` destructures into `id`, extracting payload data. But `type Marker` has 0 fields and occupies 0 bytes; it carries zero data to extract. Furthermore, matching an irrefutable type performs no runtime check. Thus, `let Marker = m` extracts nothing, checks nothing, and binds nothing—it is pure dead ceremony.
3. **Abuse of Guarded Bindings for Jump Assertions**: Writing `let Ok() = flush_cache() else { return Err("aborted") }` or `let None = opt else { ... }` abuses the destructuring binding mechanism solely as a conditional jump without binding variables.
4. **Universal Static Rejection (`E0309: VacuousBindingError`)**:
   Ril establishes the **Universal Non-Vacuous Binding Invariant**: all `let` statements (both simple `let Pattern = expr` and guarded `let Pattern = expr else { ... }`) MUST bind at least one variable into the enclosing lexical scope, with the sole exception of the explicit wildcard discard pattern `let _ = expr`.
   
   Developers are steered directly toward intention-revealing, idiomatic alternatives:
   - To discard a value explicitly: Wildcard discard `let _ = m`.
   - For error propagation: Postfix `?` (`flush_cache()?`).
   - For error fallback and recovery: The fallback operator `??` (`flush_cache() ?? \err -> ...`).
   - For boolean assertions / branching: The pattern test operator `is` (`if !(flush_cache() is Ok()) { ... }`).
   - For multi-way branching: Explicit `match` expressions.

### 4.9 Compile-Time HKT Metaprogramming vs. Reified Runtime Generics

While languages such as C# opted for runtime reified generics, they deliberately rejected Higher-Kinded Types (HKTs) due to insurmountable runtime complexity: dynamic higher-order unification, unbounded JIT specialization cascades, and GC object layout unpredictability. Conversely, functional systems like Haskell and Scala support HKTs by completely erasing them prior to execution (lowering to dictionary passing or erased pointer references).

Ril reconciles expressive abstraction with systems-grade performance through the **Phase Distinction Invariant** ($\text{Meta} \succ \text{Runtime}$):
1. **First-Class Static HKT Type Functions**: Higher-kinded constructors are fully supported as compile-time pure type functions (`\M: Type -> Type, T -> M<T>`). Kind arity checking (`E0306: KindMismatchError`) is performed entirely by the static type checker, providing complete mathematical abstraction for schema mapping and type transformations.
2. **Deterministic Runtime Lowering**: At runtime, all generic parameters and pure type functions are either statically monomorphized into specialized machine representations or represented via explicit operation records (dictionary passing).
3. **Rejection of Runtime Reified HKTs**: The Ril abstract machine maintains zero dynamic higher-kinded type descriptors or runtime unification engines. This preserves deterministic object layouts, eliminates JIT latency, and ensures that GC headers remain compact and predictable.

### 4.10 Constructor-Tuple Equivalence vs. Function Parameter Isolation

In algebraic languages, developers routinely suffer from visual friction when returning composite values: operations returning fallible pairs or coordinates require repetitive "parenthesis stuttering" `Ok((val, msg))` and `let Ok((val, msg)) = res`. Ril resolves this tension by formalizing **Constructor-Tuple Equivalence**:
$$\text{Variant}(T_1, T_2, \dots, T_n) \equiv \text{Variant}((T_1, T_2, \dots, T_n)) \quad (n \ge 0)$$

#### 1. Why Confining Equivalence to Data Constructors is Sound
Historical attempts to unify tuples with parameter lists suffered severe defects in general-purpose languages:
- **The Swift 2 to 3 Disaster (SE-0029, SE-0110)**: Swift originally unified function parameter lists with tuples (`f(a, b)` $\equiv$ `f((a, b))`). Because this applied across arbitrary overloaded functions, closures, and methods, it caused combinatorial explosions in type checker constraint solving and rampant overload ambiguities. Swift 3 strictly repealed tuple splatting.
- **The Scala 2 Auto-Tupling Trap**: Scala 2 allowed auto-tupling on methods, silently coercing `println(1, 2)` into `println((1, 2))` because `println` accepted `Any`, while `fn wrap[T](x: T)` mistakenly called with 2 arguments silently inferred `T = (A, B)`.

Ril avoids these pitfalls through a fundamental distinction:
- **Ordinary Functions (`fn`) maintain Strict Parameter Isolation**: Named and anonymous functions, methods, and mutating pipelines possess dedicated parameter lists with names, defaults, `mut` roots, and capability annotations. Ordinary functions NEVER auto-tuple. Calling `add(1, 2)` with a tuple `add(pair)` is statically rejected (`E0301`).
- **Data Constructors represent Pure Algebraic Product Packaging**: Sum type variants and nominal wrappers possess unique lexical identities. They are not overloaded methods; they are pure injection functions into tagged sum spaces. Conflating constructor arguments with product tuples introduces zero constraint solving explosion.

#### 2. Deterministic Arity Partitioning across $n \ge 0$
Because Ril strictly possesses **no 1-element tuples `(T,)`** (`(x)` is parenthesized expression grouping, while tuples strictly require $k \ge 2$ elements; `()` represents the unit product), constructor arity partitioning is strictly deterministic:
- **$n = 0$**: Unit payload constructor absorption (`Ok()` for unit `()`). Outer constructor parentheses absorb the 0-element unit tuple `()`. Contrast with pure nullary tags (like `None`), which possess zero payload parameters and strictly prohibit parentheses.
- **$n = 1$**: Single scalar payload, OR whole-tuple binding when passed/matched with a single variable identifier (`Ok(pair)`).
- **$n \ge 2$**: Positional multi-element tuple payload (`Ok(code, msg)`), where outer constructor parentheses absorb inner tuple parentheses.

#### 3. Single-Layer Non-Transitivity & Rigid Type Safety
Equivalence is strictly single-layer at the outermost constructor boundary:
- **Nested Tuples**: `Variant((1, 2), 3)` requires $n = 2$ arguments; recursive auto-flattening (`Variant(1, 2, 3)`) is statically rejected (`E0301`).
- **Rigid Type Variables**: Deconstructing `Ok(a, b)` against an unconstrained generic type parameter $T$ (not statically proven or refined by a GADT equation to be a tuple) is statically rejected (`E0301`). The compiler never speculatively guesses that an unknown type is a tuple.

#### 4. Zero-Cost Memory Inlining Invariant
In Ril's abstract machine and native code generation, Constructor-Tuple Equivalence incurs zero runtime overhead:
- **Payload Inlining in Variants**: A variant `Ok(10, "ready")` does not allocate an independent heap tuple; its tuple elements are inlined directly into contiguous slots in the variant's allocation header (`[GC Header | Tag | Slot 0 | Slot 1]`), guaranteeing single-allocation footprint (32 bytes).
- **Nominal Wrappers**: `type Coord(int, int)` has zero wrapper bytes, compiling to pure compile-time type branding with the exact machine layout and register conventions of `(int, int)`.

### 4.11 Compiler-Enforced Identifier Casing (`E0101`–`E0103`) & Dual Compound Freezing (`E0530`)

#### 1. Why Identifier Casing is Enforced by the Compiler Rather than Deferred to a Linter
In many languages, naming conventions are relegated to optional style linters. In Ril, identifier casing is elevated to a **first-class grammar and AST invariant** (`E0101`–`E0103`) for fundamental semantic reasons:

1. **Deterministic Pattern-Matching Disambiguation**:
   In algebraic pattern matching, a bare identifier in pattern position creates a classic semantic hazard if casing is unconstrained:
   ```ril
   match response {
       Timeout -> handle_timeout(), -- In Ril: 'Timeout' is PascalCase, statically proven a Constructor Pattern
       retry_count -> retry(retry_count), -- In Ril: 'retry_count' is snake_case, statically proven a Variable Binding Pattern
   }
   ```
   In languages that only warn on casing (e.g. Rust), writing `match x { None => ... }` when `none` or a unit struct is out of scope can silently introduce an all-shadowing variable binding pattern. By enforcing `PascalCase` for constructors and `snake_case` for variable bindings at the parser level, Ril eliminates constructor-vs-variable pattern ambiguity with zero backtracking and zero scope speculation.
2. **Strict Scope of `SCREAMING_SNAKE_CASE`**:
   Ril strictly confines `SCREAMING_SNAKE_CASE` to **compile-time constants (`meta let`)** and **top-level immutable constants (`let`)**.
   - Top-level mutable variables (`let mut`) MUST use `snake_case` (e.g., `let mut active_workers = 0`, `let mut session_data = 0`).
   - *Rationale*: All-caps signifies a permanent, compile-time or freeze-time invariant value. Allowing mutable variables to be all-caps would create a misleading visual signal of immutability. Requiring `snake_case` for all mutable variables (`let mut`) unifies local and global mutable state under the exact same semantic and visual rules.
3. **Acronym Title-Casing Regularization (`E0102`)**:
   Acronyms embedded in `PascalCase` must be title-cased (`HttpServer`, `UserId`, `JsonParser`, rejecting `HTTPServer`, `UserID`, `JSONParser`). This guarantees unambiguous CamelHump word boundary segmentation (e.g., distinguishing `HttpServer` from `HttpsServer` without arbitrary lookahead).
4. **Cross-Platform Path Invariance**:
   Module paths in `use` statements are strictly `snake_case` / lowercase (`use ril/concurrent::{Scope}`). This prevents silent file-resolution discrepancies between case-insensitive file systems (Windows, macOS APFS default) and case-sensitive file systems (Linux ext4).

#### 2. The Dual Compound Nature of `clone_immut` (`E0530`)
The standard prelude operation `clone_immut(x)` is a compound semantic primitive performing two simultaneous transitions:
1. **`clone` (Deep Duplication)**: Traverses the object graph and allocates an independent memory duplicate.
2. **`immut` (Deep Freezing)**: Recursively seals all mutable fields and handles into permanently immutable `Immut<T>`.

When an entity carries active capabilities (`&mut`, `&^mut`), stateful closures, or scoped cleanup handles (e.g., `counter_handle`), passing it to `clone_immut` violates **both** dimensions simultaneously:
- **Unclonable**: An active capability represents an exclusive or linear modification permit. Duplicating it would forge unauthorized concurrent access routes.
- **Unfreezable**: Active capabilities and closures are executable effect vectors, not passive data values. They cannot be stripped of their mutating essence into static inert data.

Therefore, `E0530: IllegalCapabilityCloneImmutError` reflects this dual impossibility: the target entity is **neither clonable nor freezable into `Immut<T>`**. Calling either `clone()` or `clone_immut()` on active capabilities is statically rejected.

### 4.12 Flow-Sensitive Type Narrowing: In-Place Refinement vs. Binding Ceremony

#### 1. The Cognitive Friction of Redundant Variable Rebinding
In traditional statically-typed languages lacking flow-sensitive type refinement (such as Rust), inspecting optional or sum-type values requires continuous variable shadowing or dummy identifiers:
```rust
// Rust: Continuous shadowing ceremony
let opt: Option<User> = fetch_user();
let opt = match opt {
    Some(user) => user,
    None => return,
};
```
When an algorithm merely needs to assert that an existing variable satisfies an invariant and continue execution, forcing the developer to invent distinct variable names or shadow bindings clutters the lexical scope and creates unnecessary cognitive friction.

#### 2. Reconciling with the Non-Vacuous Binding Invariant (`E0309`)
Ril establishes the **Universal Non-Vacuous Binding Invariant (`E0309`)**, strictly prohibiting `let` patterns that bind zero variables (such as `let None = opt else { ... }` or `let Ok() = res else { ... }`). A declaration statement exists definitionally to *introduce new bindings* into scope; using `let` with zero variables degrades declaration syntax into an ad-hoc conditional branch.

Flow-sensitive type narrowing completes the architectural symmetry:
- **`match`**: Used for multi-way structural decomposition, introducing new pattern variables per arm.
- **`let ... else`**: Used for linear early-exit extraction, mandating $\ge 1$ new bound variables.
- **Narrowing (`if` / `while`)**: Used for in-place refinement of *existing* identifiers, introducing 0 new variables.

By offloading in-place type refinement to flow typing, developers naturally write `if opt == None { return }` or `if res is Ok { ... }` without ever being tempted to construct vacuous bindings.

#### 3. Soundness via the Three-Tier Mutability Architecture & Latent Capability Tracking
In dynamic or permissive languages (e.g. TypeScript), flow typing is notoriously vulnerable to aliasing bugs: an object property is checked for non-nullness, but an intervening function call mutates the property behind the compiler's back. Kotlin partially mitigates this by prohibiting smart casts on `var` properties, but still faces subtle concurrency and closure capture hazards.

Ril achieves **100% mathematical soundness** without whole-program alias analysis by resting flow typing directly on its Three-Tier Mutability Architecture and State Capability system:
1. **Immutable Handles (`let`)**: Guarantee deep and permanent immutability. Narrowing on `let` is monotonic throughout its dominance region, completely impervious to external function calls or background tasks.
2. **Pinned Mutable Handles (`let mut`)**: Handle pointer addresses and constructor discriminants are permanently pinned (`E0502`). Variant identity cannot change; only mutable fields require invalidation upon direct writes.
3. **Reassignable Variables (`var`)**: Direct assignments immediately invalidate prior refinements (`E0310`).
4. **Transitive Latent Havoc**: If an external function call, higher-order callback (such as `list !> Array::for_each`), or active effect handler transitively holds mutable capability over a `var` binding ($\&\{\text{mut } v\}$), the compiler conservatively Havocs all refinements prefixed by $v$.
5. **Anti-Aliasing Shield (`E0533`)**: If a `var` binding is aliased via a live view (`let view`) or captured in an escaping mutable closure, the compiler statically forbids flow narrowing, requiring developers to freeze the value into an immutable `let` handle before branching.

#### 4. Bounded Complexity: $D_{\max} = 3$ Path Truncation & $K = 3$ Widening Budget
Unchecked path narrowing on recursive structures (e.g. `node.next.0.next.0...`) and deep fixpoint iterations across nested loops can trigger state space explosion, turning type checking into an exponential constraint-satisfaction problem.

Ril bounds this complexity with two hard compiler invariants:
- **Path Depth Bound ($D_{\max} = 3$)**: Paths longer than 3 segments (e.g. `a.b.c.d`) evaluate normally at runtime, but the compiler does not track their refinement in $\Gamma$. Deep structures must be anchored to local `let` bindings.
- **Widening Budget ($K = 3$)**: In loop fixpoint analysis, if a variable's flow type does not converge within 3 iterations, it is forcibly widened to its root declared type $T_{\text{root}}$.

This guarantees that type narrowing operates in strictly linear time $O(1)$ per branch, ensuring instantaneous compiler diagnostics and sub-millisecond IDE responsiveness.

### 4.13 Dual-Tier 'where' Architecture: Interface Abstraction vs. Implementation Encapsulation

Modern statically typed languages with algebraic effects and fine-grained capability systems face an unavoidable ergonomic challenge: **Signature Bloat**. When higher-order functions declare generics, fallible closures, algebraic effects (`@Fiber + Async`), and explicit mutable capability sets (`&{mut log} &closure`), the signature header expands into an unreadable 5-to-10 line wall of annotations.

Ril resolves this tension through the **Dual-Tier 'where' Architecture**, establishing an asymmetric, mathematically stratified division of responsibility between interface-level type abstraction and block-level implementation encapsulation.

#### 1. Why Waist 'where' is Indispensable: Cognitive Reading Flow & Visual Locality
A naive compiler optimization might suggest eliminating waist `where` altogether, forcing all local declarations into a single trailing `where` clause at the bottom of the function's root block. However, this produces a severe cognitive defect: **Disrupted Cognitive Reading Flow**.

Consider an engineer reading a library function:
```ril
pub fn process_stream<T, R, E>(
    stream: []T,
    transform: TransformFn<T, R, E>,
    sink: AuditSink<R>,
) -> Result<[]R, E> @Async &{mut audit_log}
```
Upon reading the parameter list, the reader's immediate question is: *"What concrete signature and capability contract does `TransformFn` enforce?"*
- **Under Tail-Only Where**: If the function body spans 80 lines of imperative data pipeline logic, the definition of `TransformFn` is buried 80 lines below at the bottom of the screen. The reader must scroll all the way to the bottom to discover the contract, and then scroll back up to understand the body logic. This breaks the **Newspaper Principle**.
- **Under Waist Where (`SignatureWhereClause`)**: The concrete contract is located immediately below the signature header and directly above the root block `{`. The reader's gaze flows naturally: Function Identity $\to$ Parameter Roles $\to$ Contract Definitions $\to$ Body Execution. The entire interface contract is verified in a single visual field.

Furthermore, API documentation generators (`docgen`) and language servers (LSP) can extract public signatures and their waist definitions in $O(1)$ header time, without parsing or traversing function execution bodies.

#### 2. The Asymmetric Separation of Concerns
To prevent waist `where` from degrading into the "Buried Body" anti-pattern (where procedural helper functions push the main body dozens of lines down), Ril enforces an **Asymmetric Declaration Partition**:

| Tier | Syntactic Location | Permitted Declarations | Architectural Purpose |
| :--- | :--- | :--- | :--- |
| **Waist (`SignatureWhereClause`)** | Signature $\dots$ `{` | **`type` ONLY** | **Interface Specification**: Decomposing complex callable signatures, effects, and capability sets. |
| **Tail (`BlockWhereClause`)** | End of Block `{ ... }` | **`fn`, `type`, `eff`** | **Implementation Mechanics**: Mutually recursive worker functions, local scratch types, and private delimited control effects. |

Declaring procedural helpers (`fn`) or algebraic effects (`eff`) at the waist is statically rejected (`E0704`). This ensures that executable blocks (`{ ... }`) never appear before the function's primary body block.

#### 3. Resolving the Escapability Paradox: Why Waist Prohibits `eff`
Why can't local algebraic effects (`eff`) be declared in the waist `where` clause alongside types?

Ril enforces the **Strict Local Discharge Invariant (`E0618`)**: any locally declared effect MUST be completely handled within the declaring function via an in-scope handler (`with`). A local effect CANNOT escape into the public `@Effect` annotation because external callers cannot import or name an unexported private effect.

Permitting `eff` at the waist triggers the **Escapability Paradox**:
1. If the effect appears in the outer signature `@MyEffect`, callers cannot name it and the function is statically uncallable.
2. If the effect does NOT appear in the outer signature, it is purely internal implementation mechanism. Placing it at the signature waist falsely advertises private control flow as part of the public interface contract.

Therefore, `SignatureWhereClause` is restricted to `type` aliases (which may freely reference in-scope *ambient* effects, such as `@Io`), while generative local `eff` declarations are strictly confined to the block where they are handled (`BlockWhereClause`).

#### 4. Strict Declarative Partitioning (`E0703` vs `E0702`)
In languages like C++, Rust, or JavaScript, developers can scatter `type` aliases and local function declarations arbitrarily across procedural code. This creates temporal illusions (e.g. wondering whether a type is dynamically bound or lexically hoisted) and complicates dead-code elimination.

Ril enforces **Strict Declarative Partitioning**:
- The sequential statement sequence (`StatementSequence`) contains strictly imperative code (`let`, `var`, `with`, pipelines, control transfer). Interleaving `fn`, `type`, or `eff` is statically rejected (`E0703: IllegalSequentialDeclarationError`).
- Conversely, `where` clauses contain strictly hoisted, side-effect-free declarations. Placing variable bindings (`let`, `var`) in `where` is statically rejected (`E0702: InvalidWhereItemError`).

#### 5. Soundness: Stratified Tarjan SCC & Downward Isolation (`E0705`, `E0706`)
To eliminate cross-tier dependency cycles and phase-ordering deadlocks, Ril's type checker formalizes **Unidirectional Downward Isolation**:
1. **No Downward References (`E0705`)**: Types in `SignatureWhereClause` cannot reference declarations in `BlockWhereClause`.
2. **Signature Reference Confinement (`E0706`)**: Any type alias used in the outer signature MUST reside in `SignatureWhereClause` or module scope, never in `BlockWhereClause`.
3. **Stratified Dependency Graph**: The dependency graph $\mathcal{G} = \mathcal{G}_{\text{waist}} \ \vec{\sqcup}\ \mathcal{G}_{\text{block}}$ contains zero bipartite cross-edges from Waist to Block ($E_{\text{waist} \to \text{block}} = \emptyset$). Tarjan's SCC algorithm runs independently per layer, guaranteeing that the combined graph is a strictly stratified DAG with provably zero cross-tier mutual recursion deadlocks.

### 4.14 Ergonomics and Soundness of Shorthand Projection Accessors: Product Types vs. Dynamic Collections

Modern functional pipelines rely heavily on higher-order combinators (`Array::map`, `Array::filter`, `Array::sort_by`). Writing verbose lambda headers (`\x -> x.field`) for simple, single-path property projections introduces unneeded lexical overhead. Ril resolves this via shorthand projection accessors (`\.field`, `\.0`, `\.field?.subfield`, `\?.field`).

#### 1. The Categorical Product Duality: Records and Tuples
Record types and tuple types are categorical duals under finite product types ($\prod_{i=1}^n T_i$):
- **Records**: Static finite products with string labels ($\pi_{\text{field}}: R \to T$).
- **Tuples**: Static finite products with ordinal positions ($\pi_k: (T_0, \dots, T_{n-1}) \to T_k$).

In Ril's core type system, value extraction for both constructs uniformly employs the dot member operator (`val.field`, `val.0`). Extending `AccessorExpr` from `\.field` to `\.0` guarantees mathematical symmetry across all product projections.

Furthermore, tuple accessors are **statically total morphisms**:
- Tuple arity $n$ is known at compile time.
- Any out-of-bounds access (`\.2` on `(int, str)`) is statically diagnosed and rejected as `E0301`.
- Because evaluation never incurs bounds-check branching, runtime dynamic allocation, or panics, the accessor lowers directly to a zero-cost offset load.

#### 2. Safe Navigation Accessor Chaining (`?.`)
In business domain schemas, optional nesting is pervasive (`?Department`, `?Employee`). In imperative or naive functional styles, extracting a nested property requires verbose null-guarding or chained Option combinators (`\c -> c.dept?.leader?.name`).

By incorporating `?.` into `AccessorExpr`, Ril preserves total function semantics across optional boundaries:
1. If an intermediate receiver evaluates to `None`, navigation short-circuits to `None` without evaluating downstream accessors.
2. The compiler automatically lifts the closure's inferred return type from $T$ to $?T$.
3. When navigating from an already-optional root (`?T`), the leading safe navigation `\?.field` avoids unnecessary unboxing ceremonies.

#### 3. Why Dynamic Collections (Array, Map) are Excluded from Accessor Shorthand
A tempting proposal is extending shorthand accessors to dynamic collections, such as `\[0]` or `\.[0]` for arrays and `\.["key"]` for associative maps. Ril explicitly rejects this design across three architectural dimensions:

1. **Total Projections vs. Partial Operations**:
   - Record fields and tuple indices are infallible, total projections.
   - Array indexing `arr[i]` is a **partial operation**: accessing an empty array panics at runtime. Providing lightweight shorthand for partial operations encourages developers to write crash-prone data pipelines.
   - Map lookups `map[key]` are associative queries that return an `Option<V>`. A syntactic accessor `\.["key"]` obscures the distinction between static schema projection and dynamic runtime table queries.

2. **Segregation of Product Types and Dynamic Collections ( 4.4)**:
   - Ril maintains an absolute partition between compile-time schema shapes (`{}` and `()`) and runtime heap collections (`[]` and `[:]`).
   - Dot projection on collections is statically rejected (`E0301`). Introducing `\.[0]` or `\.0` on arrays would breach this invariant, creating semantic ambiguity over whether an expression denotes a tuple or an array.

3. **Lexical Hygiene & Pattern Matching Disambiguation**:
   - `\[...]` as a prefix clashes directly with lambda pattern matching:
     ```ril
     let match_fn = \[0] -> "singleton zero"   -- Lambda with pattern matching on array literal
     ```
     Allowing `\[0]` as an accessor expression creates parsing lookahead hazards and degrades compiler diagnostic clarity.

4. **Primacy of Higher-Order Combinators**:
   - In idiomatic Ril, collection access is addressed using first-class functions and combinators:
     ```ril
     -- Array: explicit safe indexing or dedicated combinators:
     let first_cols = matrix |> Array::filter_map(\row -> row?[0])
     let heads = matrix |> Array::filter_map(Array::first)

     -- Map: first-class key lookup function:
     let values = configs |> Array::filter_map(Map::get("host"))
     ```
   - Standard library combinators cleanly communicate optionality and failure semantics without compromising grammar or type checker soundness.

### 4.15 Pure Type Functions & Zero-Dialect Schema Metaprogramming

#### 1. Ontological Distinction: Why Type Functions are Not Closures
In historical literature and earlier compiler drafts, compile-time type abstractions (`\T -> type<...>`) were occasionally referred to as "static type closures". In Ril, this terminology was identified as a severe ontological category error:
- **Runtime Closures (`&closure`, `&capture`)**: In Ril's execution model, a closure is a concrete, runtime-allocated entity. It pairs a machine code pointer with a heap- or stack-allocated environment record capturing lexical state. Escaping closures require factory annotations (`&capture`), state capabilities (`&closure`, `&{mut ident}`), and are constrained by handle-level invocation mutability (`let` vs `let mut`).
- **Type Functions ($\text{Type} \to \text{Type}$)**: Type functions are pure compile-time type-level $\lambda$-abstractions in System $F_\omega$. They maintain zero environment records, allocate zero runtime memory, capture zero mutable variables, and are completely erased during monomorphization.
- **Architecture Principle**: Confining "closure" strictly to runtime state-capturing entities and designating compile-time abstractions as **Type Functions** restores theoretical precision and eliminates developer confusion regarding runtime overhead.

#### 2. Axiomatic Purity & The Zero-Annotation Invariant ($\mathbf{Eff} = \emptyset, \mathbf{Cap} = \emptyset$)
Compile-time evaluation operates strictly within the pure symbolic domain:
- **No Physical Hardware or OS Side Effects**: The compilation phase cannot perform network calls, device interactions, or preemptive concurrency. Consequently, algebraic effects are mathematically empty: $\mathbf{Eff}_{\text{meta}} \equiv \emptyset$.
- **No Runtime Mutable Sharing**: Symbolic type substitution manipulates immutable AST representations and constant values, meaning physical memory aliasing and capability tracking are also mathematically empty: $\mathbf{Cap}_{\text{meta}} \equiv \emptyset$.
- **Zero-Annotation Model**: Rather than burdening type signatures with `@Pure` or `&pure` ceremony, Ril formalizes the **Zero-Annotation Invariant**: type functions are implicitly, axiomatically pure. Annotating effects (`@Effect`) or capabilities (`&mut`, `&closure`) on a type function is statically rejected (`E0301`). In return, type function bodies enjoy unrestricted pure functional computation: local immutable bindings (`let`), conditionals (`if`), pattern matching (`match`), invocation of pure `meta fn` functions, collection combinators, and recursion bounded by totality (`halt type`) or step budgets (`E0811`).

#### 3. The Zero-Dialect Principle: Rejecting Secondary Type-Level Dialects
A common trap in language design is addressing compile-time type transformations by inventing an ad-hoc, secondary dialect inside the type system:
- **The TypeScript Anti-Pattern**: Lacking first-class compile-time code execution, TypeScript was forced to invent a complex secondary language on top of its type space: distributive conditional types (`T extends U ? X : Y`), `never`-filtering hacks, key remapping clauses (`as`), and template literal manipulations (`${P}_${K & string}`). This resulted in extreme cognitive overhead ("type gymnastics") and fragile compilation cascades.
- **The Zig Comptime Precedent**: Zig demonstrated that types can be manipulated using standard language code (`comptime`). However, lacking garbage collection and higher-order functional combinators, Zig's comptime struct synthesis requires verbose imperative loops and manual slice buffer copies.
- **Ril's Pure Data-Driven Synthesis**: Ril achieves maximum expressiveness with zero dialect bloat. In expression contexts, `keyof T` reifies directly to an immutable array of strings `[]str`. To construct a mapped schema, Ril reuses the single comprehension form `{ [K in Expr]: TypeExpr }`, where `Expr` is any compile-time pure expression evaluating to `[]str`.
- **Elimination of `as` Remapping**: By deliberately omitting dedicated remapping clauses (such as `as`), Ril preserves syntactic purity. Developers reshape schemas using ordinary pure expressions and helper functions (e.g. `str_strip_prefix(K, prefix)` or dictionary lookups), ensuring that writing type transformations feels identical to writing standard, readable business logic.

#### 4. Canonical Lexicographical Key Ordering and Leibniz Equivalence
In Ril, structural record equality is order-independent (§3.3):
$$\{ \text{id}: \text{int}, \text{name}: \text{str} \} \equiv \{ \text{name}: \text{str}, \text{id}: \text{int} \}$$
If `keyof T` returned fields in source declaration order, two structurally identical types $T_1 \equiv T_2$ would evaluate to different string arrays (`["id", "name"]` vs `["name", "id"]`). Any type function relying on array indexing or folding would then yield $F\langle T_1 \rangle \not\equiv F\langle T_2 \rangle$, violating **Leibniz's Indiscernibility of Identicals**:
$$\forall T_1, T_2. \quad T_1 \equiv T_2 \implies F\langle T_1 \rangle \equiv F\langle T_2 \rangle$$
To preserve soundness, Ril enforces the **Canonical Lexicographical Key Ordering Invariant**: in expression contexts, `keyof T` strictly returns field names sorted in UTF-8 byte order.

#### 5. Zero-Cost Native Lowering (CTFE Pipeline)
During compilation, all higher-order pipelines (`Array::filter`, `Array::map`, `Record::from_fields`) are reduced by the deterministic compile-time evaluator. The resulting record schemas are lower-level lowered into contiguous machine structs with statically fixed offsets, 8-byte alignment, and GC pointer masks. At runtime, machine code executes zero dynamic string comparisons, zero dictionary queries, and retains zero type-level metadata, achieving 100% zero-cost abstraction.



