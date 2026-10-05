# Ril Language Design Rationale and Defensive Principles

> **Status**: Informative / Non-Normative Companion to the Ril Language Specification.  
> **Target Audience**: Language implementors, compiler engineers, runtime architects, and advanced language researchers.  
> **Normative Companion**: For the authoritative, compiler-facing normative rules, consult [`SPECIFICATION.md`](../SPECIFICATION.md) and [`spec/`](./).

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

The only safe boundary for containing a defect panic is an **isolated concurrent execution domain**. In Ril, this boundary is the structured concurrency `nursery`. A worker task spawned inside a nursery evaluates in isolation; if it panics, the nursery catches the panic, unwinds the failed task's `let scoped` resources, cooperative-cancels sibling tasks, and reports `TaskResult::Panicked` to the supervising frame. The supervisor can then restart the subsystem, fail over, or reject the external request with an HTTP 500 status code, without corrupting the supervisor's own memory.

### 1.4 Dual-Track Partial Operations: Assertive vs. Safe Total

Many elementary operations are mathematically *partial functions*—functions that are undefined for certain inputs. For example:
- Indexing: $f(\text{array}, i)$ is undefined when $i \ge \text{len}(\text{array})$.
- Division: $f(a, b)$ is undefined when $b = 0$.
- Numeric downcasting: $f(n)$ is undefined when $n > 255$ for `u8`.

Instead of forcing a single awkward compromise across the language, Ril establishes a **Dual-Track Operational Architecture**:

| Track | Syntactic Form | Semantic Assumption | Failure Mode | Use Case |
| :--- | :--- | :--- | :--- | :--- |
| **Assertive Track** | `arr[i]`, `a / b`, `u8(n)` | Caller guarantees preconditions hold ($b \ne 0, i < \text{len}$). | Raises immediate Bug Panic upon breach. | Performance-critical inner loops, mathematically proven algorithms. |
| **Safe Total Track** | `arr?[i]`, `a /? b`, `ril/conv::try_u8(n)` | Input validity is uncertain; environmental input. | Evaluates total result into `?T` or `Result<T, E>`. | Boundary input validation, configuration parsing, untrusted payloads. |

This dual-track model satisfies both ergonomics and safety: developers are never forced to unwrap safe optionals when an invariant has already been proven, yet they have first-class syntax (`/?`, `?[]`) to safely inspect uncertain domain values.

### 1.5 Floating-Point and Collection Boundary Pragmatism

1. **Floating-Point Division by Zero**: Under IEEE 754 standards, floating-point division by zero is mathematically well-defined: $1.0 / 0.0 = +\infty$, $-1.0 / 0.0 = -\infty$, and $0.0 / 0.0 = \text{NaN}$. Panicking on floating-point zero division would break scientific computing libraries, graphics engines, and numerical convergence algorithms. Therefore, Ril conforms strictly to IEEE 754: floating-point `/` never panics.
2. **Collection Slicing (`c[start..end]`)**: Unlike single-element indexing `arr[i]` (which expects a specific element to exist and panics if absent), sub-slice extraction represents a sub-window. Clamping slicing bounds to $[0, \text{len}(c)]$ and yielding an empty slice `[]` when $\text{start} \ge \text{end}$ eliminates off-by-one fencepost panics in string parsing and stream buffer processing without masking single-element logic bugs.
3. **Map Key Lookup (`map[k]`)**: A map is conceptually an associative dictionary where absence of a key is a routine domain condition rather than a program bug. Hence, `map[k]` evaluates directly to `?V` (Option), requiring explicit unwrapping via `??` or `?`.

---

## 2. Aliasing, Mutability, and The Law of Exclusivity

### 2.1 Zero-Tolerance Static Rejection of Mutability Laundering

In languages with reference semantics and mutable state, a notorious class of bugs stems from **mutability laundering**: taking a reference that was passed as read-only, and by means of reassignment, pattern matching, closure capture, or container injection, recovering write permissions to the underlying data.

Ril's philosophy for professional developers mandates that **non-mut parameters and read-only handles can never be upgraded to mutable handles under any circumstances**. Rather than relying on dynamic runtime checks, the Ril compiler enforces **Monotonic Degradation**:
$$\text{Mut} \succ \text{ReadOnly} \succ \text{None}$$
Permissions can degrade, but never upgrade. The compiler provides a closed static diagnostic closure (`E0520` through `E0528`) covering:
- Assigning read-only to `let mut` (`E0520`).
- Destructuring read-only records into `mut` fields (`E0521`).
- Injecting read-only objects into mutable arrays or records (`E0522`).
- Spreading read-only records into mutable variables (`E0525`).
- Mutating a collection while iterating over it in `for` (`E0526`).
- Capturing read-only references into mutable closure scopes (`E0527`).
- Returning read-only parameter references into caller `let mut` bindings (`E0528`).

### 2.2 Cross-Argument Disjointness vs. Borrow Checker Complexity

Rust achieves memory safety through affine types and lifetime annotations (`'a`, `'b`), demanding significant cognitive overhead from application developers. Swift enforces safety through the dynamic and static **Law of Exclusivity**.

Ril targets high-level and mid-level application software. It eliminates the cognitive overhead of lifetime annotations while retaining mathematical aliasing safety by enforcing **Cross-Argument Disjointness at Call Sites**:
$$\forall i \in \operatorname{MutArgs},\; \forall j \ne i,\quad \operatorname{Path}(a_i) \cap \operatorname{Path}(a_j) = \emptyset$$

If a function call passes `mut a` and `mut b`, or `mut a` and read-only `b`, the compiler statically inspects the origin root paths. If they alias the same memory location, compilation fails immediately with `E0523` (Mut-Mut Conflict) or `E0524` (Read-Mut Hazard). This delivers aliasing safety without requiring developers to write complex lifetime bounds.

The same checks include external captures of callees and callbacks. A variable's absence from the explicit argument list does not make its storage disjoint from a mutable argument.

### 2.3 Live Views: Heap Observability Without Type-Level Contagion

When developers write `let view = handle` or `let ro = handle`:
- The handle itself loses write permission. The developer cannot write `view.field = value`.
- However, `view` remains a **Live View** into the underlying GC-managed heap object. If the holder of `mut handle` modifies the object, subsequent reads through `view` observe the updated values.

**Why Ril rejects "View Contagion" (Type-Level Contagion)**:
If creating a view changed the type of `x: User` into `View<User>` or `&User`, then:
1. Every function in the language would need two versions: one accepting `User` and one accepting `View<User>`.
2. Standard collection types (`[]User`) could not store views without wrapper allocation.
3. Ergonomics would degrade severely.

In Ril, a view's static type remains $T$. The immutability constraint is enforced strictly at the **binding and handle level**. If an application requires a permanently frozen, mathematically immutable object that is completely immune to concurrent or future mutations, it calls `clone_immut(x)`, which returns a deeply normalized `Immut<T>`. Conversely, if it requires an independent, mutable duplicate to modify without mutating the original, it calls `clone(x)`.

### 2.4 Named External Retained Sharing

External state and retained sharing are separate dimensions: `&{mut counter}` permits mutation of an external origin, while `&{^mut counter}` additionally discloses establishing another writable access path that survives a call or closure publication boundary. Copying an integer value does not share its variable cell; publishing a closure that mutates that cell can. Merely mutating already-shared state does not introduce a new sharing obligation.

The name identifies shared source storage, not the container receiving it. Origin identities survive aliases and indirect calls. Hiding a private origin behind a callable interface retains both `&capture` and anonymous `&^mut`; the hazard cannot disappear through abstraction. Local discharge checks captured origins and retention destinations as well as explicit arguments, so local arguments cannot disguise retention of global state.

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

### 3.2 Structured Concurrency Nurseries as Defect Containment Domains

Unstructured concurrency (`go func()`, background thread detached spawning, dangling Promises) is the leading source of resource leaks, orphan goroutines, and race conditions.

Ril unifies all concurrent execution under **Structured Concurrency**:
$$\forall c \in \text{Children}(N), \quad \operatorname{Lifetime}(c) \subseteq \operatorname{Lifetime}(N) \subset \operatorname{Lifetime}(\text{Frame}_{\text{parent}})$$

A parent nursery cannot exit until all child tasks finish. If a child task panics, the nursery guarantees that:
1. Sibling tasks are immediately cancelled via delimited Early Abort.
2. All `let scoped` resource handles inside cancelled fibers execute their cleanup handlers in strict LIFO order.
3. No orphan tasks remain executing in the background.

### 3.3 Floating-Point Determinism in Multi-Core Reductions

In multi-threaded parallel reductions (`par_reduce`, `par_fold`), worker threads process chunks of data concurrently. However, floating-point addition is non-associative:
$$(a + b) + c \ne a + (b + c)$$

If the tree of reduction depended on dynamic thread scheduling, OS preemption, or core count $P$, running the same parallel computation twice on the same machine could yield slightly different floating-point results. This non-determinism breaks financial simulations, scientific models, and regression test suites.

Ril resolves this by establishing the **Canonical Binary Reduction Tree**:
- Regardless of how many hardware cores $P$ are executing tasks via work-stealing, sub-results are merged strictly according to a canonical binary tree indexed by input slice indices with a fixed leaf grain $G_{\text{canonical}} = 64$.
- The resulting floating-point computation is **bit-for-bit identical** whether executed on 1 core, 64 cores, or sequentially.

---

## 4. Syntax Ergonomics and Deliberate Omissions

### 4.1 Built-in Intrinsics (`assert`, `panic`) vs. Language Keywords

Many languages designate `assert` and `panic` as dedicated language keywords. Ril deliberately treats them as **Prelude Built-in Intrinsics**:
1. **First-Class Syntactic Regularity**: `assert(cond, msg)` and `panic(msg)` follow standard function call syntax, fitting naturally into pipelines (`cond |> assert("failed")`).
2. **Grammar Parsimony**: Keeping keywords to a minimum avoids unnecessary grammar rules in parsers and allows identifiers like `assert` to be used as field names or API endpoints in external record schemas where necessary.

### 4.2 Pure Value Coalescing (`??`) vs. Embedded Control Transfers (`return`)

In early discussions, some suggested allowing control flow transfer expressions inside `??`, such as:
```ril
-- Disallowed in Ril:
let user = find_user(id) ?? return Err("not found")
```
Ril statically prohibits this syntax (`E0710: IllegalControlTransferInFallbackError`).

**Rationale**:
- **Purity of Expression Evaluation**: Binary operators in expressions should compute values. Allowing a binary operand to silently hijack control flow and unwind the function stack creates hidden exit points that degrade code auditability.
- **Redundancy with Dedicated Idioms**: Ril already provides two superior, explicit alternatives:
  1. *Inline early-return error propagation*:
     ```ril
     let user = find_user(id) ? "not found"
     ```
  2. *Structured multi-line block divergence*:
     ```ril
     let Some(user) = find_user(id) else {
         Logger::warn("User not found")
         return Err("not found")
     }
     ```
Restricting `??` to value fallback guarantees that whenever a developer reads `a ?? b`, they are guaranteed that control flow continues to the next statement.

### 4.3 File-as-Module by Default and The Role of Inline Submodules

Modern developers spend significant time maintaining redundant boilerplate when languages require explicit module wrappers around every file.

Ril establishes **File-as-Module by Default**:
- Every `.ril` file is automatically an independent compilation unit.
- Items marked `pub` at the file root are the module's public interface.
- The `module { ... }` construct exists strictly as a secondary namespace tool for grouping private helpers or mocks within a single large file, avoiding module proliferation. Inline submodules are prohibited inside functions to maintain a clean compilation model.

### 4.4 First-Class Operation Records vs. Ad-Hoc Typeclasses and Coherence

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

---

## 5. Proof Theory and Halting Computation

### 5.1 Soundness and Strong Normalization in `halt fn`

To allow compile-time type computation and propositional verification without risking compiler hangs or infinite loops, Ril introduces total halting functions (`halt fn`).

By Theorem 1.1 (**Strong Normalization**) and Theorem 1.2 (**Confluence**), all computations admitted in `halt fn` terminate in finite steps to a unique normal form. Divergence ($\bot$) is unreachable.

### 5.2 Prevention of Girard's and Curry's Paradoxes

In dependently typed languages and type-level programming, admitting unrestricted recursive types or negative recursive constructors allows encoding logical contradictions:
$$\text{Type } T = T \to \bot$$
If evaluated at compile time, such types introduce Girard's or Curry's paradoxes, causing type checking to become undecidable.

Ril's **Negative Occurrence Ban** statically rejects any attempt to eliminate or recurse over negative recursive types during halting computation, guaranteeing the logical consistency of the type computation system.

### 5.3 Zero-Cost Propositional Equality Rewriting

When developers prove that two types or expressions are propositionally equal using `Eq<A, a, b>` and constructor `Refl`:
$$\text{rewrite } p \text{ in } expr$$
The type checker transports the term $expr$ across the equivalence. Because definitional equality is verified statically at compile time, the compiler strips the proof and emits **zero runtime instructions**. Proofs in Ril guarantee correctness without paying any runtime penalty.
