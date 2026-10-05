# 05. Memory Model and Storage

This chapter defines Ril's memory model, value versus reference passing semantics, the handle-level read-only invariant, the definite mutation invariant, parameter permissions, aliasing rules, live views versus detached deep copies, nested in-place mutation paths, and copy-on-write deep updates.

---

## 1. Managed Memory Model

Ril execution is governed by an automatic garbage-collected (GC) memory manager. Compilers and runtimes MUST adhere to the following memory guarantees:
1. **Safety and Absence of Dangling Pointers**: There are no manual heap allocation or deallocation primitives. Values with live references are preserved until they become unreachable.
2. **Deterministic Data Layout**: Compound objects (records, arrays, maps, variant payloads) reside in managed heap storage. Memory access is safe from buffer underflows, use-after-free, and wild pointers.

---

## 2. Value Semantics vs. Reference Semantics

Ril strictly categorizes data into two operational categories:

```
┌────────────────────────────────────────────────────────────────────────┐
│                        Data Storage Categories                         │
├───────────────────────────────────┬────────────────────────────────────┤
│ Passed and Copied by Value        │ Managed by Heap Reference          │
├───────────────────────────────────┼────────────────────────────────────┤
│ • Primitives: `bool`, `unit`, `never`│ • Tuples: `(T1, T2)`               │
│ • Integers: `i8`..`i64`, `u8`..`u64`│ • Records and Schemas: `{ ... }`   │
│ • Big integers: `bigint`          │ • Arrays and Slices: `[]T`         │
│ • Floats: `f32`, `f64`            │ • Hash Maps: `Map<K, V>`           │
│ • Strings: `str` (immutable UTF-8)│ • Sets: `Set<T>`                   │
│ • Byte buffers: `bytes` (immutable)│ • Sum type instances and Closures  │
└───────────────────────────────────┴────────────────────────────────────┘
```

1. **Value Semantics**: Reassigning or passing a value type copies its bits. An implementation MAY optimize `str` and `bytes` via shared immutable byte buffers, provided observable immutability is preserved.
2. **Reference Semantics**: Assigning or passing a compound object copies the reference to the heap object. Both bindings refer to the same underlying heap storage.
3. **Nominal Single-Payload Wrappers (`type W(T)`)**: Inherit the storage category of the underlying type `T`: primitive payloads are copied by value; compound payloads reside in managed heap storage.

---

## 3. Handle-Level Read-Only Invariant and Definite Mutation

### 3.1 Handle-Level Read-Only Invariant

A central invariant of Ril's mutability model is the **Handle-Level Read-Only Invariant**:

> **Normative Rule**: Binding a reference object to an immutable identifier (`let x = expr`) or passing it as an unannotated parameter (`x: T`) establishes a **Read-Only Handle** (`Read-Only Alias`), which **strictly strips write capabilities across all reachable paths through that identifier**.

1. **Permission Stripping Through Read-Only Handles**:
   - An immutable binding (`let`) not only prevents reassigning the variable name `x`, but also statically strips all in-place mutation rights across fields, array elements, or map entries through `x` (e.g., `x.field = val`, `x[0] = val`, `x !> Array::push(val)` are compile-time static errors).
   - This restriction governs the *handle's access permissions*, not the physical immutability of the underlying heap allocation. If the underlying heap object is concurrently referenced by a live mutable handle (`let mut`), modifications made through the mutable handle may be observed through the read-only handle (see [§5.1 Live Views](#51-live-views)). To obtain permanent, isolated immutability, an explicit detached immutable copy MUST be created via `clone_immut` (see [§5.2](#52-detached-deep-copies-clone-and-clone_immut)). For an independent mutable copy, `clone` is used.
   - This stripping holds even if the underlying record schema declared mutable fields (`type Point = { mut x: int }`). A field's `mut` modifier grants the *capability* of being mutated, but that capability is active **only when accessed through a mutable handle (`let mut`) or a mutable parameter (`mut`)**.
2. **Prerequisite for In-Place Mutation**:
   In-place modification of any field, array element, or collection entry strictly requires:
   - An explicit `let mut` root binding in the local frame; or
   - An explicit `mut` parameter declaration on the receiving function or closure.

### 3.2 Definite Mutation Invariant

To ensure that mutability annotations reflect genuine operational intent and prevent false alarms in static escape analysis, Ril enforces the **Definite Mutation Invariant**:

> **Normative Rule**: Any variable binding declared with `let mut` or any parameter declared with `mut` MUST undergo at least one syntactically reachable write operation (*Reachable May-Write*) along an executable control-flow path:
> $\exists \pi \in \text{ReachablePaths}(\text{decl}), \quad \text{Write}(\pi, x)$

1. **Valid Mutation Operations**:
   A write operation is recognized if the identifier or any of its nested access paths undergoes:
   - Direct reassignment (`x = expr`);
   - In-place compound or field assignment (`x.field = expr`, `x[i] += 1`);
   - Mutating pipeline operations (`x !> Array::push(item)`);
   - Invocation of a state-capturing callable (`&capture`, `&{mut ...}`) bound to that handle;
   - Being retained or stored into an escaping or mutable data structure where the retained reference preserves active write capabilities under `&^mut`; or
   - Being passed as an argument with `mut` prefix to a `mut` parameter of a callee carrying `&mut` or `&^mut`.
2. **Rejection of Unused Mutability (`UnusedMutError`)**:
   Declaring a binding (`let mut`) or parameter (`mut param: T`) that is never written to along any reachable control-flow path is a compile-time static error (`UnusedMutError`). Redundant mutability annotations are strictly prohibited.
3. **Dead Code Rule**:
   Write operations located exclusively within statically unreachable basic blocks (e.g., following an unconditional `return`, `panic`, or within provably dead branches) do NOT satisfy the Definite Mutation Invariant.

### 3.3 Monotonic Permission Degradation and Anti-Laundering Invariant

Ril enforces the **Monotonic Permission Degradation Axiom**:
$$\text{Mut} \succ \text{ReadOnly} \succ \text{None}$$

1. **Unidirectional Degradation**: Permissions can only degrade monotonically ($\text{Mut} \to \text{ReadOnly}$). Any attempt to upgrade, cast, or coerce a read-only reference back into a mutable location is strictly prohibited.
2. **Compile-Time Anti-Laundering Rejections**:
   - **Direct Assignment / Binding Laundering (`E0520: MutabilityLaunderingError`)**: Binding a read-only parameter, `let` binding, or read-only projection to `let mut`, or assigning it to an existing mutable lvalue (`uninit_mut = ro`), is a compile-time static error.
   - **Destructuring Laundering (`E0521: DestructuringLaunderingError`)**: When pattern-matching or destructuring a read-only reference, declaring nested reference fields as `mut` is a compile-time static error.
   - **Container Injection Laundering (`E0522: ContainerLaunderingError`)**: Storing a read-only reference containing mutable fields into a mutable container (`mut_arr !> push(ro)`) or mutable record field is a compile-time static error. The reference must first be detached into `Immut<T>` via `clone_immut()`.
   - **Shallow Spread Laundering (`E0525: SpreadLaunderingError`)**: Shallow-spreading a read-only record with nested reference fields into a `let mut` root binding is a compile-time static error.
   - **Collection Mutation During Active Iteration (`E0526: CollectionMutationDuringIterationError`)**: In-place mutation of a collection (via `!>` or passing to a `mut` parameter) while that collection is being actively iterated in an enclosing `for` loop is a compile-time static error.
   - **Closure Capture and Invocation Laundering (`E0527: ClosureCaptureLaunderingError`)**: Capturing a read-only reference into a closure declaring mutable environment access (`&{mut ro}`), invoking a state-capturing callable (`&capture`, `&{mut ...}`) through a read-only handle, or passing a read-only reference as a mutable argument (`f(mut ro)` or `ro !> f()`) is a compile-time static error.
   - **Pass-Through Return Laundering (`E0528: ReturnLaunderingError`)**: Binding the return value of a function to `let mut` when that return value originates from a read-only parameter is a compile-time static error.
   - *(Note: Cross-argument borrow conflicts `E0523` and `E0524` are governed by the Law of Exclusivity in §4.2).*

---

## 4. Parameter Permissions and Aliasing

### 4.1 Parameter Permission Modes

Parameters declare their write and sharing permissions explicitly in their signatures:

1. **Shared Read-Only View (`param: T`)**:
   - Default mode. Grants read-only access to the caller's value or reference.
   - The reference is safely shared by default. It MAY be stored into longer-lived heap structures, returned from functions, or captured by closures without annotation, provided the target container does not grant write access to mutable fields of the stored reference (preventing read-only handle laundering).
2. **Borrowed Mutable Location (`mut param: T`)**:
   - Grants in-place write access to the caller's storage location for the duration of the call.
   - **Strict Reference Type Requirement**: The parameter type `T` MUST be a heap-allocated reference type (records, schemas, arrays, maps, tuples, sum type variants). Value types (`bool`, `int`, `i8`..`i64`, `u8`..`u64`, `bigint`, `f32`, `f64`, `str`, `bytes`, `()`, `never`) possess copy-by-value semantics and CANNOT be declared or borrowed as `mut` parameters. Attempting to declare `mut param: ValueType` or passing a value type to a `mut` parameter is a compile-time static error (`ValueTypeMutableBorrowError`).
   - Callers MUST explicitly mark arguments passed to `mut` parameters using `mut` prefix notation (e.g., `f(mut x)`) or the mutating pipeline operator (`x !> f()`).
   - **Prohibition of RValues and Temporaries**: Passing temporary expressions, literals, or rvalues to a `mut` parameter is a **compile-time static error**. Writable arguments MUST be addressable lvalue locations holding mutable reference handles.

### 4.2 Law of Exclusivity and Cross-Argument Disjointness

To guarantee algorithmic predictability and prevent hidden aliasing corruption, Ril enforces the **Law of Exclusivity**:
> **Normative Rule**: Any mutable borrow via `mut` establishes an exclusive write access window. For every argument $a_i$ passed to a `mut` parameter, its storage path MUST be pairwise disjoint from every other argument $a_j$ ($j \ne i$) supplied in that function call (including both other `mut` arguments and shared read-only arguments):
> $$\forall i \in \operatorname{MutArgs}, \ \forall j \in \operatorname{AllArgs} \setminus \{i\}, \quad \operatorname{Path}(a_i) \cap \operatorname{Path}(a_j) = \emptyset$$
> Two paths $p_1, p_2$ overlap ($p_1 \cap p_2 \ne \emptyset$) if and only if one is an access prefix of the other ($p_1 \sqsubseteq p_2 \lor p_2 \sqsubseteq p_1$). Distinct field projections ($x.a$ and $x.b$ where $a \ne b$) satisfy $x.a \cap x.b = \emptyset$. Dynamic collection indices ($arr[i]$ and $arr[j]$) are conservatively treated as overlapping unless provably distinct compile-time constants.

1. **Rejection of Mut-Mut Aliasing (`E0523: MutMutAliasingConflictError`)**:
   Passing identical or overlapping writable lvalue locations to two or more `mut` parameters in the same call expression is a **compile-time static error**:
   ```ril
   fn swap(mut a: Counter, mut b: Counter) &mut { ... }
   let mut c = Counter.{ val: 10 }
   -- swap(mut c, mut c) -- STATIC ERROR [E0523]: Simultaneous mutable borrow conflict on 'c'
   ```
2. **Rejection of Read-Mut Aliasing (`E0524: ReadMutAliasingHazardError`)**:
   Passing overlapping memory locations to both a `mut` parameter and a read-only parameter in the same call is a **compile-time static error**:
   ```ril
   fn merge_into(source: []int, mut target: []int) &mut { ... }
   let mut buf = [1, 2]
   -- merge_into(buf, mut buf) -- STATIC ERROR [E0524]: Read-mut access hazard: 'buf' overlaps with 'mut buf'
   ```
3. **Suspension Invariance**: Active `mut` borrows remain exclusively reserved across asynchronous suspension points (`@Async`).

---

## 5. Live Views vs. Detached Deep Copies

Ril distinguishes between live reference observation and isolated deep copies:

### 5.1 Live Views

Binding a mutable object to an immutable binding (`let x = mutable_obj` or explicit `let view x = mutable_obj`) creates a **live read-only view**:
1. **Handle-Level Mutation Stripping**: The view handle cannot perform mutations (`view.field = 1` is statically rejected).
2. **Deep Field Projection Contagion**: Any nested field access through a live view handle (`view.child.score`) is strictly read-only. Write permissions are stripped across all reachable paths through that handle.
3. **Zero Type-Level Contagion**: Live views do NOT introduce a distinct `view T` type. The static type remains `T`. Functions and signatures are not colored by view qualifiers.
4. **Permitted Live Observation**: A read-only live view observes subsequent mutations performed on the underlying heap object through any coexisting mutable handle. The managed garbage-collected runtime guarantees safety against memory corruption and dangling references.
5. **Anti-Laundering Enforcement**: The view cannot be upgraded to write access (`let mut bad = view` is statically rejected with `E0520`). If a detached, independent copy is required that does not observe subsequent root modifications, an explicit copy must be created via `clone` (for an independent mutable copy) or `clone_immut` (for a permanent, isolated `Immut<T>`).

### 5.2 Detached Deep Copies (`clone` and `clone_immut`)

Ril provides two prelude primitives to construct detached deep copies of an object graph:

```ril
fn clone<T>(value: T) -> T
fn clone_immut<T>(value: T) -> Immut<T>
```

```ebnf
CloneExpr ::= Expression "|>" ( "clone" | "clone_immut" ) | ( "clone" | "clone_immut" ) "(" Expression ")"
```

1. **Mutable Deep Copy (`clone`)**:
   - `clone` recursively traverses all reachable heap objects, constructing a topologically congruent, detached isolated object graph of type `T` while preserving internal sharing and cycles within that graph.
   - Preserves mutable capabilities of mutable fields. The resulting root object MAY be bound to `let mut` or passed to `mut` parameters, and subsequent mutations affect only the cloned subgraph without mutating the original source.
   - Types containing scoped resource handles (`let scoped`) MUST NOT be passed to `clone` (`E0723: ScopedHandleCloneViolation`).

2. **Immutable Deep Copy (`clone_immut`)**:
   - `clone_immut` recursively traverses all reachable heap objects, constructing a topologically congruent, detached isolated object graph deeply normalized to `Immut<T>`.
   - **Permanent Immobility**: Objects created via `clone_immut` are permanently read-only and CANNOT regain write access under any circumstances. They unconditionally satisfy `Shareable` and are safe for cross-thread sharing.
   - **Prohibition on Capabilities**: Types containing resource capabilities, retained mutable sharing, mutable closure captures (`&mut`, `&^mut`, `&capture`, or `&{mut ...}`), or scoped resource handles MUST NOT be passed to `clone_immut`. Passing such types is a compile-time static error (`E0530: IllegalCapabilityCloneImmutError`).

3. **Non-Establishment of Halting or Stability**:
   - Creating a clone does NOT prove termination (`halt`) and does NOT turn an arbitrary data structure into an admissible stable index. Cyclic data remains inadmissible for stable indices even after cloning.

4. **Shallow Spreads vs. Deep Clones**:
   - Record spread syntax (`.{ ...record, field: val }`) creates only a shallow copy of the outer record; nested references remain shared. To isolate the entire graph, an explicit `clone` or `clone_immut` is required.

---

## 6. Nested In-Place Mutation and LValue Paths

Ril guarantees that assignments and mutating operations to nested data structures modify storage directly in place without copying containing containers:

```ebnf
AssignTarget ::= QualifiedName { MemberAccess | TupleIndex | IndexExpr }
```

### 6.1 Assignable Targets (`AssignTarget`)

Any chain of static field accessors (`.field`), positional tuple indexers (`.0`), and dynamic indexers (`[expr]`) rooted at a mutable variable binding (`let mut`) or a mutable parameter (`mut param`) constitutes a valid writable lvalue.

### 6.2 In-Place Semantics Guarantee

Assignments (`=`, `+=`, etc.) and mutating pipelines (`!>`) to nested targets:
- `array[i].score += 10`
- `grid[row][col] = 9`
- `record.nested_list !> Array::push(item)`
- `lookup["key"].status = "active"`

MUST modify the targeted storage location directly in place without duplicating containing records or allocating fresh outer parent arrays.

---

## 7. Copy-on-Write Deep Updates (`produce`)

`produce` executes functional updates over reference data graphs via copy-on-write proxy mechanics:

```ebnf
ProduceCall ::= Expression "|>" "produce" LambdaExpr | "produce" "(" Expression "," LambdaExpr ")"
```

```ril
type Address = { mut city: str }
type User = { name: str, addr: Address }

let u1 = User.{ name: "Alice", addr: Address.{ city: "Shanghai" } }
let u2 = u1 |> produce \mut draft -> {
    draft.addr.city = "Beijing"
}
```

### 7.1 Operational Semantics of `produce`

1. **Draft Generation**: `produce(base, recipe)` provides the mutating closure `recipe` with a mutable draft proxy of `base`.
2. **Copy-on-Write (CoW)**:
   - Only nodes along the path that are actually modified during the execution of `recipe` are shallow-copied on write.
   - Unmodified sibling subtrees and nested fields retain their exact reference identities (`u2.name == u1.name`).
3. **Immutable Output on Return**: When `recipe` completes, the modified root is finalized and returned as a fresh immutable value. The `base` object graph is invariant under the execution of `produce` and retains full structural integrity.

---

## 8. Multithreaded Memory Model and Data-Race Freedom (DRF)

### 8.1 Data-Race-Free Invariant (DRF-SC)

Ril guarantees **Data-Race Freedom (DRF)** by static construction. A well-typed Ril program is statically proven to contain no data races. Observable multithreaded and multicore execution adheres strictly to **Sequential Consistency (SC)**:

> **Normative Rule**: In the absence of data races, execution of a Ril program across concurrent threads, parallel workers, and asynchronous fibers appears as some global interleaving of sequential thread evaluations.

### 8.2 Concurrency Classification: `Shareable` and `Isolated`

All types in Ril adhere to compile-time concurrency classifications governing thread boundaries:

$$
\text{Transferable} = \text{Shareable} \uplus \text{Isolated}
$$

1. **`Shareable` (Concurrent Shared Read / Arbitrary Aliasing)**:
   A type is `Shareable` if concurrent access from multiple threads is safe without runtime data races:
   - All scalar value types (`bool`, integers, floats, `unit`, `never`), `str`, and `bytes` are natively `Shareable`.
   - Records, tuples, and variants composed entirely of non-`mut` fields whose element types are `Shareable` are transitively `Shareable`.
   - Interior synchronization primitives (`Atom<T: Shareable>`, `Mutex<T>`, `RwLock<T>`) are `Shareable`.
   - Any type deeply normalized via `clone_immut` (`Immut<T>`) is `Shareable`.
   - Pure functions (`fn(A) -> B`) whose closures capture only `Shareable` bindings are `Shareable`.
   - Any type containing a `mut` field, dynamic array `[]T`, or mutable map MUST NOT be classified as `Shareable` unless explicitly converted via `clone_immut` to `Immut<T>`.
   - `Shareable` values MAY be freely aliased across threads without invalidating sender aliases.

2. **`Isolated` (Detached Unique Ownership)**:
   A value is `Isolated` if it represents an unaliased object graph with strictly zero external live aliases in the sending thread:
   - Fresh allocations created in pure functions or unshared local scopes without external live borrows satisfy unaliased isolation.
   - Transferring an `Isolated` value across a thread boundary or channel MUST use affine transfer `move(x)`, which statically invalidates the sender's identifier.

3. **Concurrency Container Invariants**:
   - `Atom<T>` strictly requires `T: Shareable`. Constructing an `Atom` over a mutable or non-`Shareable` type is a compile-time static error (`E0601`).
   - `Channel<T>` strictly requires `T: Transferable` (i.e. `T: Shareable` or `T: Isolated`).

### 8.3 Live Views vs. Cross-Thread Escapes

A live read-only view (`let view = mutable_obj`) strips write permissions locally within its lexical frame, but does NOT transform the underlying heap graph into an immutable structure.
- Passing a live view whose underlying type contains `mut` fields to another thread or capturing it in a concurrent closure MUST yield a compile-time static error (`E0601: CrossThreadDataRaceHazardError`).
- Passing data referenced by a live view across a thread boundary SHALL require explicitly detaching the view via `clone_immut(view)` (producing a deeply immutable `Immut<T>`), transferring unique ownership via `move(x)`, or synchronizing access via `Atom` or `Mutex`.

### 8.4 Safe Ownership Transfer and Affine Invalidation (`move(x)`)

An unaliased mutable object graph MAY be transferred across thread boundaries without copying via the `move(x)` intrinsic:
- **Affine Invalidation**: Evaluating `move(x)` statically transitions $x$ to the `Moved` state. Any subsequent read or write of $x$ along any reachable path MUST produce compile-time static error `E0606: UseAfterMoveError`.
- **Branch and Loop Invariants**: Moving a variable inside a conditional branch leaves it in a partially moved state at the join point, prohibiting subsequent access without re-initialization. Moving inside a loop body without re-initialization MUST be statically rejected with `E0606`.
- **Deep Uniqueness Invariant**: Transferring $x$ requires that no live borrows or active live views overlap with $x$'s reachable heap footprint ($\operatorname{ActiveHandles}(\Gamma) \cap \mathcal{F}(x) = \emptyset$). Violation MUST be statically rejected (`E0604: AliasedIsolationTransferError`).

### 8.5 State Capabilities at Concurrency Boundaries

Concurrent task spawns (`spawn`, `fork`) SHALL require tasks to be free of caller-bound mutable state capabilities:
- A callable passed to a concurrent task MUST NOT declare `&mut`, `&^mut`, `&capture`, or `&{mut ...}`. Violation MUST yield compile-time static error `E0602: IllegalStateCapabilityCrossThreadError`.
- Tasks passed to parallel combinators (`par_map`, `par_fold`) or parallel nurseries MUST require zero external mutable capabilities; violations MUST yield `E0605: InvalidParallelCapabilityError`.
- Reading external immutable state via `&{var}` across concurrent boundaries is permitted if and only if `typeof(var)` satisfies `Shareable`. Capturing a non-`Shareable` variable MUST yield `E0603: NonShareableLexicalCaptureError`.

### 8.6 Safe Publication and Memory Ordering

A conforming runtime MUST guarantee safe publication for all heap allocations:
1. All initialization writes to an object graph MUST occur before the reference pointer becomes observable across a thread boundary or channel.
2. Channels, atomics, mutexes, and thread spawns MUST enforce release-acquire semantics across hardware architectures (x86-64, ARM64, RISC-V).
3. Pure immutable graphs and `Immut<T>` MUST NOT incur garbage-collection write barriers during concurrent traversal.
