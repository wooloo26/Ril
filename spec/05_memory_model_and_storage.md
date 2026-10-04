# 05. Memory Model and Storage

This chapter defines Ril's memory model, value versus reference passing semantics, the handle-level read-only invariant, the definite mutation invariant, parameter permissions, aliasing rules, live views versus detached snapshots, nested in-place mutation paths, and copy-on-write deep updates.

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

---

## 3. Handle-Level Read-Only Invariant and Definite Mutation

### 3.1 Handle-Level Read-Only Invariant

A central invariant of Ril's mutability model is the **Handle-Level Read-Only Invariant**:

> **Normative Rule**: Binding a reference object to an immutable identifier (`let x = expr`) or passing it as an unannotated parameter (`x: T`) establishes a **Read-Only Handle** (`Read-Only Alias`), which **strictly strips write capabilities across all reachable paths through that identifier**.

1. **Permission Stripping Through Read-Only Handles**:
   - An immutable binding (`let`) not only prevents reassigning the variable name `x`, but also statically strips all in-place mutation rights across fields, array elements, or map entries through `x` (e.g., `x.field = val`, `x[0] = val`, `x !> push(val)` are compile-time static errors).
   - This restriction governs the *handle's access permissions*, not the physical immutability of the underlying heap allocation. If the underlying heap object is concurrently referenced by a live mutable handle (`let mut`), modifications made through the mutable handle may be observed through the read-only handle (see [§5.1 Live Views](#51-live-views)). To obtain permanent, isolated immutability, an explicit detached snapshot MUST be created via `snapshot` (see [§5.2](#52-isolated-snapshots-snapshot)).
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
   - Mutating pipeline operations (`x !> push(item)`);
   - Invocation of a state-capturing callable (`&capture`, `&{mut ...}`) bound to that handle;
   - Being retained or stored into an escaping or mutable data structure where the retained reference preserves active write capabilities under `&^mut`; or
   - Being passed as an argument with `mut` prefix to a `mut` parameter of a callee carrying `&mut` or `&^mut`.
2. **Rejection of Unused Mutability (`UnusedMutError`)**:
   Declaring a binding (`let mut`) or parameter (`mut param: T`) that is never written to along any reachable control-flow path is a compile-time static error (`UnusedMutError`). Redundant mutability annotations are strictly prohibited.
3. **Dead Code Rule**:
   Write operations located exclusively within statically unreachable basic blocks (e.g., following an unconditional `return`, `panic`, or within provably dead branches) do NOT satisfy the Definite Mutation Invariant.
4. **Host Contract Exemption**:
   Declarations under foreign host interfaces (`decl "C"`, `decl "host"`) lacking function bodies are exempt from the Definite Mutation Invariant at their declaration sites; call sites passing to their `mut` parameters MUST still treat arguments as actively written to.

---

## 4. Parameter Permissions and Aliasing

### 4.1 Parameter Permission Modes

Parameters declare their write and sharing permissions explicitly in their signatures:

1. **Shared Read-Only View (`param: T`)**:
   - Default mode. Grants read-only access to the caller's value or reference.
   - The reference is safely shared by default. It MAY be stored into longer-lived heap structures, returned from functions, or captured by closures without annotation, provided the target container does not grant write access to mutable fields of the stored reference (preventing read-only handle laundering).
2. **Borrowed Mutable Location (`mut param: T`)**:
   - Grants in-place write access to the caller's storage location for the duration of the call.
   - Binds both scalar locations (integers, booleans) and compound heap references.
   - Callers MUST explicitly mark arguments passed to `mut` parameters using `mut` prefix notation (e.g., `f(mut x)`) or the mutating pipeline operator (`x !> f()`).
   - **Prohibition of RValues and Temporaries**: Passing temporary expressions, literals, or rvalues to a `mut` parameter (e.g., `increment(mut 1)`) is a **compile-time static error**. Writable arguments MUST be addressable lvalue locations.

### 4.2 Aliasing Rules

Ril permits multiple mutable parameters to alias the same underlying memory location:

```ril
fn increment_both(mut left: int, mut right: int) &mut {
    left += 1
    right += 1
}

let mut count = 0
increment_both(mut count, mut count)
-- count evaluates to 2
```

1. **Order of Evaluation**: Writes to aliased parameters occur strictly in the source execution order of statements within the callee function.
2. **Absence of Undefined Behavior**: Because evaluation is strictly sequenced and memory is GC-managed, aliasing between mutable parameters does not produce undefined memory states or race conditions in single-threaded contexts.
3. **Suspension Invariance**: Active `mut` borrows remain valid across asynchronous suspension points (`@Async`).

---

## 5. Live Views vs. Detached Snapshots

Ril distinguishes between live reference observation and isolated immutable copies:

### 5.1 Live Views

Assigning a mutable object to an immutable binding (`let view = mutable_obj`) creates a **live read-only view**:
- The view cannot perform mutations (`view.field = 1` is statically rejected).
- The view cannot be upgraded to write access (`let mut bad = view` is statically rejected).
- The view observes all subsequent mutations performed through the original mutable root (`mutable_obj.field = 2`).

### 5.2 Isolated Snapshots (`snapshot`)

The prelude function `snapshot(value: T) -> T` constructs a detached, read-only deep copy of a data graph:

```ebnf
SnapshotExpr ::= Expression "|>" "snapshot" | "snapshot" "(" Expression ")"
```

1. **Deep Cloning**: `snapshot` recursively traverses all reachable heap objects, creating a brand new isolated object graph while preserving internal sharing and cycles within that graph.
2. **Permanent Immobility**: Objects created via `snapshot` are permanently read-only and CANNOT regain write access under any circumstances.
3. **Prohibition on Capabilities**:
   - Types containing resource capabilities, retained mutable sharing, or mutable closure captures (`&mut`, `&^mut`, `&capture`, or `&{mut ...}`) MUST NOT be snapshotted. Passing such types to `snapshot` is a compile-time static error.
4. **Non-Establishment of Halting or Stability**:
   - Creating a `snapshot` does NOT prove termination (`halt`) and does NOT turn an arbitrary data structure into an admissible stable index. Cyclic data remains inadmissible for stable indices even after snapshotting.
5. **Shallow Spreads vs. Deep Snapshots**:
   Record spread syntax (`.{ ...record, field: val }`) creates only a shallow copy of the outer record; nested references remain shared. To isolate the entire graph, an explicit `snapshot` is required.

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
- `record.nested_list !> push(item)`
- `lookup["key"].status = "active"`

MUST modify the targeted storage location directly in place without duplicating containing records or allocating fresh outer parent arrays.

---

## 7. Copy-on-Write Deep Updates (`produce`)

To facilitate efficient functional updates over deeply nested immutable records without full-graph cloning, the prelude provides `produce`:

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
3. **Freezing on Return**: When `recipe` completes, the modified root is frozen and returned as a fresh immutable value. The original `base` graph remains completely unmodified.
