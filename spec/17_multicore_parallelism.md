# 17. Multicore Parallelism and Data Parallelism

This chapter formalizes Ril's multicore parallel execution model, data parallelism combinators, structured task parallelism, deterministic reduction invariants, work-stealing scheduling semantics, and parallel capability constraints.

---

## 1. Multicore Parallel Execution Model

Parallelism in Ril designates compute-bound evaluation executing across multiple hardware execution contexts (cores/threads) on shared-memory architectures. Parallelism is strictly orthogonal to asynchronous fiber suspension (`@Async`, `@Fiber`).

### 1.1 Worker Execution Model

1. **Worker Pool**: A conforming multicore runtime SHALL manage a pool of $P$ worker threads ($P \ge 1$), where $P$ defaults to the number of available hardware execution contexts unless configured otherwise.
2. **Task Distribution**: Parallel compute workloads are decomposed into discrete, non-blocking evaluation tasks scheduled across worker threads.
3. **Absence of Shared Mutable State**: Conforming parallel tasks MUST NOT communicate via unmanaged mutable memory. Coordination is restricted to fork-join synchronization, deterministic reduction, and interior synchronization primitives (`Atom`, `Channel`).

---

## 2. Parallel Capability Tracking and Isolation

Parallel execution is governed by Ril's state capability tracking system (Chapter 11) and concurrency classification (Chapter 05).

### 2.1 Parallel Local Mutation Purity Theorem

**Theorem 17.1 (Parallel Local Mutation Purity)**:
Let $T$ be an evaluation task executing on a worker thread. Any local mutable binding `let mut local = expr` allocated inside $T$'s execution frame that does NOT escape $T$'s lexical lifetime satisfies:
1. **Thread-Confinement**: The storage location of `local` is strictly private to the hardware thread executing $T$, residing entirely within the thread's stack or thread-local heap allocation frame.
2. **Zero Cross-Core Coherence Traffic**: In-place mutations (`local !> op()`, `local[i] = v`) do NOT broadcast cache-invalidation signals to other processor cores, as the referenced storage is provably unshared.
3. **Local Capability Discharge**: When $T$ terminates and produces a value $V$ whose type carries no retained capabilities (`&mut`, `&^mut`, `&capture`), all mutation capabilities $\sigma$ are **discharged locally**.
4. **Referential Transparency**: To any external or parent task, $T$ evaluates as a pure, side-effect-free mathematical function.

### 2.2 Static Data-Race Freedom Theorem

**Theorem 17.2 (Static Absence of Data Races)**:
An expression is admissible for parallel evaluation if and only if all sub-computations require zero external mutable capabilities ($\sigma \cap \Sigma_{\text{mut}} = \emptyset$, prohibiting active `&mut`, `&^mut`, `&capture`, and lexical `&{mut ...}`) and zero unhandled algebraic effects.
Any parallel closure capturing an external variable `v` MUST satisfy $\text{typeof}(v) \in \text{Shareable}$.
Consequently:

$$
\forall e_1, e_2 \text{ evaluated in parallel}, \quad \text{Writes}(e_1) \cap \text{Reads}(e_2) = \emptyset \land \text{Writes}(e_1) \cap \text{Writes}(e_2) = \emptyset
$$

---

## 3. Data Parallelism Library Interface (`ril/parallel`)

The standard library module `ril/parallel` provides pure data-parallel combinators operating over slices `[]T`:

```ril
-- Module: ril/parallel
module parallel {
    pub fn par_map<T, U>(source: []T, transform: fn(T) -> U) -> []U
    pub fn par_filter<T>(source: []T, predicate: fn(T) -> bool) -> []T
    pub fn par_reduce<T>(source: []T, identity: T, combine: fn(T, T) -> T) -> T
    pub fn par_fold<T, Acc>(
        source: []T,
        init_acc: fn() -> Acc,
        fold_local: fn(mut Acc, T) -> () &mut,
        merge_acc: fn(Acc, Acc) -> Acc,
    ) -> Acc
    pub fn par_chunks<T, R>(
        source: []T,
        chunk_size: int,
        process_chunk: fn([]T) -> R,
    ) -> []R
    pub fn par_sort_by<T>(source: []T, compare: fn(T, T) -> int) -> []T
    pub fn par_scan<T>(source: []T, identity: T, combine: fn(T, T) -> T) -> []T
}
```

### 3.1 Operator Semantics

1. **`par_map(source, transform)`**: Applies `transform` to each element of `source` in parallel, returning a newly allocated slice `[]U`. `transform` MUST NOT declare mutable state capabilities.
2. **`par_filter(source, predicate)`**: Evaluates `predicate` across elements in parallel, concatenating elements satisfying the predicate into a fresh slice in original input order.
3. **`par_reduce(source, identity, combine)`**: Reduces elements via the canonical binary reduction tree (§5.1). `combine` MUST be associative with respect to `identity`.
4. **`par_fold(source, init_acc, fold_local, merge_acc)`**:
   - For each worker partition, invokes `init_acc()` to instantiate a thread-local accumulator.
   - Accumulates slice elements using in-place mutation: `fold_local(mut acc, item)` via mutating pipeline (`!>`).
   - Upon partition exhaustion, discharges `&mut` and merges thread accumulators deterministically using `merge_acc` along the canonical reduction tree.
5. **`par_chunks(source, chunk_size, process_chunk)`**: Splits `source` into contiguous chunks of length `chunk_size` (the final chunk MAY be smaller), processing each chunk in parallel and returning `[]R`.

---

## 4. Scheduling and Grain Semantics

### 4.1 Work-Stealing Scheduling

A conforming parallel runtime SHALL evaluate parallel tasks using a work-stealing scheduler:
1. Each worker thread maintains a double-ended task queue (deque).
2. The local thread pushes and pops sub-tasks at the bottom (LIFO order).
3. Idle threads steal tasks from the top of other threads' deques (FIFO order).

### 4.2 Grain Sizing and Bisection

1. **Canonical Reduction Grain ($G_{\text{canonical}}$)**:
   The evaluation topology of reductions is governed by a fixed canonical leaf grain size $G_{\text{canonical}} = 64$, independent of physical core count $P$, ensuring input-determined reduction tree shapes.
2. **Dynamic Work-Stealing Grain ($G_{\text{steal}}$)**:
   To amortize task deque scheduling overhead, runtime workers steal canonical sub-trees grouped according to:

   $$
   G_{\text{steal}}(P) = \max\left(G_{\text{canonical}}, \; \frac{N}{8 \times P}\right)
   $$
3. **Sequential Vectorization Fallback**:
   When a sub-slice length satisfies $N \le G_{\text{canonical}}$, the worker thread executes a sequential loop over contiguous elements. An implementation MAY vectorize such loops using native SIMD instructions.
4. **Cache-Oblivious Bisection**:
   For $N > G_{\text{canonical}}$, the range is recursively bisected at $\lfloor (start + end) / 2 \rfloor$. The left sub-range and right sub-range form the canonical child nodes in the evaluation tree.

---

## 5. Structured Task Parallelism via Multi-Core Nursery

Heterogeneous task parallelism in Ril does NOT require specialized language keywords or ad-hoc arity functions. Instead, task-level parallel execution is unified under **`nursery`** (Chapter 10, §4.1) executing within a multi-core work-stealing scheduler:

```ril
use ril/concurrent::{nursery, Scope, Task}

let (metrics, index, warnings) = nursery \mut scope -> {
    let t1 = scope !> Scope::spawn \-> compute_metrics(data_1)
    let t2 = scope !> Scope::spawn \-> compute_index(data_2)
    let t3 = scope !> Scope::spawn \-> check_warnings(data_3)

    (t1 |> Task::join()?, t2 |> Task::join()?, t3 |> Task::join()?)
}
```

1. **Unification with Structured Concurrency**:
   Task parallelism shares identical semantics with structured asynchronous concurrency. Under a multi-core work-stealing handler (`Schedulers::work_stealing`), spawned tasks are distributed directly across worker execution queues.
2. **Arbitrary Arity and Types**:
   A `nursery` block naturally accommodates any number of concurrent tasks ($N \ge 1$) with completely heterogeneous return types, avoiding arity limits or tuple chaining.
3. **Purity and Capability Confinement**:
   Parallel child tasks spawned within a multi-core nursery MUST require zero external mutable capabilities ($\sigma \cap \Sigma_{\text{mut}} = \emptyset$, prohibiting active `&mut`, `&^mut`, `&capture`, and lexical `&{mut ...}`). Passing a mutating closure across work-stealing worker threads MUST yield compile-time static error `E0605: InvalidParallelCapabilityError`.
4. **Deterministic Cancellation and Scoped Cleanup**:
   If any spawned task panics or aborts early, the nursery immediately initiates cascading cancellation of all remaining sibling tasks and deterministically executes LIFO cleanup of all parent and child `let scoped` resources.

---

## 6. Determinism Invariants

To comply with **Chapter 01 (§1.1 Semantic Determinism Invariant)**, parallel evaluation in Ril MUST guarantee that all observable numeric outputs match sequential reference evaluation bit-for-bit.

### 6.1 Floating-Point Canonical Reduction Tree

In IEEE 754 arithmetic, floating-point addition and multiplication are non-associative:

$$
(a + b) + c \neq a + (b + c)
$$

**Normative Rule (Canonical Reduction Topology)**:
In `par_reduce` and `par_fold`, reduction operations MUST strictly evaluate along a **predetermined canonical binary tree topology** indexed by input slice bounds and fixed leaf grain $G_{\text{canonical}} = 64$:

$$
\operatorname{Reduce}(s, e) = \begin{cases} 
\operatorname{Reduce}_{\mathrm{seq}}(s, e), & \text{if } (e - s) \le G_{\text{canonical}} \\
\operatorname{combine}(\operatorname{Reduce}(s, m), \operatorname{Reduce}(m, e)), & \text{where } m = s + \lfloor (e - s) / 2 \rfloor
\end{cases}
$$

Dynamic work-stealing schedules sub-trees across available cores, but partial results are combined strictly according to the parent-child relationships defined by the canonical static topology. The final floating-point result is bit-for-bit invariant regardless of thread count $P$, CPU frequency fluctuations, or operating system thread preemption.

### 6.2 Splittable Pseudo-Random Numbers

1. **Topology-Keyed RNG State**:
   Parallel PRNG streams derive internal state from a counter-based hash keyed on the task's unique node path within the reduction DAG:

   $$
   \text{Seed}_{\text{child}} = \text{hash}(\text{Seed}_{\text{parent}}, \text{ChildIndex})
   $$
2. **Reproducibility Invariant**:
   A parallel randomized computation MUST produce the identical sequence of pseudo-random numbers and identical numerical results regardless of the number of worker threads $P$.

### 6.3 Deterministic Panic Precedence

If multiple concurrent tasks spawned within a parallel nursery or multiple chunks of a data-parallel combinator raise panics simultaneously:
1. **Primary Panic Selection**: The panic raised by the task or chunk with the **lowest lexical source position** or **smallest index range** SHALL be designated as the **Primary Panic**.
2. **Panic Attachment**: All panics raised by concurrent tasks with higher indices or later source positions MUST be captured and deterministically attached to the Primary Panic as suppressed causes.
3. **Sibling Cancellation**: Upon any panic, sibling tasks in the same nursery or parallel construct MUST be signaled for cooperative cancellation at the earliest safe checkpoint.

---

## 7. Formal Conformance Criteria

A conforming Ril compiler and runtime implementation supporting multicore parallelism MUST satisfy:

1. **Static Capability Rejection (`E0605`)**:
   Attempting to pass a callable carrying active `&mut`, `&^mut`, `&capture`, or external `&{mut var}` to `par_map`, `par_reduce`, `par_fold`, or any parallel worker task MUST result in compile-time static error `E0605: InvalidParallelCapabilityError`.
2. **Bit-Level Floating-Point Determinism**:
   Conforming parallel reductions MUST evaluate floating-point expressions according to the canonical binary tree topology defined in §6.1, producing bit-for-bit identical results regardless of worker thread count $P$.
3. **Structured Lifetime Confinement**:
   A conforming runtime MUST guarantee that no worker thread continues executing sub-tasks spawned by a parallel nursery after the enclosing nursery returns or unwinds.
4. **Deterministic Panic Precedence**:
   In multicore evaluations where multiple parallel tasks panic, the emitted panic structure MUST deterministically designate the task with lowest lexical/index order as primary.
