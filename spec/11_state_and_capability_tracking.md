# 11. State and Capability Tracking

This chapter formalizes the static capability and state tracking system in Ril, governing parameter borrows (`&mut`), retained mutable sharing (`&^mut`, `&{^mut var}`), closure capabilities (`&capture`), external lexical captures (`&{var}`, `&{mut var}`), capability abstraction, and invocation permission invariants.

---

## 1. Local Mutation Purity Invariant

### 1.1 Invariant (Local Mutation Purity Invariant)

For any evaluation frame with local allocations $\mathcal{L} \subset \text{Store}$ such that $\mathcal{L} \cap \mathop{\mathrm{Escaped}}(\text{Frame}) = \emptyset$, mutating transitions on locations in $\mathcal{L}$ do not introduce capability annotations on the callable's signature:

$$
\forall l \in \mathcal{L}, \quad \text{Write}(l) \implies \Gamma \vdash f : \text{fn}(P) \to R
$$

```ril
fn sum_to(n: int) -> int {
    let mut total = 0
    let mut i = 1
    while i <= n {
        total += i
        i += 1
    }
    total -- purely functional to external callers
}
```

1. Local variables allocated within a function or block that undergo mutation and never escape do NOT infect the enclosing function's signature with state annotations.
2. The function `sum_to` above is typed as a strictly pure callable `fn(int) -> int`.

---

## 2. Parameter State Tracking (`&mut`)

When a function mutates a borrowed caller location via a `mut` parameter, it declares the anonymous `&mut` state annotation:

```ril
type Counter = { mut val: int }

fn increment(mut counter: Counter) &mut {
    counter.val += 1
}
```

### 2.1 Local Discharge of `&mut`

When a function invoking an `&mut` operation supplies local storage allocated within its own frame, the `&mut` requirement is **discharged locally**:

```ril
fn compute() -> int {
    let mut local = Counter.{ val: 10 }
    increment(mut local) -- &mut discharged locally: local is frame-confined
    local.val
}
```

The caller `compute` remains strictly pure to external observers.

---

## 3. External State Tracking (`&{var}`, `&{mut var}`, and `&{^mut var}`)

When a function accesses state not passed via its parameter list (e.g., module-level state or enclosing outer lexical variables), it MUST explicitly annotate that access:

```ebnf
StateItem     ::= "^" "mut" [ Identifier ] | "capture" | "mut" [ Identifier ] | Identifier
StateItems    ::= StateItem { "," StateItem } [ "," ]
StateArgument ::= "&" ( "mut" | "^" "mut" | "capture" | "{" [ StateItems ] "}" )
```

1. **Reading External State (`&{var}`)**:
   Reading an external variable from outer scope without mutating it requires `&{var}`:
   ```ril
   let title = "Ril Core"
   fn read_title() -> str &{title} { title }
   ```
2. **Mutating External State (`&{mut var}`)**:
   Mutating an external variable requires explicit `&{mut var}`:
   ```ril
   let mut counter = 0
   fn tick() -> int &{mut counter} {
       counter += 1
       counter
   }
   ```
3. **Prohibition of Anonymous Concealment**:
   Anonymous `&mut` CANNOT be used to conceal mutations to external named variables. An external mutable access MUST be covered by `&{mut var}` or the stronger `&{^mut var}`. Anonymous `&^mut` likewise CANNOT replace a known external origin's named sharing annotation, except through the explicit interface abstraction in §6.
4. **Forwarding External State**:
   Forwarding an external state variable to a function accepting a `mut` parameter retains the external state mutation effect:
   ```ril
   let mut shared_hub = Counter.{ val: 0 }

   fn forward_global() &{mut shared_hub} {
       increment(mut shared_hub) -- retains &{mut shared_hub}
   }
   ```

### 3.1 Named Retained Mutable Sharing (`&{^mut var}`)

`&{^mut var}` permits mutable access to an external binding and discloses that the callable may establish retained mutable sharing of storage originating from that binding. It subsumes `&{mut var}` for the same binding; both annotations are not required together.

```ril
type Counter = { mut value: int }
type Hub = { mut counters: []Counter }
let mut counter = Counter.{ value: 0 }

fn register_counter(mut hub: Hub) &{mut, ^mut counter} {
    hub.counters !> Array::push(counter)
}
-- 'mut' covers the parameter hub; '^mut counter' covers the retained
-- writable alias to the external Counter, whose original handle remains live.
-- Using only &{mut, mut counter}, or &{mut counter, ^mut}, is insufficient
-- to disclose this known external sharing origin: static error E0510.
```

1. **Origin Identity**: The identifier resolves lexically to a binding identity, not merely its textual spelling. Its tracked storage comprises the binding's mutable cell and the reference object graph reachable through that binding when accessed. Alias and projection provenance MUST preserve originating storage identities through assignments, containers, returns, closure capture, and indirect calls. Different names do not establish disjointness; rebinding a reference does not change the origin of aliases already retained.
2. **Source vs. Destination**: The named item identifies the source of shared writable storage. Storing `counter` into `hub` introduces sharing of `counter`; modifying the destination `hub` is a separate mutation obligation. Merely storing a fresh local object into an external container does not establish sharing of the container's own storage. Sharing of a fresh local origin is covered by anonymous `&^mut` when multiple writable paths are retained.
3. **Value Copies vs. Captured Cells**: Copying the value of an external scalar does not alias its binding cell. An escaping closure capturing that scalar for subsequent mutation retains access to the same cell. If the original writable access remains live, the closure's publication introduces named retained sharing even if the creating call performs no immediate write.
4. **Boundary and Existing Sharing**: Sharing is determined at the callable's return or a closure publication/escape boundary, as specified in §5.1. Merely reading or modifying storage that was already shared does not introduce an additional sharing obligation. Temporary mutable borrows ending at the call boundary and retained read-only aliases do not qualify.
5. **Permissions**: A named sharing annotation does not grant write permission to a read-only binding. The referenced binding MUST possess mutable access permission; attempting `&{^mut ro}` on a read-only origin is mutability laundering. Escaping closures and containers MUST retain only permissions actually available at their source.
6. **Multiple Origins and Forwarding**: Every known external origin whose writable access is newly retained MUST be covered, e.g. `&{^mut left, ^mut right}`. Calling an `&^mut` operation with external storage substitutes that storage's origin into the sharing obligation. Mutation-only forwarding retains `&{mut var}`. Calls involving both parameter/local origins and external origins MAY require both anonymous and named sharing items.

```ril
let mut total = 0

fn share_total() -> (fn() -> int &{mut total}) &{^mut total} {
    \-> { total += 1; total }
}
-- Creating the escaping closure shares the external variable's cell.
-- Calling the returned closure only mutates that existing cell; its callable
-- type needs &{mut total}, not ^mut unless it introduces further sharing.
```

---

## 4. Closure Environment Capabilities (`&capture`) and Composition

The built-in `&capture` capability marks functions that allocate and return an escaping closure capturing local/internal state:

```ril
pub type Counter = fn() -> int &capture

pub fn make_counter(start: int) -> Counter &capture {
    let mut count = start
    \-> { count += 1; count } -- escaping closure captures internal 'count'
}
```

### 4.1 Closure Capability Rules

1. **Escaping State Invariant**: A function that constructs and returns an escaping closure that captures local state allocated within that function MUST declare `&capture` in its signature.
2. **Pure Closures**: Functions returning closures that capture no environment state do NOT annotate `&capture` (e.g., `fn() -> (fn() -> int)`).
3. **External State Inheritance**: A function returning a closure that captures external state inherits that external state's annotations (`&{var}` or `&{mut var}`). Publishing a new writable capture while another writable path survives additionally requires `&{^mut var}`, which subsumes `&{mut var}` on the creating function. The returned closure's invocation capabilities describe what its body does; publishing it does not automatically add `^mut` to every later invocation.
4. **Composite State and Capability Annotations**:
   - Combining parameter mutation and internal closure capture: `&mut &capture` or `&{mut, capture}`.
   - Combining internal closure capture and external state capture: `&capture &{mut var}`.

---

## 5. Retained Mutable Sharing (`&^mut`)

The built-in `&^mut` capability statically tracks and audits **retained mutable sharing** of parameter or locally allocated origins. The named form `&{^mut var}` tracks the same hazard for an external lexical origin. Both ensure that long-lived, aliased writable access is explicitly disclosed in callable signatures.

```ril
-- Stashing a mutable argument into an outer structure introduces retained mutable sharing:
fn register_listener(mut hub: EventHub, mut listener: Listener) &^mut {
    hub.listeners !> Array::push(listener)
}
```

### 5.1 Retained Mutable Sharing Invariants

> **Normative Rule**: A callable MUST cover each retained mutable sharing obligation with `&^mut` or `&{^mut var}` according to the origin rules in §3.1. An obligation arises when execution causes an addressable mutable location $n$ to satisfy all three conditions at the callable's return or a closure publication/escape boundary, regardless of where or when $n$ was allocated:
> 1. **Is-Mutable**: The location possesses active write capability (`mut`).
> 2. **Is-Newly-Retained**: The operation establishes at least one new writable access path that survives the relevant boundary (e.g., stored into an incoming parameter or module-level structure, captured by an escaping closure, or returned). A temporary borrow, a read-only alias, or reuse of an existing retained path does not satisfy this condition.
> 3. **Is-Forked (Aliased)**: At that boundary, $\ge 2$ independent live access paths retain write capability to that location:
>    `|{ p ∈ P_esc(n) | permission(p) = Write }| >= 2`

Capability annotations are upper bounds on permitted behavior, consistent with callable subtyping. Declaring a stronger sharing contract does not require every execution path to create an alias. Uniquely transferring writable ownership without another surviving writable path does not introduce retained mutable sharing.

1. **Forced Disclosure Requirement (`MissingRetainedSharingCapabilityError`)**:
   If escape and sharing analysis identifies an uncovered obligation, including a missing named external origin, compilation MUST fail with `E0510: MissingRetainedSharingCapabilityError`. If origin or escape analysis cannot prove that an operation avoids retained mutable sharing, the compiler MUST conservatively retain the corresponding obligation rather than silently erase it.
2. **Permissive Runtime Execution**:
   Anonymous and named sharing capabilities are static audit contracts and do NOT induce runtime locks, reference counts, or borrow check failures. They do not relax read-only, scoped-resource, exclusivity, ownership-transfer, or concurrency constraints.
3. **Local Discharge of `&^mut`**:
   A caller MAY discharge an anonymous or named sharing obligation only when all affected source origins, retention destinations, and their transitively reachable writable storage are confined to fresh allocations within the caller's frame, and no retained writable path or returned capability escapes that frame. This analysis MUST include external captures of the callee and callbacks, not only explicit arguments. A binding external to a nested helper can still be local to its caller; module-level storage cannot be discharged merely because the arguments are local:
   ```ril
   fn isolated_operation() -> int {
       let mut local_hub = EventHub.new()
       let mut local_listener = Listener.new()
       register_listener(mut local_hub, mut local_listener) -- &^mut discharged locally
       local_hub.count
   }
   ```
   The caller `isolated_operation` remains strictly pure to external callers.

   ```ril
   fn local_capture_only() -> int {
       let mut local_counter = Counter.{ value: 0 }
       let mut local_hub = Hub.{ counters: [] }
       fn retain(mut hub: Hub) &{mut, ^mut local_counter} {
           hub.counters !> Array::push(local_counter)
       }
       retain(mut local_hub)
       len(local_hub.counters)
   }
   -- local_counter is external to retain, but both source and destination
   -- are confined to local_capture_only: its signature remains pure.
   -- register_counter(mut local_hub) instead retains module-level counter
   -- and requires ^mut counter on the enclosing function.
   ```

4. **Subtyping and Subsumption**:
   State hazard capabilities form a preorder lattice (`mut` $\sqsubset$ `^mut`). Callable subtyping is covariant under capability subsumption: a localized mutable operation is a valid subtype of a retained shared mutation:
   - `fn(P) -> R &mut  <:  fn(P) -> R &^mut`
   - `fn(P) -> R &^mut </: fn(P) -> R &mut`
   For the same external binding identity `x`, `fn(P) -> R &{mut x} <: fn(P) -> R &{^mut x}`, but not conversely. Neither relation permits substitution of a different binding identity. For one origin, `^mut x` subsumes `mut x` and read access `x`; for mixed origins, each obligation remains distinct.
5. **Orthogonality to Closure Capture (`&capture`)**:
   `&^mut` and `&capture` represent orthogonal hazard dimensions:
   - `&^mut   </: &capture`
   - `&capture </: &^mut`
   An escaping closure that encapsulates freshly allocated internal state is `&capture`. A function that publishes that closure while retaining another writable path to its internal state MUST declare `&{capture, ^mut}`. Sharing an existing external state cell instead requires its named `^mut var` obligation (§3.1); it does not itself allocate new internal state.

---

## 6. Interface Abstraction

> **Normative Rule**: In function types and public interfaces, concrete captured bindings **abstract to general capabilities**: concrete `&{mut var}` satisfies the abstract capability `fn(...) -> ... &capture`.

```ril
-- Internal concrete implementation:
let mut saved = 0
let ticker: fn() -> int &{mut saved} = \-> { saved += 1; saved }

-- Abstract public interface satisfaction:
let general: fn() -> int &capture = ticker -- VALID: &{mut saved} abstracts to &capture
```

The sharing hazard cannot be erased by abstraction. A concrete `&{^mut var}` MAY hide its binding name behind an interface carrying **both** `&capture` and anonymous `&^mut` (e.g., `&{capture, ^mut}`). Abstraction to only `&capture`, `&mut`, or `&{mut var}` is prohibited. Anonymous `&^mut` likewise cannot be concealed by `&capture` or `&mut` alone. Compilers MUST preserve hidden origin and escape summaries for alias checks and local discharge; hiding a name does not prove confinement or disjointness.

---

## 7. Invocation Permissions and Clone Prohibition

### 7.1 Invocation Permission Invariant

> **Normative Rule**:
> 1. **Captured Mutable State (`&capture`, `&{mut ...}`, `&{^mut ...}`)**: Invoking any callable value carrying captured mutable access or sharing strictly requires the callable identifier itself to be bound as a mutable handle (`let mut`) or a mutable parameter (`mut`). Calling such a closure through a read-only (`let`) handle is statically rejected (`E0520: MutabilityLaunderingError`) to prevent covert mutations or writable retention through read-only views. Named function items access their declared external bindings directly; this handle requirement applies to callable values, not to binding a named function declaration as `let mut`.
> 2. **Parameter Mutation (`&mut`, `&^mut`)**: Invoking a callable carrying parameter mutation requires arguments supplied to `mut` parameters to be writable lvalue locations. It does NOT require the callable handle itself (or named function item) to be bound as `let mut`.

```ril
-- Stateful closure: requires mutable handle on the callable
let mut active = make_counter(0)
active() -- valid: invoked through mutable binding

let fixed = make_counter(0)
-- fixed() -- STATIC ERROR [E0520]: cannot invoke '&capture' callable through read-only handle

-- Parameter mutating function: callable itself can be read-only; arguments must be mutable reference handles
let mut data = Counter.{ val: 10 }
increment(mut data) -- valid: 'data' is mutable reference handle; 'increment' is a top-level item
```

### 7.2 Clone and Immutability Prohibition Theorem

Any type containing `&mut`, `&^mut`, `&capture`, `&{mut ...}`, or `&{^mut ...}` callables, or scoped resource handles CANNOT be converted into an immutable representation via `clone_immut` (nor can scoped resource handles be cloned via `clone`). Passing such a type to `clone_immut` is a compile-time static error:

```ril
let mut job = make_counter(0)
let bad = job |> clone_immut -- STATIC ERROR: type contains '&capture' callables and cannot be converted to Immut
```

### 7.3 Capture and Capability Erasure Invariant

Callables capturing external state (`&{var}`, `&{mut var}`, or `&{^mut var}`) or carrying `&mut`, `&^mut`, or `&capture` capabilities CANNOT be cast, coerced, or erased to unannotated pure function types (`fn(...) -> ...`) or plain `&mut`. The explicit abstraction in §6 preserves both captured access and sharing hazards.

---

## 8. Capability Anti-Laundering Formal System

Ril defines an axiomatic formal system governing permission preservation, preventing covert mutation laundering through handles, closures, containers, or return values.

### 8.1 Monotonic Permission Degradation Axiom

Permissions across reference access paths satisfy the strict partial order:

$$
\text{Mut} \succ \text{ReadOnly} \succ \text{None}
$$

Permissions SHALL degrade monotonically along dataflow paths ($\text{Mut} \to \text{ReadOnly}$). Any operation attempting to upgrade, coerce, or cast a read-only reference or handle back into a mutable capability is statically rejected.

### 8.2 Capability Preorder Lattice

State capabilities form a bounded preorder lattice $(\Sigma, \sqsubseteq)$:

$\emptyset \sqsubset$ `&mut` $\sqsubset$ `&^mut`

For each external binding identity `x`, the corresponding chain is `&{x}` $\sqsubset$ `&{mut x}` $\sqsubset$ `&{^mut x}`, with $\And\text{capture}$ spanning an orthogonal dimension. Named obligations from distinct identities remain separate even when alias analysis finds overlapping storage. Subsumption allows narrower capability contracts to satisfy broader capability contexts:

$$
\mathcal{S}_1 \sqsubseteq \mathcal{S}_2 \implies \text{fn}(P) \to R \ \mathbin{\And}\mathcal{S}_1 \lt : \text{fn}(P) \to R \ \mathbin{\And}\mathcal{S}_2
$$

### 8.3 Anti-Laundering Static Diagnostic Closure Matrix

A conforming compiler MUST reject mutability laundering attempts under the following normative static error taxonomy:

| Error Code | Diagnostic Identifier | Violation Criterion |
| :--- | :--- | :--- |
| **`E0510`** | `MissingRetainedSharingCapabilityError` | Function introduces retained writable aliases without the required anonymous `&^mut` or named `&{^mut var}` contract, or erases that hazard through abstraction. |
| **`E0520`** | `MutabilityLaunderingError` | Binding a read-only reference to `let mut`, mutating through a read-only live view, or invoking captured mutable access/sharing via a read-only handle. |
| **`E0521`** | `DestructuringLaunderingError` | Destructuring a read-only reference with `mut` modifiers on nested reference fields. |
| **`E0522`** | `ContainerLaunderingError` | Storing a read-only reference into a mutable container or mutable record field. |
| **`E0523`** | `MutMutAliasingConflictError` | Overlapping independent write access paths through mutable arguments or external captures in a single call. |
| **`E0524`** | `ReadMutAliasingHazardError` | Overlapping independent read and mutable access paths through arguments or external captures in a single call. |
| **`E0525`** | `SpreadLaunderingError` | Shallow-spreading a read-only record with reference fields into a `let mut` root binding. |
| **`E0526`** | `CollectionMutationDuringIterationError`| Mutating a collection in place while actively iterating over it in a `for` loop. |
| **`E0527`** | `ClosureCaptureLaunderingError` | Capturing read-only references into `&{mut ro}` or `&{^mut ro}`, or passing read-only handles to `mut` parameters. |
| **`E0528`** | `ReturnLaunderingError` | Binding a function return value to `let mut` when that value originates from a read-only parameter. |
