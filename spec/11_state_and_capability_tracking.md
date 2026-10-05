# 11. State and Capability Tracking

This chapter formalizes the static capability and state tracking system in Ril, governing parameter borrows (`&mut`), closure capabilities (`&capture`), external lexical captures (`&{var}`, `&{mut var}`), capability abstraction, and invocation permission invariants.

---

## 1. Local Mutation Purity Invariant

A central principle of Ril's effect and state system is that **non-escaping local mutation is strictly pure**:

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

## 3. External State Tracking (`&{var}` and `&{mut var}`)

When a function accesses state not passed via its parameter list (e.g., module-level state or enclosing outer lexical variables), it MUST explicitly annotate that access:

```ebnf
StateItem     ::= "^" "mut" | "capture" | "mut" [ Identifier ] | Identifier
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
   Anonymous `&mut` CANNOT be used to conceal mutations to external named variables. Applying `&mut` without `&{mut var}` to a function mutating global state is a compile-time static error.
4. **Forwarding External State**:
   Forwarding an external state variable to a function accepting a `mut` parameter retains the external state mutation effect:
   ```ril
   let mut shared_hub = Counter.{ val: 0 }

   fn forward_global() &{mut shared_hub} {
       increment(mut shared_hub) -- retains &{mut shared_hub}
   }
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
3. **External State Inheritance**: A function returning a closure that captures external state inherits that external state's annotations (`&{var}` or `&{mut var}`).
4. **Composite State and Capability Annotations**:
   - Combining parameter mutation and internal closure capture: `&mut &capture` or `&{mut, capture}`.
   - Combining internal closure capture and external state capture: `&capture &{mut var}`.

---

## 5. Retained Mutable Sharing (`&^mut`)

The built-in `&^mut` capability statically tracks and audits **retained mutable sharing**, ensuring that functions creating long-lived, aliased mutable references across frames are explicitly disclosed in their public signatures.

```ril
-- Stashing a mutable argument into an outer structure introduces retained mutable sharing:
fn register_listener(mut hub: EventHub, mut listener: Listener) &^mut {
    hub.listeners !> Array::push(listener)
}
```

### 5.1 Retained Mutable Sharing Invariants

> **Normative Rule**: A function MUST declare `&^mut` in its signature if and only if its execution causes an addressable mutable location $n$ to satisfy all three conditions upon exiting its lexical allocation frame:
> 1. **Is-Mutable**: The location possesses active write capability (`mut`).
> 2. **Is-Retained**: The location escapes its lexical frame (e.g., stored into an incoming parameter, assigned to a module-level variable, captured by an escaping closure, or returned).
> 3. **Is-Forked (Aliased)**: Upon escaping, $\ge 2$ independent live access paths retain write capability to that location:
>    `|{ p ∈ P_esc(n) | permission(p) = Write }| >= 2`

1. **Forced Disclosure Requirement (`MissingRetainedSharingCapabilityError`)**:
   If the compiler's escape and sharing analysis determines that a function introduces retained mutable sharing, and the signature lacks `&^mut`, compilation MUST fail with a static error (`E0510: MissingRetainedSharingCapabilityError`).
2. **Permissive Runtime Execution**:
   The `&^mut` capability is a static audit contract and does NOT prohibit execution or induce runtime locks, reference counts, or borrow check failures. Functions carrying `&^mut` are fully conforming and execute deterministically under Ril's garbage-collected memory model.
3. **Local Discharge of `&^mut`**:
   When a caller invokes an `&^mut` function, but all arguments passed to that call and their entire transitively reachable object graphs were freshly allocated within the caller's frame, and neither the arguments nor any returned value escapes the caller, the `&^mut` capability is **discharged locally**:
   ```ril
   fn isolated_operation() -> int {
       let mut local_hub = EventHub.new()
       let mut local_listener = Listener.new()
       register_listener(mut local_hub, mut local_listener) -- &^mut discharged locally
       local_hub.count
   }
   ```
   The caller `isolated_operation` remains strictly pure to external callers.
4. **Subtyping and Subsumption**:
   State hazard capabilities form a preorder lattice (`mut` $\sqsubset$ `^mut`). Callable subtyping is covariant under capability subsumption: a localized mutable operation is a valid subtype of a retained shared mutation:
   - `fn(P) -> R &mut  <:  fn(P) -> R &^mut`
   - `fn(P) -> R &^mut </: fn(P) -> R &mut`
5. **Orthogonality to Closure Capture (`&capture`)**:
   `&^mut` and `&capture` represent orthogonal hazard dimensions:
   - `&^mut   </: &capture`
   - `&capture </: &^mut`
   An escaping closure that encapsulates internal state is `&capture`. A function that escapes a closure while retaining an external live mutable alias to the closure's state MUST declare both capabilities: `&{capture, ^mut}`.

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

`&^mut` represents an unabstractable hazard contract; concrete `&^mut` cannot be concealed by abstracting into `&capture` or `&mut`.

---

## 7. Invocation Permissions and Snapshot Prohibition

### 7.1 Invocation Permission Invariant

> **Normative Rule**:
> 1. **Internal State Mutation (`&capture`, `&{mut ...}`)**: Invoking any callable carrying internal captured state mutation strictly requires the callable identifier itself to be bound as a mutable handle (`let mut`) or a mutable parameter (`mut`). Calling such a closure through a read-only (`let`) handle is statically rejected to prevent covert mutations through read-only views.
> 2. **Parameter Mutation (`&mut`, `&^mut`)**: Invoking a callable carrying parameter mutation requires arguments supplied to `mut` parameters to be writable lvalue locations. It does NOT require the callable handle itself (or named function item) to be bound as `let mut`.

```ril
-- Stateful closure: requires mutable handle on the callable
let mut active = make_counter(0)
active() -- valid: invoked through mutable binding

let fixed = make_counter(0)
-- fixed() -- STATIC ERROR: cannot invoke '&capture' callable through read-only handle

-- Parameter mutating function: callable itself can be read-only; arguments must be mutable reference handles
let mut data = Counter.{ val: 10 }
increment(mut data) -- valid: 'data' is mutable reference handle; 'increment' is a top-level item
```

### 7.2 Snapshot Prohibition

Any type containing `&mut`, `&^mut`, `&capture`, or `&{mut ...}` callables CANNOT be snapshotted. Passing such a type to `snapshot` is a compile-time static error:

```ril
let mut job = make_counter(0)
let bad = job |> snapshot -- STATIC ERROR: type contains '&capture' callables and cannot be snapshotted
```

### 7.3 Capture and Capability Erasure Invariant

Callables capturing external state (`&{var}` or `&{mut var}`) or carrying `&mut`, `&^mut`, or `&capture` capabilities CANNOT be cast, coerced, or erased to unannotated pure function types (`fn(...) -> ...`) or plain `&mut`.
