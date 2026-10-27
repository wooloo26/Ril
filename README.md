# Ril

**Ril** is an expression-oriented systems and application language designed around deep immutability, zero-cost live observation, explicit retained mutable sharing, fine-grained capability & effect tracking, and unified compile-time introspection.

The following sections highlight Ril's distinctive innovations over mainstream languages.

---

### Orthogonal Binding and Storage Matrix

Declarations cleanly decouple **slot reassignability** (`let` pinned vs. `var` reassignable) from **interior capability** (deeply immutable vs. `mut` interior-writable vs. `view` live observer), including deterministic lexical resource scopes (`scoped`).

```ril
type Document = { mut title: str }
type Resource = { name: str, on_close: fn() -> () }

pub fn storage_matrix() {
    let doc1 = Document.{ title: "Doc 1" }
    let doc2 = Document.{ title: "Doc 2" }

    -- 1. let: pinned immutable binding (deeply immutable graph, thread-safe)
    let immutable_doc = doc1
    -- immutable_doc.title = "Draft"        -- Error [E0520]: immutable binding has no write permission
    -- immutable_doc = doc2                 -- Error [E0501]: pinned slot cannot be rebound

    -- 2. let mut: pinned mutable handle
    let mut pinned_draft = clone(doc1)
    pinned_draft.title = "Revised"          -- OK: in-place interior write permitted
    -- pinned_draft = clone(doc2)           -- Error [E0502]: pinned handle cannot be rebound

    -- 3. let view: pinned live view (tracks mutations without write authority)
    let view pinned_view = pinned_draft
    assert(pinned_view.title == "Revised")
    -- pinned_view.title = "Hacked"         -- Error [E0520]: view grants no write authority

    -- 4. var: reassignable read-only slot
    var selected_doc = doc1
    selected_doc = doc2                     -- OK: slot rebound
    -- selected_doc.title = "New"           -- Error [E0520]: var grants no interior write permission

    -- 5. var mut: reassignable slot AND mutable handle
    var mut active_draft = clone(doc1)
    active_draft.title = "Active 1"         -- OK: interior write permitted
    active_draft = clone(doc2)              -- OK: slot rebound
    active_draft.title = "Active 2"

    -- 6. var view: reassignable live view cursor
    var view cursor = pinned_draft
    let mut target_draft = clone(doc2)
    cursor = target_draft                   -- OK: cursor rebound to another pinned mutable origin

    -- 7. let scoped mut: deterministic LIFO resource cleanup
    let mut log: []str = []
    {
        let scoped mut res = Resource.{
            name: "port",
            on_close: \-> { log !> Array::push("closed") },
        }
    }
    assert(log == ["closed"])               -- Cleaned up automatically on scope exit
}
```

| Binding | Slot Reassignment | Interior Writes | Data Guarantee / Semantics |
| :--- | :---: | :---: | :--- |
| `let` | No (`E0501`) | No (`E0520`) | Deeply immutable, freely shareable across tasks |
| `let mut` | No (`E0502`) | Granted | Pinned mutable handle; root for live views |
| `let view` | No (`E0502`) | No (`E0520`) | Pinned live view observing mutations of a `let mut` origin |
| `var` | Yes | No (`E0520`) | Reassignable slot; referenced data remains read-only |
| `var mut` | Yes | Granted | Reassignable slot with interior write authority |
| `var view` | Yes | No (`E0520`) | Reassignable live view cursor; rebound across `let mut` origins |
| `let scoped mut` | No (`E0502`) | Granted | Deterministic LIFO cleanup (`on_close`) on scope exit or abort |

---

### Live Views and Safe Functional Updates (`derive`)

Live views dynamically observe interior mutations without holding write access. `clone_immut` snapshots a live view into a deeply immutable graph, while `derive` enables in-place mutation within an unescapable, isolated temporary draft.

```ril
type Document = { mut title: str }

pub fn views_and_derivation() {
    let mut working = Document.{ title: "Draft" }
    let view observed = working            -- Live non-owning observer
    let view read_title = \-> observed.title

    working.title = "Revised"
    assert(read_title() == "Revised")      -- Reflects underlying mutation live

    -- Snapshot a live view into deeply immutable data
    let snapshot: Immut<Document> = clone_immut(observed)
    working.title = "Working Again"
    assert(snapshot.title == "Revised")    -- Isolated from further mutations

    -- Functional update on immutable data via confined mutable draft
    let updated = snapshot |> derive \mut draft -> {
        draft.title = "Published"
        -- draft references cannot escape the closure (E0607)
    }
    assert(snapshot.title == "Revised")
    assert(updated.title == "Published")
}
```

- **`let view`**: Non-owning live window over a `let mut` origin. Does not freeze the target, nor can it be laundered into write access.
- **`clone_immut`**: Deep-copies eligible data into an independent, deeply immutable `Immut<T>` value.
- **`derive`**: Receives an immutable source and executes an isolated `\mut draft -> ()` recipe. Unaffected subtrees are structurally shared, while the draft is strictly confined (`E0607`).

---

### Explicit Retained Sharing (`^mut`) and Law of Exclusivity

Mutable handles cannot be aliased implicitly. Replicating or retaining a mutable reference requires explicit `^mut`. The compiler statically enforces disjointness across arguments to eliminate aliased race conditions.

```ril
type Node = { mut val: int }
type Hub = { mut nodes: []Node }

fn attach(mut hub: Hub, ^mut node: Node) &^mut {
    hub.nodes !> Array::push(^mut node)    -- Explicit retained write authority
}

fn swap(mut a: Node, mut b: Node) &mut {
    let temp = a.val
    a.val = b.val
    b.val = temp
}

pub fn test_sharing_and_exclusivity() {
    let mut n = Node.{ val: 1 }
    -- let mut hidden = n                  -- Error [E0510]: implicit mutable alias forbidden
    let mut alias = ^mut n                 -- OK: explicitly marked retention
    alias.val = 2
    assert(n.val == 2)

    -- In-place mutation pipeline (!>) vs transform pipeline (|>)
    let mut list = [1, 2]
    list !> Array::push(3)                 -- In-place mutation: list becomes [1, 2, 3]
    let doubled = list |> Array::map(\x -> x * 2) -- Pure transformation

    -- Law of Exclusivity: cross-argument disjointness
    let mut n1 = Node.{ val: 10 }
    let mut n2 = Node.{ val: 20 }
    swap(mut n1, mut n2)                   -- OK: proven disjoint origins
    -- swap(mut n1, mut n1)                -- Error [E0523]: overlapping mutable origins
}
```

- **Explicit `^mut`**: Retaining an alias or container entry requires explicit `^mut` at both declaration and use sites, preventing unexpected side effects.
- **In-Place Pipeline (`!>`)**: Clearly distinguishes mutating operations (`x !> f` desugars to `f(mut x)`) from immutable transform pipelines (`x |> f` desugars to `f(x)`).
- **Cross-Argument Disjointness**: The compiler verifies actual memory origins; overlapping mutable arguments to distinct `mut` parameters are rejected (`E0523`).

---

### Fine-Grained Capability and State Tracking

The capability system tracks parameter mutation, external state, and closure environments without sacrificing local mutation flexibility or leaking implementation secrets.

```ril
-- 1. Local Mutation Purity: local writes are discharged; callers see purity @{} &{}
pub fn histogram(scores: []int) -> []int @{} &{} {
    let mut counts = [0, 0, 0]
    for scores as score {
        counts[score] += 1
    }
    counts                                 -- Discharges local mutation; published as immutable
}

-- 2. State Contract References: inherit verified state access without exposing private storage
-- counter.ril
var private_counter = 0
pub fn tick() &{mut private_counter} {
    private_counter += 1
}

-- client.ril
use counter
pub fn step() &Counter::tick {
    Counter::tick()                        -- Inherits verified contract without private names
}
-- pub fn bad_step() { Counter::tick() }  -- Error [E0510]: inherited state is undeclared

-- 3. Layered Closure Capture Tracking
type Step = fn() -> int &closure

fn make_step(increment: int) -> Step &capture {
    var count = 0
    step
    where
        fn step() -> int &{closure, increment, mut count} {
            count += increment
            count
        }
}
```

- **Local Capability Discharge**: Functions allocating and mutating local data can return immutable results and be certified pure (`@{} &{}`).
- **Opaque State Inheritance**: `&Module::func` inherits another function's verified concrete state obligations without exposing internal variable identities.
- **Explicit Obligations**: Function signatures explicitly declare parameter mutation (`&mut`), retention (`&^mut`), and capture contracts (`&capture`, `&{closure, ...}`).

---

### Algebraic Effects, Affine Resumption, and Finite Evaluation (`Div`)

Ril features first-class algebraic effects with strictly affine resumptions, deterministic early abort with LIFO cleanup, and totality guarantees via `Div`.

```ril
eff Ask { prompt(str) -> str }
eff Auth { authenticate() -> bool }

-- 1. Effect Handlers and Affine Resumption
fn greet() -> str @Ask {
    let name = Ask::prompt("Name:")
    "Hello, {name}!"
}

pub fn run_greet() -> str {
    with Ask::prompt(_query) -> resume "Alice" -- Affine: resumed at most once
    greet()
}

-- 2. Delimited Early Abort with Deterministic LIFO Cleanup
type AuditLog = { mut entries: []str }
type Resource = { name: str, on_close: fn() -> () }

fn workflow(mut audit: AuditLog) -> str @Auth &mut {
    audit.entries !> Array::push("STEP_1")
    let scoped mut res = Resource.{
        name: "res",
        on_close: \-> { audit.entries !> Array::push("CLEANED") },
    }
    if !Auth::authenticate() { "Denied" } else { "Allowed" }
}

pub fn test_early_abort() {
    let mut audit = AuditLog.{ entries: [] }
    let res = {
        with Auth::authenticate() -> "Aborted" -- Early abort without resume
        workflow(mut audit)
    }
    assert(res == "Aborted")
    -- LIFO cleanup ran deterministically; prior write "STEP_1" remains committed
    assert(audit.entries == ["STEP_1", "CLEANED"])
}

-- 3. Totality and Finite Evaluation with Div
fn spin() -> int { loop {} }

halt fn bounded_execution() -> ?int {
    with Div::exhausted() -> None
    with Div::budget(10_000)               -- Fresh finite execution boundary
    Some(spin())
}
-- Evaluates to None when the fuel budget is exhausted
```

- **Affine Resumption**: `resume` is affine; calling it more than once (`E0610`) or escaping the arm (`E0611`) is statically rejected.
- **Delimited Early Abort**: Returning from an arm without `resume` safely aborts the protected computation, running `scoped` cleanups in LIFO order while preserving prior committed writes.
- **Finite Evaluation (`Div`)**: `Div::budget(limit)` bounds execution steps; fuel exhaustion triggers `Div::exhausted()` without undefined behavior. Functions certified to terminate use `halt fn`.

---

### Unified Tripartite Introspection and Metaprogramming

Compile-time introspection unifies records, sum types (ADTs), and tuples under a single coordinate model via `keyof T` and constituent projection `T.(K)`.

```ril
-- 1. Universal Coordinate Indexing (keyof T) & Projection (T.(K))
type User = { id: int, name: str, active: bool }
meta let USER_KEYS: []str = keyof User             -- ["active", "id", "name"] (UTF-8 sorted)
type UserName = User.("name")                      -- str

type UiEvent { Click({ x: int, y: int }), Hover(int, int), Focus }
meta let EVENT_KEYS: []str = keyof UiEvent         -- ["Click", "Focus", "Hover"]
type ClickPayload = UiEvent.Click                  -- { x: int, y: int }
type FocusPayload = UiEvent.Focus                  -- () (nullary injection domain)

type Pair = (int, str)
meta let PAIR_KEYS: []int = keyof Pair             -- [0, 1]
type First = Pair.0                                -- int

-- 2. Symmetrical Mapped Comprehensions
-- Generic visitor/handler table valid for BOTH records and sum types:
type HandlerTable = \T, R -> type<{
    [K in keyof T]: fn(T.(K)) -> R
}>
type UserHandlers = HandlerTable<User, ()>
-- Resolves to: { active: fn(bool) -> (), id: fn(int) -> (), name: fn(str) -> () }

-- Mapped tuple comprehension (e.g. compile-time tuple reversal):
halt type ReverseTuple = \T -> {
    let rev_indices = keyof T |> Array::reverse
    type<( [I in rev_indices]: T.(I) )>
}
type ReversedPair = ReverseTuple<Pair>             -- (str, int)

-- 3. Pure Type Functions and Structural Type Pattern Matching
type UnwrapOption = \T -> match type<T> {
    type<Option<let U>> -> type<U>,
    _ -> panic("UnwrapOption requires Option<T>"),
}
type Unwrapped = UnwrapOption<Option<int>>         -- int
```

- **Universal Coordinate Indexing**: `keyof T` returns canonically sorted field names (`[]str`) for records, constructor names (`[]str`) for sum types, and positional indices (`[]int`) for tuples.
- **Constituent Projection**: `T.(K)` statically retrieves field types, constructor payload types (under Constructor-Tuple Equivalence), or tuple components.
- **Symmetrical Mapped Comprehensions**: `{ [K in Expr]: TypeExpr }` and `( [I in Expr]: TypeExpr )` enable type-level maps, schema filtering, and tuple manipulations.
- **Pure Type Functions (`halt type`)**: First-class type computations parameterized by types or static values, with budget enforcement and compile-time custom diagnostics (`panic(message)`).

---

### Constructor-Tuple Equivalence

Data constructors establish an algebraic equivalence between multi-field variants and tuple payloads, eliminating artificial nesting.

```ril
-- Constructor argument parentheses absorb inner tuples (n >= 2):
let res1: Result<(int, str), str> = Ok(200, "OK")
let res2: Result<(int, str), str> = Ok((200, "OK"))    -- Definitionally equivalent to res1

-- Unit constructors (n = 0) vs Nullary tags:
let unit_res: Result<(), str> = Ok()                  -- Directly constructs () unit payload
let opt: Option<int> = None                           -- Pure nullary tag (None() rejected with E0353)

-- First-class constructors:
let make_ok: fn(int) -> Result<int, str> = Ok         -- First-class constructor function
```
