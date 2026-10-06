# Ril

**Ril** is an expression-oriented, strongly typed programming language featuring algebraic effect handlers, capability-tracked state, and deterministic compilation to native machine code.

---

### 1. Algebraic Effects (`@Effect`)

```ril
pub effect Ask {
    prompt: fn(str) -> str
}

fn greet() -> str @Ask {
    "Hello, " + Ask::prompt("Name:")
}

-- Handled via one-shot delimited resumption
let message = {
    with Ask::prompt(_) -> resume("World")
    greet() -- "Hello, World"
}
```

### 2. Local Mutation Purity (`&mut`)

```ril
-- In-place mutation via mutating pipeline (!>)
fn append(mut list: []str, item: str) &mut {
    list !> push(item)
}

-- Frame-confined mutation is pure: &mut discharged locally
fn extract_valid(tags: []{ name: str, is_valid: bool }) -> []str {
    let mut result: []str = []
    for tags |> filter(\.is_valid) as t {
        append(mut result, t.name)
    }
    result -- pure signature: fn([]{ name: str, is_valid: bool }) -> []str
}
```

### 3. State Capabilities & Read-Only Handles (`&^mut`, `&capture`)

```ril
-- Retained mutable sharing: escaping aliased mutation requires &^mut
fn register(mut hub: Hub, mut listener: Listener) &^mut {
    hub.listeners !> push(listener)
}

-- External state access requires explicit capability annotation
let mut counter = 0
fn tick() -> int &{mut counter} {
    counter += 1
    counter
}

-- Publishing a writable capture of external state requires named sharing
fn share_counter() -> (fn() -> int &{mut counter}) &{^mut counter} {
    \-> { counter += 1; counter }
}
-- The returned closure mutates existing shared state; creating it retains
-- another writable path. ^mut counter includes mut counter.

-- Escaping stateful closures require &capture
pub fn make_step() -> (fn() -> int &capture) &capture {
    let mut n = 0
    \-> { n += 1; n }
}

-- `let` is a read-only handle; mutation requires a mutable handle `let mut`
let read_only = make_step()
-- read_only() -- STATIC ERROR: cannot invoke &capture through read-only handle

let mut active = make_step()
active()       -- OK: 1
```

---

See [SPECIFICATION.md](SPECIFICATION.md) for the formal language specification.


### 4. Recursive Data and Closure-Based Type Programming

```ril
type Tree<T> = { value: T, children: []Tree<T> }

halt type Box = \T -> type[{ value: T }]
type IntBox = Box(type[int])

halt fn read_box(value: Box(type[int])) -> int { value.value }
```

Type computations use static closures, with inferred results and ordinary closure syntax. `halt type` guarantees normal termination; an unmarked type closure permits broader pure static algorithms under compiler budgets and optional project lint restrictions. Static closures and runtime fn values cannot invoke or coerce into each other. Halt declarations reject ordinary computation dependencies, including in signatures and annotations.

The repository specifies a language design; these examples are specification examples, not verified compiler output. See [SYNTAX.md](SYNTAX.md) for syntax, [Chapter 12](spec/12_type_computation_and_proofs.md) for totality, static computation and boundary acceptance cases, and [the design rationale](spec/DESIGN_RATIONALE.md) for the design choices and limits.


### 5. Hidden Associated Types

```ril
type EncoderBox = {
    opaque type Item,
    value: Item,
    encode: fn(Item) -> bytes,
}
```

Generic parameters and hidden type witnesses are implicitly compile-time-only. The record carries runtime data and operations tied to one abstract Item; it does not store a runtime Type field. Examples focus on application/library patterns rather than proof-assistant programming.
