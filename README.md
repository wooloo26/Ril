# Ril

**Ril** is an expression-oriented, strongly typed programming language featuring algebraic effect handlers, capability-tracked state, and deterministic compilation to native machine code.

---

### 1. Algebraic Effects (`@Effect`)

```ril
pub eff Ask {
    prompt(str) -> str,
}

fn greet() -> str @Ask {
    "Hello, " + Ask::prompt("Name:")
}

-- Handled via one-shot delimited resumption
let message = {
    with Ask::prompt(_) -> resume "World"
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

-- Escaping stateful closures require &capture; returned callable carries &closure
pub fn make_step() -> (fn() -> int &closure) &capture {
    let mut n = 0
    \-> { n += 1; n }
}

-- `let` is a read-only handle; mutation requires a mutable handle `let mut`
let read_only = make_step()
-- read_only() -- STATIC ERROR [E0520]: cannot invoke mutable-capturing closure through read-only handle

let mut active = make_step()
active()       -- OK: 1
```

---

See [SPECIFICATION.md](SPECIFICATION.md) for the authoritative, code-first language specification, and [DESIGN_RATIONALE.md](DESIGN_RATIONALE.md) for architectural design rationale.
