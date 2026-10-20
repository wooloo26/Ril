# Ril

**Ril** is an expression-oriented, strongly typed language with algebraic effects, immutable data, live read-only views, and explicit mutable-sharing capabilities.

### Immutable values and live views

```ril
type Document = { mut title: str }

pub fn test_views() {
    let document = Document.{ title: "Guide" }
    let alias = document
    let mut working = clone(document)
    let view observed = working
    let view read_title = \-> observed.title
    working.title = "Draft"
    assert(alias.title == "Guide")
    assert(read_title() == "Draft")

    let snapshot = clone_immut(observed)
    let revised = snapshot |> derive \mut draft -> {
        draft.title = "Revised"
    }
    assert(snapshot.title == "Draft" && revised.title == "Revised")
}
```

`let` guarantees immutable data, not unique ownership. `let view` can observe changes but cannot supply mutable authority. Deep cloning isolates ordinary data; `derive` shares only immutable data and confines its writable draft.

### Effects and stable handlers

```ril
pub eff Ask { prompt(str) -> str }

fn greet() -> str @Ask {
    let name = Ask::prompt("Name:")
    "Hello, {name}"
}

pub fn greeting() -> str {
    with Ask::prompt(_question) -> resume "World"
    greet()
}
```

Effects and closure obligations can flow through higher-order calls. Each invocation still needs a stable handler and the required access permissions; forwarding does not change parameter modes.

### Reassignment and interior writes

```ril
type Cell = { mut count: int }

pub fn test_slots() {
    var selected = Cell.{ count: 0 }
    selected = Cell.{ count: 1 }
    -- selected.count += 1             -- Error [E0520]: var alone grants no interior write authority

    var mut working = Cell.{ count: 0 }
    working.count += 1
    working = Cell.{ count: 2 }
    assert(working.count == 2)
}
```

`var` permits slot reassignment. `var mut` also permits interior writes when the value's origins grant them; it cannot turn an immutable value or live view into writable data. Both the reassignable slot and interior/environment authority must be exercised; use `let mut` when only pinned interior authority is needed.

### Local mutation and explicit retained sharing

```ril
pub fn numbers() -> []int {
    let mut result: []int = []
    result !> Array::push(1)
    result
}

type Entry = { mut id: int }
type Hub = { mut entries: []Entry }

fn register(mut hub: Hub, ^mut entry: Entry) &^mut {
    hub.entries !> Array::push(^mut entry)
}

pub fn test_local_sharing() {
    let mut entry = Entry.{ id: 1 }
    -- let mut hidden = entry          -- Error [E0510]: another writable authority needs ^mut
    let mut alias = ^mut entry
    alias.id = 2
    entry.id = 3
    assert(alias.id == 3)

    let mut pair = (^mut entry, ^mut entry)
    pair.0.id = 4
    assert(pair.1.id == 4)
}
```

Locally constructed data can enter `let` when no external writer survives. `mut` grants temporary writes; `^mut` explicitly marks retention or another writable authority to an existing value, including local aliases and aggregate members. It preserves existing permissions and never manufactures them. Shared origins still participate in exclusivity checks; different names or tuple positions do not prove independence.

### Stateful closures

```ril
type Step = fn() -> int &closure

pub fn make_step() -> Step &capture {
    var count = 0
    \-> { count += 1; count }
}

fn invoke(mut step: Step) -> int &mut { step() }

pub fn test_step() {
    let mut step = make_step()
    assert(invoke(mut step) == 1)
    -- let immutable = step -- Error [E0535]: a mutable environment cannot become immutable data
}

pub fn test_shared_step() {
    let mut cell = Cell.{ count: 0 }
    let mut step = \-> { cell.count += 1; cell.count }
    assert(step() == 1)
    cell.count += 1
    assert(step() == 3)

    let view observed = cell
    -- let mut forged = ^mut observed  -- Error [E0520]: the marker cannot supply missing write authority
}
```

Callable types abbreviate environment details while preserving inferred obligations.

Lexical capture is inferred, and the machine tracks the sharing between `cell` and `step`. Escaping captures still obey the factory's `&capture`, `&^mut`, and parameter contracts. Calling an existing shared closure again does not create another sharing event.

### Captured source groups

```ril
fn make_named_step(increment: int) -> Step &capture {
    var count = 0
    step
    where
        fn step() -> int &{closure, increment, mut count} {
            count += increment
            count
        }
}
```

Each captured group names bindings from one enclosing function or lambda layer. The immediate layer can omit its name; a farther named layer uses a header such as `closure make_outer`. Farther anonymous layers still use `closure`, with separate groups for different layers. A nonempty group without that header, such as `&{config, mut cache}`, names module storage. The grouping never merges binding identities, dynamic environments, or aliased objects. `&capture` and standalone `&^mut` stay separate.

### Public state contracts

```ril
-- counter.ril
var private_count = 0
pub fn advance() &{mut private_count} { private_count += 1 }

-- client.ril
use counter
fn wrapper() &Counter::advance { Counter::advance() }
-- fn hidden() { Counter::advance() } -- Error [E0510]: concrete inherited state is undeclared
```

`&Counter::advance` references that function's verified concrete named state without exporting its private variables. It is available on ordinary named function definitions; it does not replace direct storage annotations or include effects, parameter permissions, `&capture`, or standalone `&^mut`. Anonymous functions and callable types keep their existing inference and contract forms.

### Complete tracking, compact source

```ril
var count = 0
fn read_count() -> int &{count} { count }
fn advance() &{mut count} { count += 1 }

fn invoke_action(action: fn() -> ()) { action() }
fn explicit_wrapper() &advance { invoke_action(advance) }
-- fn hidden_wrapper() { invoke_action(advance) } -- Error [E0510]: this callback is already known
fn invoke_pure(action: fn() -> ()) @{} &{} { action() }
-- invoke_pure(advance)              -- Error [E0534]: the total state is not empty

fn check_choice(choose_write: bool) {
    let action = if choose_write { advance } else { \-> () }
    -- invoke_pure(action)
    -- Error [E0534]: the possible external write survives the run-time branch
}
```

`&{count}` grants read-only access to the module binding; it does not claim that `count` is immutable. The machine tracks actual origins, permissions, live observations, captured environments, sharing, and effects through ordinary returns and higher-order calls. Source annotations may omit inferred details without weakening the concrete declarations required by named definitions.

Complete tracking preserves those facts under the specified conservative judgments; it does not predict arbitrary run-time behavior exactly. Unknown facts cannot establish independence, purity, or absence of escape.

The machine must retain complete traceable facts; diagnostics can display them on demand and show the source-to-use chain that caused a conflict, including aliases, captures, handlers, and retained references. They distinguish missing annotations from semantic conflicts: adding an annotation cannot authorize a forbidden write, hide overlapping access, or make a live reference immutable.
