# Ril

**Ril** is an expression-oriented, strongly typed language with algebraic effects, immutable data, live read-only views, and explicit mutable-sharing capabilities.

The [specification](SPECIFICATION.md) defines the language. [Design rationale](DESIGN_RATIONALE.md) explains its choices.

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
```

Locally constructed data can enter `let` when no external writer survives. `mut` grants temporary writes; `^mut` explicitly permits retaining a writable reference. Shared origins still participate in exclusivity checks.

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
```

Callable types can abbreviate environment details while preserving inferred obligations. An explicit `fn() -> () @{} &{}` contract requires both rows to be closed.
