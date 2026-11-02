# Ril

Ril is a programming language designed to reduce manual reasoning about data access, state, effects, and termination through explicit markers and statically checked contracts.

```ril
-- Permission dependencies propagate through generic calls and local reception.
type Cell = { var value: int }

fn relay<T>(via value: T) -> infer T {
    let via item = value
    item
}

fn append<T>(mut xs: [via]T, via value: T) &mut -> () {
    xs !> Array::push(relay(value))
}

fn transfer() -> () {
    let mut cells: [mut]Cell = []
    let mut cell = Cell.{ value: 1 }
    append(mut cells, new cell)
    -- cell.value                           -- E0549: source path ended.
}
```

```ril
-- Callable contracts retain environment creation, sharing, and contained origins.
type Step = fn() &up -> int
fn make_shared_step(^mut cell: Cell)
    &capture &^mut &return{^mut cell} -> new Step {
    \-> { cell.value += 1; cell.value }
}

fn sharing() -> () {
    let mut cell = Cell.{ value: 0 }
    let ^mut step = make_shared_step(^mut cell)
    assert(step() == 1)
    cell.value += 1
    assert(step() == 3)
}

var visits = 0
fn record_visit() &up(sub){mut visits} -> () { visits += 1 }
fn visit() &record_visit -> () { record_visit() } -- Inherit verified named state.
```

```ril
-- Functional updates preserve graph aliases while confining draft mutation.
type Pair = { left: Cell, right: Cell }
fn update_graph() -> () {
    let cell = Cell.{ value: 1 }
    let base = Pair.{ left: cell, right: cell }
    let updated = base |> derive \mut draft -> { draft.left.value += 1 }
    assert(base.right.value == 1 && updated.right.value == 2)
}
```

```ril
-- A checked budget makes eligible unbounded work usable in a finite, pure contract.
fn spin() -> int { loop {} }
halt fn bounded() -> ?int {
    with Div::exhausted() -> None
    with Div::budget(1_000)
    Some(spin())
}
```

```ril
-- Schema transformations preserve both slot replacement and access modes.
type Select = \T: { ..R }, keys: []str -> {
    let selected = keyof T |> Array::filter(\key -> keys |> Array::contains(key))
    <{ modeof T.(K) [selected as K]: T.(K) }>
}
type Model = { id: int, var title: str, mut rows: []int }
type Editable = Select<Model, ["title", "rows"]> -- { var title: str, mut rows: []int }
```

[SPEC](doc/SPEC.md)
