# Ril

Ril is a programming language designed to make data permissions flow explicitly through computation and remain fully traceable.

[language specification](doc/SPEC.md) 

```ril
-- Access-mode dependencies propagate through generic calls and local reception.
type Cell = .{ var value: i64 }

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
-- Function signatures record environment creation, sharing, and contained origins.
type Step = fn() &up -> i64
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
fn update_snapshot() -> () {
    let mut live = Cell.{ value: 1 }
    let snapshot = clone(ref live)
    live.value = 3

    let base = .{ left: snapshot, right: snapshot }
    var current = base
    current = current |> derive \mut draft -> { draft.left.value += 1 }
    assert(base.left.value == 1 && live.value == 3)
    assert(current.left.value == 2 && current.right.value == 1)
}
```

```ril
fn update_title<T: .{ title: str, .. }>(item: T, new_title: str) -> T {
    item |> derive \mut draft -> { draft.title = new_title }
}

fn revise_article() -> () {
    let article = .{ title: "old", published: true }
    let revised = update_title(article, "new")
    assert(article.title == "old" && revised.title == "new" && revised.published)
}
```

```ril
-- The budget bounds eligible computation; cleanup and recovery must also be finite.
fn spin() -> i64 { loop {} }
halt fn bounded() -> Result<i64, BudgetError> {
    with div_budget(1_000)
    spin()
}
```

```ril
-- Schema transformations preserve both slot replacement and access modes.
type Select = \T: .{ ..R }, keys: []str -> {
    let selected = coords(<T>) |> Array::filter(\(_, key) -> keys |> Array::contains(key))
    <.{ m [selected as (m, k)]: T.(k) }>
}
type Model = .{ id: i64, var title: str, mut rows: []i64 }
type Editable = Select<Model, ["title", "rows"]> -- .{ var title: str, mut rows: []i64 }
```
