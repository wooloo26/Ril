# Ril

Ril is a programming language designed to make data access authority flow explicitly through computation and remain fully traceable.

[language specification](doc/SPEC.md)

```ril
-- Access-mode dependencies propagate through generic calls and local reception.
type Cell = .{ var value: int }

fn relay<T>(via value: T) -> infer T {
    let via item = value
    item
}

fn make_cells() -> new []Cell { [Cell.{ value: 1 }] }

fn receive_cells() -> () {
    let mut cells: [mut]Cell = make_cells() -- New elements receive writable access.
    cells |> mut Array::push(relay({
        let mut cell = Cell.{ value: 2 }
        cell.value += 1
        cell                                -- Promotes to unbound 'new Cell' on block exit.
    }))
    assert(cells[0].value == 1 && cells[1].value == 3)
}
```

```ril
-- New containers preserve the sources of nested shared objects.
type Cell = .{ var value: int }
type Shelf = .{ mut rows: [^mut]Cell }
fn shared_shelf(^mut cell: Cell) &^mut &return(^mut cell) -> new Shelf {
    Shelf.{ rows: [^mut cell] }
}

fn nested_sources() -> () {
    let mut cell = Cell.{ value: 0 }
    let mut shelf = shared_shelf(^mut cell)
    shelf.rows[0].value += 1
    assert(cell.value == 1)                 -- The nested Cell still shares its source.
    -- let frozen = shared_shelf(^mut cell) -- E0535: surviving outside writer.
}
```

```ril
-- A new closure records its environment and captured shared source.
type Cell = .{ var value: int }
type Step = fn() &up -> int
fn make_shared_step(^mut cell: Cell)
    &capture &^mut &return(^mut cell) -> new Step {
    \-> { cell.value += 1; cell.value }
}

fn sharing() -> () {
    let mut cell = Cell.{ value: 0 }
    let ^mut step = make_shared_step(^mut cell)
    assert(step() == 1)
    cell.value += 1
    assert(step() == 3)
}
```

```ril
type Cell = .{ var value: int }
fn update_snapshot() -> () {
    let mut live = Cell.{ value: 1 }
    let snapshot = clone(ref live)
    live.value = 3

    let base = .{ left: snapshot, right: snapshot }
    var current = base
    current = current |> derive \mut d -> { d.left.value += 1 }
    assert(base.left.value == 1 && live.value == 3)
    assert(current.left.value == 2 && current.right.value == 1)
}
```

```ril
-- Effect handlers dispatch dynamically; statement 'with' governs the rest of the block.
eff Clock { fn now_ms() -> int }
fn timestamp() @Clock -> str { "time={Clock::now_ms()}" }

fn virtual_time() -> str {
    with Clock::now_ms = \-> 1700
    timestamp()
}
```

```ril
-- One-shot algebraic effects ('ctl') compose without function coloring,
-- and unwinding a continuation deterministically runs active 'defer' cleanups.
eff Yield<T> { ctl emit(value: T) -> () }

fn first_three_doubled(xs: []int) -> new []int {
    let mut out: []int = []
    let mut trace: []str = []
    with {
        ctl Yield<int>::emit = \v, k -> {
            out |> mut Array::push(v)
            if len(ref out) < 3 { k() } else { unwind_ctl(k) }
        }

        defer trace |> mut Array::push("cleanup")
        let _ = xs |> Array::map \x -> { Yield<int>::emit(x * 2); x }
    }
    assert(trace == ["cleanup"])
    out
}
```

```ril
-- Schema transformations preserve both slot replacement and access modes.
type Select = \T: .{ .. }, keys: []str -> {
    let selected = Reflect::fields(<T>) |> Array::filter(\(_, key) -> keys |> Array::contains(key))
    <.{ m [selected as (m, k)]: T.(k) }>
}
type Model = .{ id: int, var title: str, mut rows: []int }
type Editable = Select<Model, ["title", "rows"]> -- .{ var title: str, mut rows: []int }
```
