# Ril

```ril
-- Ril aims to turn part of software engineering's cognitive load into explicit markers.
-- State intent; the compiler derives and checks the resulting contracts.

type Counter = { var value: int }

fn increment(mut counter: Counter) &mut -> () {
    counter.value += 1
}

fn bindings() -> () {
    let base = Counter.{ value: 0 }          -- Deeply immutable.
    let mut counter = clone(base)           -- Writable interior.
    let ref observed = counter              -- Live observation.
    counter !> increment
    let ^mut shared = counter               -- Another writer.
    shared !> increment
    assert(observed.value == 2 && base.value == 0)
}
```

```ril
-- clone isolates a snapshot; derive updates immutable data through a confined draft.
fn snapshots() -> () {
    let mut working = Counter.{ value: 1 }
    let ref live = working
    let snapshot = clone(ref live)
    let updated = snapshot |> derive \mut draft -> { draft.value += 1 }
    working.value = 3
    assert(snapshot.value == 1 && updated.value == 2 && live.value == 3)
}
```

```ril
-- via parameterizes permissions; infer derives the result contract.
fn relay<T>(via value: T) -> infer T {
    let via item = value
    item
}

fn append<T>(mut xs: [via]T, via item: T) &mut -> () {
    xs !> Array::push(item)
}

fn construction() -> () {
    let mut cells: [mut]Counter = []
    let mut cell = Counter.{ value: 1 }
    append(mut cells, new cell)              -- Hand off the qualified construction path.
    -- cell.value                           -- E0549: source path ended.
}
```

```ril
-- Named state and surviving environments appear in callable contracts.
var visits = 0
fn record_visit() &up(sub){mut visits} -> () { visits += 1 }
fn visit() &record_visit -> () { record_visit() }

type Step = fn() &up -> int
fn make_step() &capture -> new Step {
    var count = 0
    \-> { count += 1; count }
}
```

```ril
-- @ declares effects; with handles them; resume continues at most once.
eff Ask { name() -> str }
fn greet() @Ask -> str { "Hello, {Ask::name()}!" }

fn greeting() -> str {
    with Ask::name() -> resume "Ril"
    greet()
}
```

```ril
-- scoped runs cleanup at scope exit, including abrupt exits.
type Resource = { mut on_close: fn() & -> () }
fn cleanup() -> bool {
    var closed = false
    {
        let scoped mut resource = Resource.{
            on_close: \-> { closed = true },
        }
    }
    closed
}

-- halt requires finite, outwardly pure computation; Div::budget bounds eligible work.
fn spin() -> int { loop {} }
halt fn bounded() -> ?int {
    with Div::exhausted() -> None
    with Div::budget(1_000)
    Some(spin())
}
```

```ril
-- meta and type functions compute schemas before execution.
type User = { id: int, var name: str }
meta let USER_KEYS = keyof User              -- ["id", "name"]
meta let NAME_MODE = modeof User.name        -- MemberMode::Var
type Readonly = \T -> <{ [keyof T as K]: T.(K) }>
type PublicUser = Readonly<User>             -- { id: int, name: str }

type UnwrapOption = \T -> match <T> {
    <Option<let U>> -> <U>,
    _ -> panic("expected Option<T>"),
}
type Item = UnwrapOption<Option<int>>        -- int
```

[SPEC](doc/SPEC.md)
