#![forbid(unsafe_code)]

use std::{
    collections::BTreeSet,
    ffi::OsStr,
    fs,
    io::Write,
    path::Path,
    process::{Command, Stdio},
};

use ril_driver::Driver;
use ril_sema::{
    access::{Access, horn},
    iface::{FORMAT_VERSION, Interface},
};
use ril_test::{CaseMode, Stage, TestDriver, Unit, VirtualPackage, parse_suite, run_worker};

#[test]
fn hidden_clone_restrictions_survive_separate_compilation() {
    let source = b"pub opaque type Parcel(.{ mut cont: ctl() -> () })";
    let mut library = VirtualPackage::new(Unit::Lib);
    library.entry = "pkg/vault.ril".into();
    library.insert(library.entry.clone(), source.to_vec());
    let interface = Driver.interface(&library).unwrap().encode().unwrap();
    for (mount, bytes) in [
        ("library/vault.ril", source.as_slice()),
        ("library/vault.rili", interface.as_slice()),
    ] {
        let mut client = VirtualPackage::new(Unit::Lib);
        client.insert(mount.into(), bytes.to_vec());
        client.insert(
            client.entry.clone(),
            b"use library/vault\nfn duplicate(ref value: Vault::Parcel) -> new Vault::Parcel { clone(ref value) }"
                .to_vec(),
        );
        let checked = Driver.check(&client, Stage::Type);
        assert_eq!(
            checked.result.diagnostics.len(),
            1,
            "{mount}: {:?}",
            checked.result.diagnostics
        );
        assert_eq!(
            checked.result.diagnostics[0].code,
            Some(ril_source::diag::Code::E0301),
            "{mount}"
        );
    }
}

#[test]
fn generic_clone_domain_survives_separate_compilation() {
    let source = b"pub fn duplicate<T: []int>(value: T) -> new T { clone(value) }";
    let mut library = VirtualPackage::new(Unit::Lib);
    library.entry = "pkg/copy.ril".into();
    library.insert(library.entry.clone(), source.to_vec());
    let interface = Driver.interface(&library).unwrap().encode().unwrap();
    for (mount, bytes) in [
        ("library/copy.ril", source.as_slice()),
        ("library/copy.rili", interface.as_slice()),
    ] {
        for (ty, expected) in [
            ("[]int", None),
            ("int", Some(ril_source::diag::Code::E0306)),
        ] {
            let mut client = VirtualPackage::new(Unit::Lib);
            client.insert(mount.into(), bytes.to_vec());
            client.insert(
                client.entry.clone(),
                format!(
                    "use library/copy\nfn run(value: {ty}) -> new {ty} {{ Copy::duplicate(value) }}"
                )
                .into_bytes(),
            );
            let checked = Driver.check(&client, Stage::Type);
            let codes: Vec<_> = checked.result.diagnostics.iter().map(|d| d.code).collect();
            let expected: Vec<_> = expected.into_iter().map(Some).collect();
            assert_eq!(codes, expected, "{mount} with {ty}");
        }
    }
}

#[test]
fn transferred_snapshot_requirements_survive_separate_compilation() {
    use ril_sema::access::{Coordinate, SnapshotInput};
    use ril_source::diag::Code;

    let source = br#"
pub type Cell = .{ var count: int }
pub type Shelf = .{ var ^mut item: Cell }
pub fn freeze(new input: Shelf) -> Shelf { let snapshot = new input; snapshot }
pub fn replace(new input: Shelf) -> Shelf {
    let mut shelf = new input
    shelf.item = ^mut Cell.{ count: 42 }
    let snapshot = new shelf
    snapshot
}
"#;
    let mut provider = VirtualPackage::new(Unit::Lib);
    provider.entry = "pkg/snapshot.ril".into();
    provider.insert(provider.entry.clone(), source.to_vec());
    let interface = Driver.interface(&provider).unwrap().encode().unwrap();
    let decoded = Interface::decode(&interface).unwrap();
    for (name, replaced) in [
        ("freeze", Vec::new()),
        ("replace", vec![vec![Coordinate::Field("item".into())]]),
    ] {
        let export = &decoded.functions[&format!("pkg/snapshot.ril::{name}")];
        let expected = [SnapshotInput {
            formal: 0,
            path: Vec::new(),
            replaced,
        }];
        assert_eq!(export.summary.snapshot_inputs, expected);
        for row in &export.domain {
            assert_eq!(row.summary.snapshot_inputs, expected);
        }
    }
    for (mount, bytes) in [
        ("library/snapshot.ril", source.as_slice()),
        ("library/snapshot.rili", interface.as_slice()),
    ] {
        for (name, alias, accepted) in [
            ("freeze", "live", false),
            ("freeze", "Snapshot::Cell.{ count: 1 }", true),
            ("replace", "live", true),
        ] {
            let client_source = format!(
                "use library/snapshot
fn relay(new input: Snapshot::Shelf) -> Snapshot::Shelf {{
    let transform = Snapshot::{name}
    transform(new input)
}}
fn run() -> int {{
    let mut live = Snapshot::Cell.{{ count: 1 }}
    live.count += 1
    let frozen = relay(new Snapshot::Shelf.{{ item: ^mut {alias} }})
    live.count += 8
    frozen.item.count + live.count
}}"
            );
            let mut client = VirtualPackage::new(Unit::Lib);
            client.insert(mount.into(), bytes.to_vec());
            client.insert(client.entry.clone(), client_source.into_bytes());
            if accepted {
                assert!(Driver.analyze(&client).is_ok(), "{mount} {name} {alias}");
            } else {
                let diagnostics = Driver.analyze(&client).err().unwrap();
                assert_eq!(
                    diagnostics.len(),
                    1,
                    "{mount} {name} {alias}: {diagnostics:?}"
                );
                assert_eq!(diagnostics[0].code, Some(Code::E0535));
            }
        }
    }
}

#[test]
fn snapshot_callback_arguments_survive_separate_compilation() {
    use ril_source::diag::Code;

    let source = br#"
pub type Cell = .{ var count: int }
pub type Shelf = .{ var ^mut item: Cell }
type Action = fn(new Shelf) -> int
fn dispatch(action: Action, new source: Shelf) -> int { action(new source); 0 }
pub fn apply(action: fn(new Shelf) -> int, new source: Shelf) -> int {
    dispatch(action, new source)
}
pub fn replace_then_apply(action: fn(new Shelf) -> int, new source: Shelf) -> int {
    let mut shelf = new source
    shelf.item = ^mut Cell.{ count: 42 }
    dispatch(action, new shelf)
}
pub fn apply_via(action: fn(via Shelf) -> int, via source: Shelf) -> int {
    action(source)
}
"#;
    let mut provider = VirtualPackage::new(Unit::Lib);
    provider.entry = "pkg/snapshot.ril".into();
    provider.insert(provider.entry.clone(), source.to_vec());
    let interface = Driver.interface(&provider).unwrap().encode().unwrap();
    let decoded = Interface::decode(&interface).unwrap();
    let [invocation] = decoded.functions["pkg/snapshot.ril::apply"]
        .summary
        .snapshot_calls
        .as_slice()
    else {
        panic!("the callback invocation must be published");
    };
    assert_eq!(invocation.receiver.parameter, 0);
    assert_eq!(
        invocation.arguments[0].graph.roots[0]
            .source
            .as_ref()
            .unwrap()
            .parameter,
        1
    );

    for (mount, bytes) in [
        ("library/snapshot.ril", source.as_slice()),
        ("library/snapshot.rili", interface.as_slice()),
    ] {
        for (method, callback, item, accepted) in [
            ("apply", "count", "live", true),
            ("apply", "freeze", "live", false),
            ("apply", "freeze", "Snapshot::Cell.{ count: 42 }", true),
            ("replace_then_apply", "freeze", "live", true),
            ("apply_via", "count_via", "live", true),
            (
                "apply_via",
                "count_via",
                "Snapshot::Cell.{ count: 42 }",
                true,
            ),
        ] {
            let client_source = format!(
                "use library/snapshot
fn count(new source: Snapshot::Shelf) -> int {{ source.item.count }}
fn count_via(via source: Snapshot::Shelf) -> int {{ source.item.count }}
fn freeze(new source: Snapshot::Shelf) -> int {{ let snapshot = new source; snapshot.item.count }}
fn relay(new input: Snapshot::Shelf) -> int {{ Snapshot::{method}({callback}, new input) }}
fn run() -> int {{
    let mut live = Snapshot::Cell.{{ count: 1 }}
    live.count += 1
    let count = relay(new Snapshot::Shelf.{{ item: ^mut {item} }})
    live.count += 8
    count + live.count
}}"
            );
            let mut client = VirtualPackage::new(Unit::Lib);
            client.insert(mount.into(), bytes.to_vec());
            client.insert(client.entry.clone(), client_source.into_bytes());
            match (accepted, Driver.analyze(&client)) {
                (true, Ok(_)) => {}
                (false, Err(diagnostics)) => {
                    assert_eq!(
                        diagnostics.len(),
                        1,
                        "{mount} {callback} {item}: {diagnostics:?}"
                    );
                    assert_eq!(diagnostics[0].code, Some(Code::E0535));
                }
                (true, Err(diagnostics)) => panic!("{mount} {callback} {item}: {diagnostics:?}"),
                (false, Ok(_)) => panic!("{mount} accepted {callback} with {item}"),
            }
        }
    }
}

#[test]
fn private_snapshot_providers_survive_nested_callbacks_across_an_interface() {
    use ril_source::diag::Code;

    let source = br#"
pub type Cell = .{ var count: int }
pub type Shelf = .{ ^mut item: Cell }
pub type Leaf = fn(new Shelf) -> int
pub type Relay = fn(Leaf, new Shelf) -> int
fn freeze_impl(new shelf: Shelf) -> int { let fixed = new shelf; fixed.item.count }
fn freeze(new shelf: Shelf) -> int { freeze_impl(new shelf) }
fn relay(action: Leaf, new shelf: Shelf) -> int { action(new shelf) }
pub fn supply(action: fn(Relay, Leaf, new Shelf) -> int, new shelf: Shelf) -> int {
    action(relay, freeze, new shelf)
}
pub fn supply_closure(action: fn(Leaf, new Shelf) -> int, new shelf: Shelf) -> int {
    action(\new input: Shelf -> { let fixed = new input; fixed.item.count }, new shelf)
}
"#;
    let mut provider = VirtualPackage::new(Unit::Lib);
    provider.entry = "pkg/snapshot.ril".into();
    provider.insert(provider.entry.clone(), source.to_vec());
    let interface = Driver.interface(&provider).unwrap();
    assert_eq!(interface.functions.len(), 2);
    let contracts = &interface.functions["pkg/snapshot.ril::supply"]
        .summary
        .snapshot_providers;
    assert_eq!(contracts.len(), 2);
    assert!(contracts.iter().any(|provider| provider.inputs.len() == 1));
    assert!(contracts.iter().any(|provider| provider.calls.len() == 1));
    let interface = interface.encode().unwrap();

    for (mount, bytes) in [
        ("library/snapshot.ril", source.as_slice()),
        ("library/snapshot.rili", interface.as_slice()),
    ] {
        let mut client = VirtualPackage::new(Unit::Lib);
        client.insert(mount.into(), bytes.to_vec());
        client.insert(client.entry.clone(), br#"
use library/snapshot
fn test() -> int { Snapshot::freeze(new Snapshot::Shelf.{ item: ^mut Snapshot::Cell.{ count: 42 } }) }
"#.to_vec());
        let diagnostics = Driver.analyze(&client).err().unwrap();
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == Some(Code::E0201))
        );
        for (method, callable) in [("supply", "forward"), ("supply_closure", "dispatch")] {
            for (item, accepted) in [("live", false), ("Snapshot::Cell.{ count: 42 }", true)] {
                let source = format!(
                    "use library/snapshot
type Leaf = fn(new Snapshot::Shelf) -> int
fn dispatch(action: Leaf, new shelf: Snapshot::Shelf) -> int {{ action(new shelf) }}
fn forward(relay: fn(Leaf, new Snapshot::Shelf) -> int, action: Leaf, new shelf: Snapshot::Shelf) -> int {{
    relay(action, new shelf)
}}
fn test() -> int {{
    let mut live = Snapshot::Cell.{{ count: 1 }}
    live.count += 1
    let count = Snapshot::{method}({callable}, new Snapshot::Shelf.{{ item: ^mut {item} }})
    live.count += 8
    count + live.count
}}"
                );
                let mut client = VirtualPackage::new(Unit::Lib);
                client.insert(mount.into(), bytes.to_vec());
                client.insert(client.entry.clone(), source.into_bytes());
                match (accepted, Driver.analyze(&client)) {
                    (true, Ok(_)) => {}
                    (false, Err(diagnostics)) => {
                        assert_eq!(
                            diagnostics.len(),
                            1,
                            "{mount} {method} {item}: {diagnostics:?}"
                        );
                        assert_eq!(diagnostics[0].code, Some(Code::E0535));
                    }
                    (true, Err(diagnostics)) => panic!("{mount} {method} {item}: {diagnostics:?}"),
                    (false, Ok(_)) => panic!("{mount} accepted {method} with {item}"),
                }
            }
        }
    }
}

#[test]
fn callback_snapshot_contracts_can_take_live_inputs_before_constructing_a_graph() {
    use ril_source::diag::Code;

    let source = br#"
pub type Cell = .{ var count: int }
pub type View = .{ ref item: Cell }
pub type Leaf = fn(new View) -> int
fn freeze(new view: View) -> int { let fixed = new view; fixed.item.count }
fn count(new view: View) -> int { view.item.count }
pub fn check(action: fn(Leaf, ref Cell) -> int, ref cell: Cell) -> int { action(freeze, ref cell) }
pub fn read(action: fn(Leaf, ref Cell) -> int, ref cell: Cell) -> int { action(count, ref cell) }
"#;
    let mut provider = VirtualPackage::new(Unit::Lib);
    provider.entry = "pkg/snapshot.ril".into();
    provider.insert(provider.entry.clone(), source.to_vec());
    let interface = Driver.interface(&provider).unwrap().encode().unwrap();
    for (mount, bytes) in [
        ("library/snapshot.ril", source.as_slice()),
        ("library/snapshot.rili", interface.as_slice()),
    ] {
        for (method, accepted) in [("read", true), ("check", false)] {
            let source = format!(
                "use library/snapshot
fn dispatch(action: Snapshot::Leaf, ref live: Snapshot::Cell) -> int {{
    action(new Snapshot::View.{{ item: ref live }})
}}
fn run() -> int {{
    let mut live = Snapshot::Cell.{{ count: 1 }}
    live.count += 1
    Snapshot::{method}(dispatch, ref live)
}}"
            );
            let mut client = VirtualPackage::new(Unit::Lib);
            client.insert(mount.into(), bytes.to_vec());
            client.insert(client.entry.clone(), source.into_bytes());
            match (accepted, Driver.analyze(&client)) {
                (true, Ok(_)) => {}
                (false, Err(diagnostics)) => {
                    assert_eq!(diagnostics.len(), 1, "{mount} {method}: {diagnostics:?}");
                    assert_eq!(diagnostics[0].code, Some(Code::E0535));
                }
                (true, Err(diagnostics)) => panic!("{mount} {method}: {diagnostics:?}"),
                (false, Ok(_)) => panic!("{mount} accepted {method} with a live view"),
            }
        }
    }
}

#[test]
fn returned_and_stored_snapshot_callables_survive_separate_compilation() {
    use ril_source::diag::Code;

    let source = br#"
pub type Cell = .{ var count: int }
pub type Shelf = .{ ^mut item: Cell }
pub type Leaf = fn(new Shelf) -> int
pub type Slot = .{ var action: Leaf }
pub type Frame = .{ var action: Leaf, stamp: int }
pub type Writer = fn() &up -> ()
pub type ReadAfter = fn(mut Slot, fn(mut Slot) &mut -> ()) &mut -> Leaf
pub type Controls = .{ ^mut select: Writer, ^mut store: Writer }
fn freeze(new shelf: Shelf) -> int { let fixed = new shelf; fixed.item.count }
fn count(new shelf: Shelf) -> int { shelf.item.count }
fn make_private() -> Leaf { freeze }
fn make_with_private(make: fn(Leaf) -> Leaf) -> Leaf { make(freeze) }
pub fn make() -> Leaf { freeze }
pub fn factory() -> fn() -> Leaf { make_private }
pub fn factory_with() -> fn(fn(Leaf) -> Leaf) -> Leaf { make_with_private }
pub fn read() -> Leaf { count }
pub fn nested() -> .{ actions: []Leaf } { let fixed = .{ actions: [freeze] }; fixed }
pub fn identity(action: Leaf) -> Leaf { action }
pub fn from_callback(make: fn() -> Leaf) -> Leaf { make() }
pub fn from_callback_with(make: fn(Leaf) -> Leaf) -> Leaf { make(freeze) }
pub fn apply(make: fn() -> Leaf, new shelf: Shelf) -> int { make()(new shelf) }
pub fn apply_with(make: fn(Leaf) -> Leaf, new shelf: Shelf) -> int { make(freeze)(new shelf) }
pub fn install(mut slot: Slot) &mut -> () { slot.action = freeze }
pub fn append(mut actions: []Leaf) &mut -> () { Array::push(mut actions, freeze) }
pub fn appender(^mut actions: []Leaf) &capture &^mut &return(^mut actions) -> new Writer {
    \-> Array::push(mut actions, freeze)
}
pub fn invoke(mut action: Writer) &mut -> () { action() }
pub fn repeat(mut action: Writer, times: int) &mut -> () {
    for 0..times as _ { action() }
}
pub fn maybe_invoke(mut action: Writer, condition: bool) &mut -> () {
    if condition { action() }
}
pub fn reset(mut slot: Slot, install: fn(mut Slot) &mut -> ()) &mut -> () {
    install(mut slot)
    slot.action = count
}
pub fn reset_then_install(mut slot: Slot, install: fn(mut Slot) &mut -> ()) &mut -> () {
    slot.action = count
    install(mut slot)
}
pub fn read_after(mut slot: Slot, install: fn(mut Slot) &mut -> ()) &mut -> Leaf {
    install(mut slot)
    slot.action
}
pub fn invoke_after(mut slot: Slot, install: fn(mut Slot) &mut -> (), new input: Shelf) &mut -> int {
    install(mut slot)
    slot.action(new input)
}
pub fn read_before(mut slot: Slot, install: fn(mut Slot) &mut -> ()) &mut -> Leaf {
    let saved = slot.action
    install(mut slot)
    saved
}
pub fn read_between(mut slot: Slot, install: fn(mut Slot) &mut -> ()) &mut -> Leaf {
    install(mut slot)
    let saved = slot.action
    slot.action = count
    saved
}
pub fn destructure_after(mut slot: Slot, install: fn(mut Slot) &mut -> ()) &mut -> Leaf {
    install(mut slot)
    let .{ action } = slot
    action
}
pub fn read_either(mut slot: Slot, install: fn(mut Slot) &mut -> (), flag: bool) &mut -> Leaf {
    let saved = slot.action
    install(mut slot)
    if flag { saved } else { slot.action }
}
pub fn array_after(mut actions: []Leaf, install: fn(mut []Leaf) &mut -> ()) &mut -> Leaf {
    install(mut actions)
    actions[1]
}
pub fn slice_after(mut actions: []Leaf, install: fn(mut []Leaf) &mut -> ()) &mut -> Leaf {
    install(mut actions)
    let selected = actions[1..2]
    selected[0]
}
pub fn rest_after(mut actions: []Leaf, install: fn(mut []Leaf) &mut -> ()) &mut -> Leaf {
    install(mut actions)
    let [_, ..selected] = actions else { panic("missing first") }
    selected[0]
}
pub fn make_reader() -> ReadAfter {
    \mut slot: Slot, install: fn(mut Slot) &mut -> () -> { install(mut slot); slot.action }
}
pub fn copy_to(^mut slot: Slot, action: Leaf) &capture &^mut &return(^mut slot, action) -> new Writer {
    \-> { slot.action = action }
}
pub fn controls(^mut slot: Slot, initial: Leaf, next: Leaf) &capture &^mut &return(^mut slot, initial, next) -> new Controls {
    var action: Leaf = count
    action = initial
    Controls.{ select: \-> { action = next }, store: \-> { slot.action = action } }
}
pub fn build_array() -> []Leaf {
    let mut actions = [count]
    Array::push(mut actions, freeze)
    let fixed = new actions
    fixed
}
pub fn section(actions: []Leaf) &return(actions) -> new []Leaf { actions[1..] }
pub fn one(actions: []Leaf) &return(actions) -> new []Leaf { actions[1..2] }
pub fn stamp(base: Frame) -> Frame { derive(base) \mut d -> { d.stamp = 42 } }
pub fn freeze_frame(base: Frame) -> Frame { derive(base) \mut d -> { d.action = freeze } }
pub fn read_frame(base: Frame) -> Frame { derive(base) \mut d -> { d.action = count } }
"#;
    let mut library = VirtualPackage::new(Unit::Lib);
    library.entry = "pkg/snapshot.ril".into();
    library.insert(library.entry.clone(), source.to_vec());
    let interface = Driver.interface(&library).unwrap().encode().unwrap();
    let wrapper = br#"
use library/snapshot
pub fn invoke(mut action: Snapshot::Writer) &mut -> () { Snapshot::invoke(mut action) }
pub fn read_after(mut slot: Snapshot::Slot, install: fn(mut Snapshot::Slot) &mut -> ()) &mut -> Snapshot::Leaf {
    Snapshot::read_after(mut slot, install)
}
pub fn appender(^mut actions: []Snapshot::Leaf) &capture &^mut &return(^mut actions) -> new Snapshot::Writer {
    Snapshot::appender(^mut actions)
}
pub fn copy_to(^mut slot: Snapshot::Slot, action: Snapshot::Leaf) &capture &^mut &return(^mut slot, action) -> new Snapshot::Writer {
    Snapshot::copy_to(^mut slot, action)
}
pub fn controls(^mut slot: Snapshot::Slot, initial: Snapshot::Leaf, next: Snapshot::Leaf) &capture &^mut &return(^mut slot, initial, next) -> new Snapshot::Controls {
    Snapshot::controls(^mut slot, initial, next)
}
"#;
    let mut forwarding = VirtualPackage::new(Unit::Lib);
    forwarding.entry = "pkg/forwarding.ril".into();
    forwarding.insert(forwarding.entry.clone(), wrapper.to_vec());
    forwarding.insert("library/snapshot.rili".into(), interface.clone());
    let forwarded = Driver.interface(&forwarding).unwrap().encode().unwrap();
    for (mount, bytes) in [
        ("library/snapshot.ril", source.as_slice()),
        ("library/snapshot.rili", interface.as_slice()),
    ] {
        for (pick, freezing) in [
            ("Snapshot::make()", true),
            ("Snapshot::factory()()", true),
            ("Snapshot::factory_with()(keep)", true),
            ("Snapshot::read()", false),
            ("Snapshot::nested().actions[0]", true),
            ("Snapshot::build_array()[0]", false),
            ("Snapshot::build_array()[1]", true),
            ("Snapshot::section([count, freeze])[0]", true),
            ("Snapshot::section([freeze, count])[0]", false),
            ("Snapshot::one([freeze, count, freeze])[0]", false),
            ("Snapshot::one([count, freeze, count])[0]", true),
            (
                "{ let mut actions = [count]; let ^mut append = Snapshot::appender(^mut actions); append(); actions[0] }",
                false,
            ),
            (
                "{ let mut actions = [count]; let ^mut append = Snapshot::appender(^mut actions); append(); actions[1] }",
                true,
            ),
            (
                "{ let mut slot = Snapshot::Slot.{ action: freeze }; let ^mut store = Snapshot::copy_to(^mut slot, count); store(); slot.action }",
                false,
            ),
            (
                "{ let mut slot = Snapshot::Slot.{ action: count }; let ^mut store = Snapshot::copy_to(^mut slot, freeze); store(); slot.action }",
                true,
            ),
            (
                "{ let mut actions = [count]; let ^mut append = Forwarding::appender(^mut actions); append(); actions[1] }",
                true,
            ),
            (
                "{ let mut actions = [count]; let mut append = Snapshot::appender(^mut actions); Forwarding::invoke(mut append); actions[1] }",
                true,
            ),
            (
                "{ let mut actions = [count]; let mut append = Snapshot::appender(^mut actions); Snapshot::repeat(mut append, 1); actions[1] }",
                true,
            ),
            (
                "{ let mut actions = [count]; let mut append = Snapshot::appender(^mut actions); Snapshot::maybe_invoke(mut append, true); actions[1] }",
                true,
            ),
            (
                "{ let mut slot = Snapshot::Slot.{ action: count }; Snapshot::reset(mut slot, install); slot.action }",
                false,
            ),
            (
                "{ let mut slot = Snapshot::Slot.{ action: count }; Snapshot::reset_then_install(mut slot, install); slot.action }",
                true,
            ),
            (
                "{ let mut slot = Snapshot::Slot.{ action: count }; Snapshot::read_after(mut slot, install) }",
                true,
            ),
            (
                "{ let mut slot = Snapshot::Slot.{ action: freeze }; Snapshot::read_after(mut slot, clear) }",
                false,
            ),
            (
                "\\new input: Snapshot::Shelf -> { let mut slot = Snapshot::Slot.{ action: count }; Snapshot::invoke_after(mut slot, install, new input) }",
                true,
            ),
            (
                "\\new input: Snapshot::Shelf -> { let mut slot = Snapshot::Slot.{ action: freeze }; Snapshot::invoke_after(mut slot, clear, new input) }",
                false,
            ),
            (
                "{ let mut slot = Snapshot::Slot.{ action: count }; Snapshot::read_before(mut slot, install) }",
                false,
            ),
            (
                "{ let mut slot = Snapshot::Slot.{ action: count }; Snapshot::read_between(mut slot, install) }",
                true,
            ),
            (
                "{ let mut slot = Snapshot::Slot.{ action: count }; Snapshot::destructure_after(mut slot, install) }",
                true,
            ),
            (
                "{ let mut slot = Snapshot::Slot.{ action: freeze }; Snapshot::read_either(mut slot, clear, true) }",
                true,
            ),
            (
                "{ let mut slot = Snapshot::Slot.{ action: count }; Forwarding::read_after(mut slot, install) }",
                true,
            ),
            (
                "{ let mut slot = Snapshot::Slot.{ action: freeze }; Forwarding::read_after(mut slot, clear) }",
                false,
            ),
            (
                "{ let mut slot = Snapshot::Slot.{ action: count }; Snapshot::make_reader()(mut slot, install) }",
                true,
            ),
            (
                "{ let mut actions = [count]; Snapshot::array_after(mut actions, Snapshot::append) }",
                true,
            ),
            (
                "{ let mut actions = [count]; Snapshot::slice_after(mut actions, Snapshot::append) }",
                true,
            ),
            (
                "{ let mut actions = [count]; Snapshot::rest_after(mut actions, Snapshot::append) }",
                true,
            ),
            (
                "{ let mut slot = Snapshot::Slot.{ action: freeze }; let ^mut store = Forwarding::copy_to(^mut slot, count); store(); slot.action }",
                false,
            ),
            (
                "{ let mut slot = Snapshot::Slot.{ action: count }; let mut controls = Snapshot::controls(^mut slot, count, freeze); controls.select(); controls.store(); slot.action }",
                true,
            ),
            (
                "{ let mut slot = Snapshot::Slot.{ action: freeze }; let mut controls = Forwarding::controls(^mut slot, freeze, count); controls.select(); controls.store(); slot.action }",
                false,
            ),
            (
                "{ let mut first = Snapshot::Slot.{ action: count }; let mut second = Snapshot::Slot.{ action: count }; let mut controls = Snapshot::controls(^mut first, count, freeze); let mut other = Snapshot::controls(^mut second, count, freeze); controls.select(); controls.store(); other.store(); second.action }",
                false,
            ),
            (
                "{ let mut actions = [count]; Snapshot::append(mut actions); actions[0] }",
                false,
            ),
            (
                "{ let mut actions = [count]; Snapshot::append(mut actions); actions[1] }",
                true,
            ),
            ("Snapshot::identity(freeze)", true),
            ("Snapshot::identity(count)", false),
            ("Snapshot::from_callback(make)", true),
            ("Snapshot::from_callback_with(keep)", true),
            (
                "Snapshot::stamp(Snapshot::Frame.{ action: freeze, stamp: 1 }).action",
                true,
            ),
            (
                "{ let mut draft_base = Snapshot::Frame.{ action: freeze, stamp: 1 }; draft_base.action = count; let base = new draft_base; Snapshot::freeze_frame(base).action }",
                true,
            ),
            (
                "{ let mut draft_base = Snapshot::Frame.{ action: count, stamp: 1 }; draft_base.action = freeze; let base = new draft_base; Snapshot::read_frame(base).action }",
                false,
            ),
            (
                "\\new input: Snapshot::Shelf -> Snapshot::apply(make, new input)",
                true,
            ),
            (
                "\\new input: Snapshot::Shelf -> Snapshot::apply_with(keep, new input)",
                true,
            ),
            (
                "{ let mut slot = Snapshot::Slot.{ action: count }; Snapshot::install(mut slot); slot.action }",
                true,
            ),
        ] {
            for (item, live) in [("live", true), ("Snapshot::Cell.{ count: 42 }", false)] {
                let source = format!(
                    "use library/snapshot
use relay/forwarding
fn freeze(new shelf: Snapshot::Shelf) -> int {{ let fixed = new shelf; fixed.item.count }}
fn count(new shelf: Snapshot::Shelf) -> int {{ shelf.item.count }}
fn make() -> Snapshot::Leaf {{ freeze }}
fn keep(action: Snapshot::Leaf) -> Snapshot::Leaf {{ action }}
fn install(mut slot: Snapshot::Slot) &mut -> () {{ slot.action = freeze }}
fn clear(mut slot: Snapshot::Slot) &mut -> () {{ slot.action = count }}
fn observe() -> int {{
    let mut live = Snapshot::Cell.{{ count: 1 }}
    live.count += 1
    let action = {pick}
    let count = action(new Snapshot::Shelf.{{ item: ^mut {item} }})
    live.count += 8
    count + live.count
}}"
                );
                let mut client = VirtualPackage::new(Unit::Lib);
                client.insert(mount.into(), bytes.to_vec());
                client.insert("relay/forwarding.rili".into(), forwarded.clone());
                client.insert(client.entry.clone(), source.into_bytes());
                let accepted = !freezing || !live;
                match (accepted, Driver.analyze(&client)) {
                    (true, Ok(_)) => {}
                    (false, Err(diagnostics)) => {
                        assert_eq!(
                            diagnostics.len(),
                            1,
                            "{mount} {pick} {item}: {diagnostics:?}"
                        );
                        assert_eq!(diagnostics[0].code, Some(Code::E0535));
                    }
                    (true, Err(diagnostics)) => panic!("{mount} {pick} {item}: {diagnostics:?}"),
                    (false, Ok(_)) => panic!("{mount} accepted {pick} with {item}"),
                }
            }
        }
    }
}

#[test]
fn observed_storage_targets_survive_separate_compilation() {
    use ril_source::diag::Code;

    let source = br#"
pub type Cell = .{ var count: int }
pub type Shelf = .{ ^mut item: Cell }
pub type Slot = .{ var action: fn(new Shelf) -> int }
pub type Holder = .{ var ^mut slot: Slot }
pub type Swap = fn(mut Holder) &mut -> ()
pub type Edit = fn(mut Holder, Swap) &mut -> ()
pub type Action = fn(new Shelf) -> int
pub type Batch = .{ var ^mut items: []Action }
pub type ReplaceBatch = fn(mut Batch) &mut -> ()
pub type Extend = fn() &up -> ()
fn freeze(new shelf: Shelf) -> int { let fixed = new shelf; fixed.item.count }
pub fn count(new shelf: Shelf) -> int { shelf.item.count }
pub fn swap(mut holder: Holder) &mut -> () { holder.slot = Slot.{ action: count } }
fn paint(mut slot: Slot) &mut -> () { slot.action = freeze }
pub fn write_after(mut holder: Holder, replace: Swap) &mut -> () {
    replace(mut holder)
    holder.slot.action = freeze
}
pub fn delegate(mut holder: Holder, replace: Swap) &mut -> () {
    replace(mut holder)
    paint(mut holder.slot)
}
pub fn write_saved(mut holder: Holder, replace: Swap) &mut -> () {
    let ^mut saved = holder.slot
    replace(mut holder)
    saved.action = freeze
}
pub fn write_between(mut holder: Holder, replace: Swap) &mut -> () {
    replace(mut holder)
    let ^mut saved = holder.slot
    replace(mut holder)
    saved.action = freeze
}
pub fn writer() -> Edit {
    \mut holder: Holder, replace: Swap -> { replace(mut holder); holder.slot.action = freeze }
}
fn one() -> new []Action { [count] }
pub fn replace_one(mut batch: Batch) &mut -> () { batch.items = one() }
pub fn replace_two(mut batch: Batch) &mut -> () { batch.items = [count, count] }
pub fn append_twice(mut batch: Batch, replace: ReplaceBatch) &mut -> () {
    replace(mut batch)
    Array::push(mut batch.items, count)
    Array::push(mut batch.items, freeze)
}
pub fn unrelated(mut batch: Batch, replace: ReplaceBatch) &mut -> Action {
    let mut local = [count]
    replace(mut batch)
    Array::push(mut local, count)
    Array::push(mut local, freeze)
    local[1]
}
pub fn append_pair(mut items: []Action) &mut -> () {
    Array::push(mut items, count)
    Array::push(mut items, freeze)
}
pub fn append_selected(mut items: []Action) &mut -> Action {
    append_pair(mut items)
    items[1]
}
pub fn append_branch(mut items: []Action, flag: bool) &mut -> () {
    if flag { Array::push(mut items, count) } else { Array::push(mut items, freeze) }
    Array::push(mut items, count)
}
pub fn append_fixed(mut items: []Action) &mut -> () {
    for 0..2 as _ { Array::push(mut items, count) }
    Array::push(mut items, freeze)
}
pub fn append_variable(mut items: []Action, times: int) &mut -> () {
    for 0..times as _ { Array::push(mut items, count) }
    Array::push(mut items, freeze)
}
pub fn extender(^mut items: []Action) &capture &^mut &return(^mut items) -> new Extend {
    \-> { Array::push(mut items, count); Array::push(mut items, freeze) }
}
"#;
    let mut library = VirtualPackage::new(Unit::Lib);
    library.entry = "pkg/storage.ril".into();
    library.insert(library.entry.clone(), source.to_vec());
    let interface = Driver.interface(&library).unwrap().encode().unwrap();
    let mut forwarding = VirtualPackage::new(Unit::Lib);
    forwarding.entry = "pkg/forwarding.ril".into();
    forwarding.insert(
        forwarding.entry.clone(),
        br#"
use library/storage
pub fn write_after(mut holder: Storage::Holder, replace: Storage::Swap) &mut -> () {
    Storage::write_after(mut holder, replace)
}
pub fn write_between(mut holder: Storage::Holder, replace: Storage::Swap) &mut -> () {
    Storage::write_between(mut holder, replace)
}
pub fn writer() -> Storage::Edit { Storage::writer() }
pub fn append_twice(mut batch: Storage::Batch, replace: Storage::ReplaceBatch) &mut -> () {
    Storage::append_twice(mut batch, replace)
}
pub fn append_pair(mut items: []Storage::Action) &mut -> () { Storage::append_pair(mut items) }
"#
        .to_vec(),
    );
    forwarding.insert("library/storage.rili".into(), interface.clone());
    let forwarded = Driver.interface(&forwarding).unwrap().encode().unwrap();
    for (mount, bytes) in [
        ("library/storage.ril", source.as_slice()),
        ("library/storage.rili", interface.as_slice()),
    ] {
        for (write, target, freezes) in [
            ("Storage::write_after", "holder.slot", true),
            ("Storage::write_after", "original", false),
            ("Storage::delegate", "holder.slot", true),
            ("Storage::write_saved", "holder.slot", false),
            ("Storage::write_saved", "original", true),
            ("Storage::write_between", "holder.slot", false),
            ("Storage::writer()", "holder.slot", true),
            ("Forwarding::write_after", "holder.slot", true),
            ("Forwarding::write_between", "holder.slot", false),
            ("Forwarding::writer()", "holder.slot", true),
        ] {
            let source = format!(
                "use library/storage
use relay/forwarding
fn observe() -> int {{
    let mut original = Storage::Slot.{{ action: Storage::count }}
    original.action = Storage::count
    let mut holder = Storage::Holder.{{ slot: ^mut original }}
    {write}(mut holder, Storage::swap)
    let mut live = Storage::Cell.{{ count: 1 }}
    live.count += 1
    {target}.action(new Storage::Shelf.{{ item: ^mut live }})
}}"
            );
            let mut client = VirtualPackage::new(Unit::Lib);
            client.insert(mount.into(), bytes.to_vec());
            client.insert("relay/forwarding.rili".into(), forwarded.clone());
            client.insert(client.entry.clone(), source.into_bytes());
            match (freezes, Driver.analyze(&client)) {
                (false, Ok(_)) => {}
                (true, Err(diagnostics)) => {
                    assert_eq!(
                        diagnostics.len(),
                        1,
                        "{mount} {write} {target}: {diagnostics:?}"
                    );
                    assert_eq!(
                        diagnostics[0].code,
                        Some(Code::E0535),
                        "{mount} {write} {target}"
                    );
                }
                (false, Err(diagnostics)) => panic!("{mount} {write} {target}: {diagnostics:?}"),
                (true, Ok(_)) => panic!("{mount} {write} accepted a live view via {target}"),
            }
        }
        for (setup, target, freezes) in [
            (
                "Storage::append_twice(mut batch, Storage::replace_one)",
                "batch.items[0]",
                false,
            ),
            (
                "Storage::append_twice(mut batch, Storage::replace_one)",
                "batch.items[1]",
                false,
            ),
            (
                "Storage::append_twice(mut batch, Storage::replace_one)",
                "batch.items[2]",
                true,
            ),
            (
                "Storage::append_twice(mut batch, Storage::replace_two)",
                "batch.items[2]",
                false,
            ),
            (
                "Storage::append_twice(mut batch, Storage::replace_two)",
                "batch.items[3]",
                true,
            ),
            (
                "Forwarding::append_twice(mut batch, Storage::replace_one)",
                "batch.items[1]",
                false,
            ),
            (
                "Forwarding::append_twice(mut batch, Storage::replace_one)",
                "batch.items[2]",
                true,
            ),
            (
                "let run = Storage::unrelated(mut batch, Storage::replace_one)",
                "run",
                false,
            ),
        ] {
            let source = format!(
                "use library/storage
use relay/forwarding
fn observe() -> int {{
    let mut batch = Storage::Batch.{{ items: [Storage::count, Storage::count, Storage::count] }}
    {setup}
    let mut live = Storage::Cell.{{ count: 1 }}
    live.count += 1
    {target}(new Storage::Shelf.{{ item: ^mut live }})
}}"
            );
            let mut client = VirtualPackage::new(Unit::Lib);
            client.insert(mount.into(), bytes.to_vec());
            client.insert("relay/forwarding.rili".into(), forwarded.clone());
            client.insert(client.entry.clone(), source.into_bytes());
            match (freezes, Driver.analyze(&client)) {
                (false, Ok(_)) => {}
                (true, Err(diagnostics)) => {
                    assert_eq!(
                        diagnostics.len(),
                        1,
                        "{mount} {setup} {target}: {diagnostics:?}"
                    );
                    assert_eq!(
                        diagnostics[0].code,
                        Some(Code::E0535),
                        "{mount} {setup} {target}"
                    );
                }
                (false, Err(diagnostics)) => panic!("{mount} {setup} {target}: {diagnostics:?}"),
                (true, Ok(_)) => panic!("{mount} {setup} accepted a live view via {target}"),
            }
        }
        for (setup, target, freezes) in [
            ("Storage::append_pair(mut items)", "items[1]", false),
            ("Storage::append_pair(mut items)", "items[2]", true),
            ("Forwarding::append_pair(mut items)", "items[1]", false),
            ("Forwarding::append_pair(mut items)", "items[2]", true),
            (
                "let selected = Storage::append_selected(mut items)",
                "selected",
                false,
            ),
            (
                "Storage::append_branch(mut items, times > 0)",
                "items[1]",
                true,
            ),
            (
                "Storage::append_branch(mut items, times > 0)",
                "items[2]",
                false,
            ),
            ("Storage::append_fixed(mut items)", "items[2]", false),
            ("Storage::append_fixed(mut items)", "items[3]", true),
            (
                "Storage::append_variable(mut items, times)",
                "items[0]",
                false,
            ),
            (
                "Storage::append_variable(mut items, times)",
                "items[1]",
                true,
            ),
            (
                "let ^mut extend = Storage::extender(^mut items); extend()",
                "items[1]",
                false,
            ),
            (
                "let ^mut extend = Storage::extender(^mut items); extend()",
                "items[2]",
                true,
            ),
        ] {
            let source = format!(
                "use library/storage
use relay/forwarding
fn observe(times: int) -> int {{
    let mut items = [Storage::count]
    {setup}
    let mut live = Storage::Cell.{{ count: 1 }}
    live.count += 1
    {target}(new Storage::Shelf.{{ item: ^mut live }})
}}"
            );
            let mut client = VirtualPackage::new(Unit::Lib);
            client.insert(mount.into(), bytes.to_vec());
            client.insert("relay/forwarding.rili".into(), forwarded.clone());
            client.insert(client.entry.clone(), source.into_bytes());
            match (freezes, Driver.analyze(&client)) {
                (false, Ok(_)) => {}
                (true, Err(diagnostics)) => {
                    assert_eq!(
                        diagnostics.len(),
                        1,
                        "{mount} {setup} {target}: {diagnostics:?}"
                    );
                    assert_eq!(
                        diagnostics[0].code,
                        Some(Code::E0535),
                        "{mount} {setup} {target}"
                    );
                }
                (false, Err(diagnostics)) => panic!("{mount} {setup} {target}: {diagnostics:?}"),
                (true, Ok(_)) => panic!("{mount} {setup} accepted a live view via {target}"),
            }
        }
    }
}

#[test]
fn clone_rejects_live_callable_state_from_an_imported_factory() {
    use ril_source::diag::Code;

    let source = br#"
pub eff Clock { fn now() -> int; fn tick() -> int }
pub fn now() @Clock -> int { Clock::now() }
pub fn make() &capture -> new fn() &up -> int {
    var counter = 0
    counter = 1
    \-> { counter += 1; counter }
}
"#;
    let mut provider = VirtualPackage::new(Unit::Lib);
    provider.entry = "pkg/clock.ril".into();
    provider.insert(provider.entry.clone(), source.to_vec());
    let encoded = Driver.interface(&provider).unwrap().encode().unwrap();
    for (mount, bytes) in [
        ("library/clock.ril", source.as_slice()),
        ("library/clock.rili", encoded.as_slice()),
    ] {
        let mut client = VirtualPackage::new(Unit::Lib);
        client.insert(mount.into(), bytes.to_vec());
        client.insert(
            client.entry.clone(),
            b"use library/clock\nfn run() -> () { let mut h = .{ ^mut cb: Clock::make() }; let _ = h.cb(); let _ = clone(ref h) }".to_vec(),
        );
        let diagnostics = Driver.analyze(&client).err().unwrap_or_default();
        assert_eq!(
            diagnostics.iter().map(|d| d.code).collect::<Vec<_>>(),
            [Some(Code::E0530)],
            "{mount}: {diagnostics:?}"
        );
        client.insert(
            client.entry.clone(),
            br#"
use library/clock as Provider
fn run() -> () {
    var counter = 0
    with Provider::Clock::tick = \-> { counter += 1; counter }
    with Provider::Clock::now = \-> 42
    let copy = clone([Provider::now])
    assert(copy[0]() == 42 && Provider::Clock::tick() == 1)
}
"#
            .to_vec(),
        );
        assert!(Driver.analyze(&client).is_ok(), "{mount}");
    }
}

#[test]
fn k_iface_no_ctl_params_and_opaque_must_consume_survive_separate_compilation() {
    use ril_source::diag::Code;

    let source = br#"
pub opaque type Token(.{ mut k: ctl() -> () })
pub fn make_token(new k: ctl() -> ()) -> new Token { Token::(.{ mut k: new k }) }
pub fn consume_token(new t: Token) -> () {
    let Token::(.{ mut k }) = new t
    unwind_ctl(new k)
}
pub fn with_defer(cb: fn() @ -> ()) -> () {
    defer cb()
}
"#;
    let mut provider = VirtualPackage::new(Unit::Lib);
    provider.entry = "pkg/kiface.ril".into();
    provider.insert(provider.entry.clone(), source.to_vec());
    let encoded = Driver.interface(&provider).unwrap().encode().unwrap();
    let decoded = Interface::decode(&encoded).unwrap();
    assert!(
        decoded.functions["pkg/kiface.ril::with_defer"]
            .summary
            .no_ctl_params
            .contains(&0),
        "expected no_ctl_params=[0] in published interface"
    );
    for (mount, bytes) in [
        ("library/kiface.ril", source.as_slice()),
        ("library/kiface.rili", encoded.as_slice()),
    ] {
        // 1. Passing a ctl-performing callback to `with_defer` is rejected with E0616.
        let mut client1 = VirtualPackage::new(Unit::Lib);
        client1.insert(mount.into(), bytes.to_vec());
        client1.insert(
            client1.entry.clone(),
            br#"
use library/kiface
eff Yield { ctl step() -> () }
fn bad() @Yield -> () {
    Kiface::with_defer(\-> Yield::step())
}
"#
            .to_vec(),
        );
        let diags1 = Driver.analyze(&client1).err().unwrap_or_default();
        assert!(
            diags1.iter().any(|d| d.code == Some(Code::E0616)),
            "{mount}: expected E0616 for ctl callback in deferred param, got {diags1:?}"
        );

        // 2. Dropping an opaque must-consume `Token` without consuming it is rejected with E0625.
        let mut client2 = VirtualPackage::new(Unit::Lib);
        client2.insert(mount.into(), bytes.to_vec());
        client2.insert(
            client2.entry.clone(),
            br#"
use library/kiface
eff Yield { ctl step() -> () }
fn bad() -> () {
    with {
        ctl Yield::step = \new k -> {
            let mut t = Kiface::make_token(new k)
            let _ = t
            ()
        }
        Yield::step()
    }
}
"#
            .to_vec(),
        );
        let diags2 = Driver.analyze(&client2).err().unwrap_or_default();
        assert!(
            diags2.iter().any(|d| d.code == Some(Code::E0625)),
            "{mount}: expected E0625 for dropped opaque must-consume Token, got {diags2:?}"
        );
    }
}

#[test]
fn clone_replays_callable_constraints_across_interfaces() {
    use ril_sema::access::{StorageStep, StorageTransfer};
    use ril_source::diag::Code;

    let source = br#"
pub type Cell = .{ var count: int }
pub type Shelf = .{ ^mut item: Cell }
pub type Action = fn(new Shelf) -> int
pub type Pair = .{ item: Cell, var tag: int }
pub fn count(new shelf: Shelf) -> int { shelf.item.count }
pub fn freeze(new shelf: Shelf) -> int { let fixed = new shelf; fixed.item.count }
pub fn duplicate(actions: []Action) -> new []Action { clone(actions) }
pub fn twice(actions: []Action) -> new []Action { duplicate(duplicate(actions)) }
pub fn pair() -> new Pair { clone(Pair.{ item: Cell.{ count: 1 }, tag: 0 }) }
pub fn append_count(mut actions: []Action) &mut -> () { Array::push(mut actions, count) }
pub fn append_freeze(mut actions: []Action) &mut -> () { Array::push(mut actions, freeze) }
pub fn after(mut actions: []Action, edit: fn(mut []Action) &mut -> ()) &mut -> new []Action {
    edit(mut actions)
    clone(ref actions)
}
pub fn after_local(edit: fn(mut []Action) &mut -> ()) -> new []Action {
    let mut actions = [count]
    edit(mut actions)
    clone(ref actions)
}
"#;
    let mut library = VirtualPackage::new(Unit::Lib);
    library.entry = "pkg/copies.ril".into();
    library.insert(library.entry.clone(), source.to_vec());
    let encoded = Driver.interface(&library).unwrap().encode().unwrap();
    let decoded = Interface::decode(&encoded).unwrap();
    let export = &decoded.functions["pkg/copies.ril::duplicate"];
    assert!(matches!(
        &export.summary.storage_flow,
        Some(StorageTransfer::Paths(paths))
            if matches!(paths.as_slice(), [steps] if matches!(steps.as_slice(), [StorageStep::Clone { .. }]))
    ));

    for (mount, bytes) in [
        ("library/copies.ril", source.as_slice()),
        ("library/copies.rili", encoded.as_slice()),
    ] {
        let mut client = VirtualPackage::new(Unit::Lib);
        client.insert(mount.into(), bytes.to_vec());
        client.insert(
            client.entry.clone(),
            br#"
use library/copies
fn run() -> int {
    let mut pair = Copies::pair()
    pair.tag += 1
    pair.item.count += 1
    pair.tag
}
"#
            .to_vec(),
        );
        let diagnostics = Driver.analyze(&client).err().unwrap_or_default();
        assert_eq!(
            diagnostics.iter().map(|d| d.code).collect::<Vec<_>>(),
            [Some(Code::E0520)],
            "{mount}: {diagnostics:?}"
        );
        for (callback, code) in [("count", None), ("freeze", Some(Code::E0535))] {
            for (copy, index) in [
                (
                    format!("let copied = Copies::twice([Copies::{callback}])"),
                    0,
                ),
                (
                    format!(
                        "let mut actions = [Copies::count]
    let copied = Copies::after(mut actions, Copies::append_{callback})
    Array::push(mut actions, Copies::freeze)"
                    ),
                    1,
                ),
                (
                    format!("let copied = Copies::after_local(Copies::append_{callback})"),
                    1,
                ),
            ] {
                let mut client = VirtualPackage::new(Unit::Lib);
                client.insert(mount.into(), bytes.to_vec());
                client.insert(
                    client.entry.clone(),
                    format!(
                        "use library/copies
fn run() -> int {{
    let mut live = Copies::Cell.{{ count: 1 }}
    live.count += 1
    {copy}
    copied[{index}](new Copies::Shelf.{{ item: ^mut live }})
}}"
                    )
                    .into_bytes(),
                );
                let diagnostics = Driver.analyze(&client).err().unwrap_or_default();
                let actual: Vec<_> = diagnostics.iter().map(|d| d.code).collect();
                let expected: Vec<_> = code.into_iter().map(Some).collect();
                assert_eq!(actual, expected, "{mount} {copy}: {diagnostics:?}");
            }
        }
    }
}

#[test]
fn ordered_draft_updates_survive_separate_compilation() {
    use ril_source::diag::Code;

    let source = br#"
pub type Cell = .{ var count: int }
pub type Shelf = .{ ^mut item: Cell }
pub type Action = fn(new Shelf) -> int
pub type Pair = .{ left: []Action, right: []Action }
pub type Update = fn(mut Derived<Pair>) &mut -> ()
pub type EditItems = fn(mut []Action) &mut -> ()
pub type Slot = .{ var action: Action }
pub type StateUpdate = fn(mut Derived<[]int>) &mut &up -> ()
pub fn count(new shelf: Shelf) -> int { shelf.item.count }
fn freeze(new shelf: Shelf) -> int { let fixed = new shelf; fixed.item.count }
pub fn extend(mut draft: Derived<Pair>) &mut -> () {
    Array::push(mut draft.left, count)
    Array::push(mut draft.left, freeze)
}
pub fn extend_safe(mut draft: Derived<Pair>) &mut -> () {
    Array::push(mut draft.left, count)
}
pub fn forward(base: Pair, edit: Update) -> Pair { derive(base, edit) }
pub fn twice(base: Pair, first: Update, second: Update) -> Pair {
    forward(forward(base, first), second)
}
fn update_draft(mut draft: Derived<Pair>, edit: Update) &mut -> () { edit(mut draft) }
pub fn forward_inside(base: Pair, edit: Update) -> Pair {
    derive(base) \mut draft -> {
        Array::push(mut draft.left, count)
        update_draft(mut draft, edit)
    }
}
pub fn append_freeze(mut items: []Action) &mut -> () { Array::push(mut items, freeze) }
fn update_items(mut draft: Derived<Pair>, edit: EditItems) &mut -> () {
    Array::push(mut draft.left, count)
    edit(mut draft.left)
}
pub fn forward_items(base: Pair, edit: EditItems) -> Pair {
    derive(base) \mut draft -> { update_items(mut draft, edit) }
}
pub fn forwarder() -> fn(Pair, Update) -> Pair {
    \base: Pair, edit: Update -> derive(base, edit)
}
pub fn updater(first: Action) &capture &return(first) -> new Update {
    \mut draft: Derived<Pair> -> { Array::push(mut draft.left, first); Array::push(mut draft.left, freeze) }
}
pub fn finished() -> Pair {
    let shared = [count]
    derive(Pair.{ left: shared, right: shared }, extend)
}
pub fn slot_updater(^mut slot: Slot, action: Action) &capture &^mut &return(^mut slot, action) -> new StateUpdate {
    \mut draft: Derived<[]int> -> { Array::push(mut draft, 2); slot.action = action }
}
pub fn edit_slot(mut slot: Slot, action: Action) &mut -> []int {
    derive([1]) \mut draft -> { Array::push(mut draft, 2); slot.action = action }
}
pub fn edit_through(mut slot: Slot, edit: fn(mut Slot) &mut -> ()) &mut -> []int {
    derive([1]) \mut draft -> { Array::push(mut draft, 2); edit(mut slot) }
}
pub fn forward_state(base: []int, edit: StateUpdate) -> []int {
    derive(base, edit)
}
"#;
    let mut library = VirtualPackage::new(Unit::Lib);
    library.entry = "pkg/updates.ril".into();
    library.insert(library.entry.clone(), source.to_vec());
    let interface = Driver.interface(&library).unwrap().encode().unwrap();
    let mut forwarding = VirtualPackage::new(Unit::Lib);
    forwarding.entry = "pkg/forwarding.ril".into();
    forwarding.insert(
        forwarding.entry.clone(),
        br#"
use library/updates
pub fn updater(first: Updates::Action) &capture &return(first) -> new Updates::Update {
    Updates::updater(first)
}
pub fn forward(base: Updates::Pair, edit: Updates::Update) -> Updates::Pair {
    Updates::forward(base, edit)
}
pub fn slot_updater(^mut slot: Updates::Slot, action: Updates::Action) &capture &^mut &return(^mut slot, action) -> new Updates::StateUpdate {
    Updates::slot_updater(^mut slot, action)
}
"#
        .to_vec(),
    );
    forwarding.insert("library/updates.rili".into(), interface.clone());
    let forwarded = Driver.interface(&forwarding).unwrap().encode().unwrap();
    for (mount, bytes) in [
        ("library/updates.ril", source.as_slice()),
        ("library/updates.rili", interface.as_slice()),
    ] {
        for (update, frozen) in [
            ("derive(base, Updates::extend)", "left[2]"),
            ("derive(base, Updates::updater(Updates::count))", "left[2]"),
            (
                "derive(base, Forwarding::updater(Updates::count))",
                "left[2]",
            ),
            ("Updates::finished()", "left[2]"),
            ("Updates::forward(base, Updates::extend)", "left[2]"),
            ("Forwarding::forward(base, Updates::extend)", "left[2]"),
            ("Updates::forwarder()(base, Updates::extend)", "left[2]"),
            ("Updates::forward_inside(base, Updates::extend)", "left[3]"),
            (
                "Updates::forward_items(base, Updates::append_freeze)",
                "left[2]",
            ),
            (
                "Updates::twice(base, Updates::extend_safe, Updates::extend)",
                "left[3]",
            ),
        ] {
            for (target, freezes) in [("left[1]", false), (frozen, true), ("right[0]", false)] {
                let source = format!(
                    "use library/updates
use relay/forwarding
fn observe() -> int {{
    let shared = [Updates::count]
    let base = Updates::Pair.{{ left: shared, right: shared }}
    let next = {update}
    let mut live = Updates::Cell.{{ count: len(base.left) }}
    live.count += 1
    next.{target}(new Updates::Shelf.{{ item: ^mut live }})
}}"
                );
                let mut client = VirtualPackage::new(Unit::Lib);
                client.insert(mount.into(), bytes.to_vec());
                client.insert("relay/forwarding.rili".into(), forwarded.clone());
                client.insert(client.entry.clone(), source.into_bytes());
                match (freezes, Driver.analyze(&client)) {
                    (false, Ok(_)) => {}
                    (true, Err(diagnostics)) => {
                        assert_eq!(
                            diagnostics.len(),
                            1,
                            "{mount} {update} {target}: {diagnostics:?}"
                        );
                        assert_eq!(
                            diagnostics[0].code,
                            Some(Code::E0535),
                            "{mount} {update} {target}"
                        );
                    }
                    (false, Err(diagnostics)) => {
                        panic!("{mount} {update} {target}: {diagnostics:?}")
                    }
                    (true, Ok(_)) => panic!("{mount} {update} accepted a live view via {target}"),
                }
            }
        }
        for update in [
            "derive([1], Updates::slot_updater(^mut slot, {action}))",
            "derive([1], Forwarding::slot_updater(^mut slot, {action}))",
            "Updates::edit_slot(mut slot, {action})",
            "Updates::edit_through(mut slot, \\mut target: Updates::Slot -> { target.action = {action} })",
            "Updates::forward_state([1], Updates::slot_updater(^mut slot, {action}))",
        ] {
            for (initial, action, freezes) in [
                ("freeze", "Updates::count", false),
                ("Updates::count", "freeze", true),
            ] {
                let update = update.replace("{action}", action);
                let source = format!(
                    "use library/updates
use relay/forwarding
fn freeze(new shelf: Updates::Shelf) -> int {{ let fixed = new shelf; fixed.item.count }}
fn observe() -> int {{
    let mut slot = Updates::Slot.{{ action: {initial} }}
    let numbers = {update}
    let mut live = Updates::Cell.{{ count: len(numbers) }}
    live.count += 1
    slot.action(new Updates::Shelf.{{ item: ^mut live }})
}}"
                );
                let mut client = VirtualPackage::new(Unit::Lib);
                client.insert(mount.into(), bytes.to_vec());
                client.insert("relay/forwarding.rili".into(), forwarded.clone());
                client.insert(client.entry.clone(), source.into_bytes());
                match (freezes, Driver.analyze(&client)) {
                    (false, Ok(_)) => {}
                    (true, Err(diagnostics)) => {
                        assert_eq!(diagnostics.len(), 1, "{mount} {update}: {diagnostics:?}");
                        assert_eq!(diagnostics[0].code, Some(Code::E0535), "{mount} {update}");
                    }
                    (false, Err(diagnostics)) => panic!("{mount} {update}: {diagnostics:?}"),
                    (true, Ok(_)) => panic!("{mount} {update} accepted a live view"),
                }
            }
        }
    }
}

#[test]
fn correlated_callback_mode_offers_survive_interface_only_calls() {
    use ril_source::diag::Code;

    let nested_callback_call = |callback| {
        format!(
            "Adapter::visit(Adapter::Node::(.{{
            action: Adapter::observe,
            next: Some(Adapter::Node::(.{{ action: Adapter::{callback}, next: None }}))
        }}))"
        )
    };
    let provider_source = br#"
pub type Cell = .{ var count: int }
fn edit(mut writer: Cell, ref reader: Cell) &mut -> () { writer.count += reader.count }
pub fn combine(via left: Cell, via right: Cell) -> () { edit(mut left, ref right) }
pub fn dispatch(action: fn(via Cell, via Cell) -> (), flag: bool) -> int {
    let mut left = Cell.{ count: 1 }
    let mut right = Cell.{ count: 2 }
    left.count += 1
    right.count += 1
    if flag { action(^mut left, ref right) }
    else { action(mut left, ^mut right) }
    left.count
}
fn forward(action: fn(via Cell, via Cell) -> (), via left: Cell, via right: Cell) -> () {
    action(left, right)
}
pub fn relay(action: fn(via Cell, via Cell) -> (), via left: Cell, via right: Cell, recur: bool) -> () {
    if recur { relay(action, left, right, false) }
    else { forward(action, left, right) }
}
pub type Node(.{ action: fn(via Cell, via Cell) -> (), next: ?Node })
pub fn observe(via left: Cell, via right: Cell) -> () { assert(left.count == right.count) }
pub fn visit(node: Node) -> int {
    let mut cell = Cell.{ count: 1 }
    let ^mut alias = cell
    alias.count += 1
    node.action(^mut cell, ^mut alias)
    match node.next { Some(tail) -> visit(tail); None -> cell.count }
}
"#;
    let mut provider = VirtualPackage::new(Unit::Lib);
    provider.entry = "pkg/adapter.ril".into();
    provider.insert(provider.entry.clone(), provider_source.to_vec());
    let interface = Driver.interface(&provider).unwrap().encode().unwrap();
    let decoded = Interface::decode(&interface).unwrap();
    assert!(decoded.functions.values().any(|export| {
        export
            .summary
            .mode_calls
            .as_ref()
            .is_some_and(|calls| calls.len() == 2)
    }));
    assert!(decoded.functions.values().any(|export| {
        export
            .summary
            .offered_mode_calls()
            .iter()
            .any(|call| call.recursive_path.is_some())
    }));
    for (mount, bytes) in [
        ("library/adapter.ril", provider_source.as_slice()),
        ("library/adapter.rili", interface.as_slice()),
    ] {
        for (call, accepted) in [
            (
                "Adapter::relay(Adapter::combine, mut left, ^mut right, flag); 0".to_owned(),
                true,
            ),
            (
                "Adapter::relay(Adapter::combine, ^mut left, ^mut right, flag); 0".to_owned(),
                false,
            ),
            (nested_callback_call("observe"), true),
            (nested_callback_call("combine"), false),
        ] {
            let source = format!(
                "use library/adapter
fn run(flag: bool) -> int {{
    let value = Adapter::dispatch(Adapter::combine, flag)
    let mut left = Adapter::Cell.{{ count: 1 }}
    let mut right = Adapter::Cell.{{ count: 2 }}
    left.count += 1
    right.count += 1
    let checked = {{ {call} }}
    value + left.count + right.count + checked
}}"
            );
            let mut client = VirtualPackage::new(Unit::Lib);
            client.insert(mount.into(), bytes.to_vec());
            client.insert(client.entry.clone(), source.into_bytes());
            let result = Driver.analyze(&client);
            match (accepted, result) {
                (true, Err(diagnostics)) => panic!("{mount} {call}: {diagnostics:?}"),
                (false, Err(diagnostics)) => {
                    assert_eq!(diagnostics.len(), 1, "{mount} {call}: {diagnostics:?}");
                    assert_eq!(diagnostics[0].code, Some(Code::E0520));
                }
                (false, Ok(_)) => panic!("{mount} unexpectedly accepted {call}"),
                (true, Ok(_)) => {}
            }
        }
    }
}

#[test]
fn derive_snapshot_domains_survive_interface_only_forwarding() {
    use ril_source::diag::Code;

    // Single-mode `via` constrained solely to Plain by `derive` is rejected with E0550.
    let single_mode_src = br#"
pub type Cell = .{ var count: int }
pub fn root(via base: Cell) -> Cell {
    derive(base) \mut draft -> { draft.count += 1 }
}
"#;
    let mut single_pkg = VirtualPackage::new(Unit::Lib);
    single_pkg.entry = "pkg/single.ril".into();
    single_pkg.insert(single_pkg.entry.clone(), single_mode_src.to_vec());
    let single_diags = Driver.interface(&single_pkg).err().unwrap();
    assert!(
        single_diags.iter().any(|d| d.code == Some(Code::E0550)),
        "expected E0550 for single-mode derive via: {single_diags:?}"
    );

    let provider_source = br#"
pub type Cell = .{ var count: int }
pub fn member(via box: .{ via item: Cell, var stamp: int }) -> Cell {
    derive(box.item) \mut draft -> { draft.count += 1 }
}
"#;
    let mut provider = VirtualPackage::new(Unit::Lib);
    provider.entry = "pkg/update.ril".into();
    provider.insert(provider.entry.clone(), provider_source.to_vec());
    let published = Driver.interface(&provider).unwrap();
    let domains = |interface: &Interface| {
        let export = interface
            .functions
            .iter()
            .find(|(path, _)| path.rsplit("::").next() == Some("member"))
            .unwrap()
            .1;
        export
            .domain
            .iter()
            .map(|row| row.modes)
            .collect::<BTreeSet<_>>()
    };
    let observed = domains(&published);
    assert_eq!(observed.len(), 8);
    let encoded = published.encode().unwrap();
    for (mount, bytes) in [
        ("library/update.ril", provider_source.as_slice()),
        ("library/update.rili", encoded.as_slice()),
    ] {
        let forwarding = r#"
use library/update
pub fn member(via box: .{ via item: Update::Cell, var stamp: int }) -> Update::Cell {
    Update::member(box)
}
"#;
        let mut client = VirtualPackage::new(Unit::Lib);
        client.insert(mount.into(), bytes.to_vec());
        client.insert(client.entry.clone(), forwarding.as_bytes().to_vec());
        assert_eq!(
            domains(&Driver.interface(&client).unwrap()),
            observed,
            "{mount}"
        );
        for (call, accepted) in [
            ("member(fixed)", true),
            ("member(mut copy)", true),
            ("member(mut live)", false),
        ] {
            let source = format!(
                "{forwarding}
fn run() -> int {{
    let snapshot = Update::Cell.{{ count: 1 }}
    let fixed = .{{ mut item: Update::Cell.{{ count: 2 }}, var stamp: 0 }}
    let mut copy = .{{ item: snapshot, var stamp: 0 }}
    let mut live = .{{ mut item: Update::Cell.{{ count: 3 }}, var stamp: 0 }}
    copy.stamp += 1
    live.stamp += 1
    {call}.count
}}"
            );
            client.insert(client.entry.clone(), source.into_bytes());
            let result = Driver.analyze(&client);
            match (accepted, result) {
                (true, Ok(_)) => {}
                (false, Err(diagnostics)) => {
                    assert!(
                        diagnostics.iter().any(|d| d.code == Some(Code::E0520)),
                        "{mount} {call}: {diagnostics:?}"
                    );
                }
                (_, result) => panic!("{mount} {call}: {:?}", result.err()),
            }
        }
    }
}

#[test]
fn joint_via_restrictions_survive_interface_only_forwarding() {
    use ril_sema::access::Input;
    use ril_source::diag::Code;

    let provider_source = br#"
pub type Cell = .{ var count: int }
fn edit(mut writer: Cell, ref reader: Cell) &mut -> () { writer.count += reader.count }
pub fn combine(via left: Cell, via right: Cell) -> () { edit(mut left, ref right) }
"#;
    let mut provider = VirtualPackage::new(Unit::Lib);
    provider.entry = "pkg/provider.ril".into();
    provider.insert(provider.entry.clone(), provider_source.to_vec());
    let interface = Driver.interface(&provider).unwrap().encode().unwrap();
    for (mount, bytes) in [
        ("library/provider.ril", provider_source.as_slice()),
        ("library/provider.rili", interface.as_slice()),
    ] {
        let relay = r#"
use library/provider
pub fn relay(via left: Provider::Cell, via right: Provider::Cell) -> () {
    let combine = Provider::combine
    combine(left, right)
}
"#;
        let mut client = VirtualPackage::new(Unit::Lib);
        client.insert(mount.into(), bytes.to_vec());
        client.insert(client.entry.clone(), relay.as_bytes().to_vec());
        let published = Driver.interface(&client).unwrap();
        let domain = &published.functions.values().next().unwrap().domain;
        assert_eq!(domain.len(), 14);
        for (pair, allowed) in [
            ([Input::Shared, Input::Shared], false),
            ([Input::Mut, Input::Shared], true),
            ([Input::Shared, Input::Ref], true),
        ] {
            assert_eq!(
                domain.iter().any(|row| row.modes == pair),
                allowed,
                "{mount}"
            );
        }
        for (call, allowed) in [
            ("relay(^mut left, ^mut right)", false),
            ("relay(mut left, ^mut right)", true),
        ] {
            let source = format!(
                "{relay}
fn run() -> int {{
    let mut left = Provider::Cell.{{ count: 1 }}
    let mut other = Provider::Cell.{{ count: 2 }}
    let ^mut right = other
    right.count += 1
    {call}
    left.count
}}"
            );
            client.insert(client.entry.clone(), source.into_bytes());
            let result = Driver.analyze(&client);
            if allowed {
                assert!(result.is_ok(), "{mount} {call}: {:?}", result.err());
            } else {
                let diagnostics = result.err().expect("shared pair must be rejected");
                assert!(
                    diagnostics.iter().any(|d| d.code == Some(Code::E0520)),
                    "{mount} {call}: {diagnostics:?}"
                );
            }
        }
    }
}

#[test]
fn compound_result_obligations_survive_an_interface_only_boundary() {
    use ril_source::diag::Code;

    let provider_source = br#"
fn get(value: int) -> new !<int, str> { Ok(value) }
pub type Packet<T>(.{ payload: T })
pub fn packet() -> new Packet<!<int, str>> { Packet::(.{ payload: get(1) }) }
pub fn batch() -> new []!<int, str> { [get(1), get(2)] }
pub fn varying_batch(flag: bool) -> new []!<int, str> {
    if flag { [get(1), Err("failed")] } else { [] }
}
pub fn lookup_table() -> new [str: !<int, str>] { ["first": get(1), "second": get(2)] }
pub type Key = .{ id: int }
pub fn first_key(table: [Key: int]) &return(table) -> new ?Key {
    for table as (key, _) { return Some(key) }
    None
}
pub fn snapshot_batch() -> []!<int, str> {
    let snapshot = [get(1), get(2)]
    snapshot
}
pub fn wrapped(flag: bool) -> new ?!<int, str> {
    if flag { Some(get(1)) } else { None }
}
pub fn pair() -> new (!<int, str>, !<int, str>) { (get(1), get(2)) }
pub fn aliases() -> new (!<int, str>, !<int, str>) {
    let shared = get(1)
    (shared, shared)
}
pub fn snapshot_aliases() -> (!<int, str>, !<int, str>) {
    let shared = get(1)
    let snapshot = (shared, shared)
    snapshot
}
"#;
    let mut provider = VirtualPackage::new(Unit::Lib);
    provider.entry = "pkg/fallible.ril".into();
    provider.insert(provider.entry.clone(), provider_source.to_vec());
    let published = Driver.interface(&provider).unwrap();
    assert!(published.functions.values().any(|export| {
        export.summary.return_sources.iter().any(|source| {
            source
                .source_path
                .contains(&ril_sema::access::Coordinate::MapKey)
        })
    }));
    let interface = published.encode().unwrap();
    assert_eq!(
        Interface::decode(&interface).unwrap().format_version,
        FORMAT_VERSION
    );
    for (mount, bytes) in [
        ("library/fallible.ril", provider_source.as_slice()),
        ("library/fallible.rili", interface.as_slice()),
    ] {
        for (body, accepted) in [
            ("let _ = Fallible::packet()", false),
            ("assert(inner(Fallible::packet()).payload == Ok(1))", true),
            ("let _ = Fallible::batch()", false),
            (
                "for Fallible::batch() as item { match item { Ok(_) -> (); Err(_) -> () } }",
                true,
            ),
            (
                "for Fallible::snapshot_batch() as item { match item { Ok(_) -> (); Err(_) -> () } }",
                true,
            ),
            (
                "for Fallible::batch() as item { match item { Ok(_) -> (); Err(_) -> () }; break }",
                false,
            ),
            ("let _ = Fallible::varying_batch(flag)", false),
            (
                "for Fallible::varying_batch(flag) as item { match item { Ok(_) -> (); Err(_) -> () } }",
                true,
            ),
            (
                "for Fallible::varying_batch(flag) as item { match item { Ok(_) -> (); Err(_) -> () }; break }",
                false,
            ),
            ("let _ = Fallible::lookup_table()", false),
            (
                "for Fallible::lookup_table() as (_, item) { match item { Ok(_) -> (); Err(_) -> () } }",
                true,
            ),
            (
                "for Fallible::lookup_table() as (_, item) { match item { Ok(_) -> (); Err(_) -> () }; break }",
                false,
            ),
            (
                "let _ = Fallible::first_key([Fallible::Key.{ id: 1 }: 3])",
                true,
            ),
            (
                "match Fallible::wrapped(flag) { Some(_) -> (); None -> () }",
                false,
            ),
            (
                "match Fallible::wrapped(flag) { Some(Ok(_)) -> (); Some(Err(_)) -> (); None -> () }",
                true,
            ),
            (
                "let (first, second) = Fallible::pair(); assert(first == Ok(1))",
                false,
            ),
            (
                "let (first, second) = Fallible::aliases(); assert(first == Ok(1))",
                true,
            ),
            (
                "let (first, second) = Fallible::snapshot_aliases(); assert(first == Ok(1))",
                true,
            ),
        ] {
            let mut client = VirtualPackage::new(Unit::Lib);
            let source = format!("use library/fallible\nfn run(flag: bool) -> () {{ {body} }}");
            client.insert(client.entry.clone(), source.into_bytes());
            client.insert(mount.into(), bytes.to_vec());
            let diagnostics = Driver.check_stage(&client, Stage::Access).diagnostics;
            let seen: BTreeSet<_> = diagnostics
                .iter()
                .map(|diagnostic| diagnostic.code)
                .collect();
            let expected = if accepted {
                BTreeSet::new()
            } else {
                BTreeSet::from([Some(Code::E0720)])
            };
            assert_eq!(seen, expected, "{mount}, {body}: {diagnostics:?}");
        }
    }
}

#[test]
fn recursive_allocation_graphs_survive_interface_replay() {
    use ril_source::diag::Code;

    let provider_source = br#"
pub type Node(.{ var value: int, var ^mut next: ?Node })
pub type Shelf = .{ var mut head: Node }
pub type Pair = .{ var ^mut left: Node, var ^mut right: Node }
pub fn build(^mut tail: Node, count: int) &mut &^mut &return(^mut tail) -> new Node {
    var ^mut head = tail
    for 0..count as i {
        let mut node = Node::(.{ value: i, next: Some(^mut head) })
        node.value += 1
        head = ^mut node
    }
    head.value += 1
    Node::(.{ value: 0, next: Some(^mut head) })
}
pub fn store(mut shelf: Shelf, ^mut tail: Node, count: int) &mut &^mut -> () {
    shelf.head = build(^mut tail, count)
}
pub fn publish(mut pair: Pair, ^mut tail: Node, count: int) &mut &^mut -> () {
    let mut head = build(^mut tail, count)
    head.value += 1
    pair.left = ^mut head
    pair.right = ^mut head
}
pub fn through(via action: fn(via Node) @& -> infer Node, ^mut tail: Node, count: int) &mut &^mut -> infer Node {
    let mut chain = build(^mut tail, count)
    action(new chain)
}
pub fn relay(via action: fn(via Node) @& -> infer Node, ^mut tail: Node, count: int) &mut &^mut -> infer Node {
    through(action, ^mut tail, count)
}
pub fn choose(via action: fn(via Node) @& -> infer Node, ^mut tail: Node, count: int, first: bool) &mut &^mut -> infer Node {
    let mut chain = build(^mut tail, count)
    if first { action(new chain) } else { action(new chain) }
}
"#;
    let mut provider = VirtualPackage::new(Unit::Lib);
    provider.entry = "pkg/chain.ril".into();
    provider.insert(provider.entry.clone(), provider_source.to_vec());
    let interface = Driver.interface(&provider).unwrap().encode().unwrap();
    let decoded = Interface::decode(&interface).unwrap();
    let allocations = &decoded.functions["pkg/chain.ril::build"]
        .summary
        .return_allocations;
    assert!(allocations.iter().any(|allocation| {
        allocation.summarized
            && allocations
                .iter()
                .any(|other| allocation.index == other.index && allocation.path != other.path)
    }));
    let updates = &decoded.functions["pkg/chain.ril::publish"]
        .summary
        .storage_updates;
    let [left, right] = updates.as_slice() else {
        panic!("expected both member updates: {updates:?}");
    };
    let root_index = |update: &ril_sema::access::StorageUpdate| {
        update
            .allocations
            .iter()
            .find(|allocation| allocation.path.is_empty())
            .unwrap()
            .index
    };
    assert_eq!(root_index(left), root_index(right));

    for name in ["through", "relay"] {
        let export = &decoded.functions[&format!("pkg/chain.ril::{name}")];
        assert!(!export.domain.is_empty(), "{name}");
        for row in &export.domain {
            let [callback] = row.summary.callback_returns.as_slice() else {
                panic!("missing callback for {name}: {:?}", row.summary);
            };
            let allocations = &callback.arguments[0].allocations;
            assert!(allocations.iter().any(|allocation| {
                allocation.summarized
                    && allocations.iter().any(|other| {
                        allocation.index == other.index && allocation.path != other.path
                    })
            }));
        }
    }
    for row in &decoded.functions["pkg/chain.ril::choose"].domain {
        let [first, second] = row.summary.callback_returns.as_slice() else {
            panic!("expected two syntactic invocations: {:?}", row.summary);
        };
        assert_ne!(first.invocation, second.invocation);
        assert_eq!(
            first.arguments[0].allocations,
            second.arguments[0].allocations
        );
    }

    let read_chain = |head: &str, mut read: String, end: &str| {
        for depth in (1..=9).rev() {
            let parent = if depth == 1 {
                head.to_owned()
            } else {
                format!("link{}", depth - 1)
            };
            read =
                format!("match ref {parent}.next {{ Some(link{depth}) -> {read}; None -> {end} }}");
        }
        read
    };
    let callback_oracle = std::env::var_os("RIL_HORN_ORACLE").map(|oracle| {
        let output = query(&oracle, "callback-graph", b"[[9,0],[9,3]]").unwrap();
        serde_json::from_slice::<[bool; 2]>(&output).unwrap()
    });
    for (path, bytes) in [
        ("library/chain.ril", provider_source.as_slice()),
        ("library/chain.rili", interface.as_slice()),
    ] {
        for (setup, head) in [
            (
                "let mut head = Chain::build(^mut tail, count)\nhead.value += 1",
                "head",
            ),
            (
                "let mut shelf = Chain::Shelf.{ head: Chain::Node::(.{ value: 0, next: None }) }\nChain::store(mut shelf, ^mut tail, count)",
                "shelf.head",
            ),
            (
                "let mut head = Chain::relay(identity, ^mut tail, count)\nhead.value += 1",
                "head",
            ),
        ] {
            for (target, spare, expected) in [
                ("tail", "", vec![Some(Code::E0524)]),
                (
                    "spare",
                    "let mut spare = Chain::Node::(.{ value: 0, next: None })",
                    Vec::new(),
                ),
            ] {
                let read = read_chain(head, format!("copy(mut {target}, ref link9)"), "()");
                let source = format!(
                    "use library/chain\n\
                     fn identity(via node: Chain::Node) -> infer Chain::Node {{ node }}\n\
                     fn copy(mut target: Chain::Node, ref reader: Chain::Node) &mut -> () {{ target.value = reader.value }}\n\
                     fn run(count: int) -> () {{\n\
                        let mut tail = Chain::Node::(.{{ value: 1, next: None }})\n\
                        {setup}\n{spare}\n{read}\n\
                     }}"
                );
                let mut client = VirtualPackage::new(Unit::Lib);
                client.insert(client.entry.clone(), source.into_bytes());
                client.insert(path.into(), bytes.to_vec());
                let diagnostics = Driver.check_stage(&client, Stage::Access).diagnostics;
                let codes: Vec<_> = diagnostics
                    .iter()
                    .map(|diagnostic| diagnostic.code)
                    .collect();
                assert_eq!(codes, expected, "{path}, {head}, {target}: {diagnostics:?}");
            }
        }
        let projection = read_chain("head", "link9".into(), "panic(\"short chain\")");
        for (case, (target, spare, expected)) in [
            ("tail", "", vec![Some(Code::E0524)]),
            (
                "spare",
                "let mut spare = Chain::Node::(.{ value: 0, next: None })",
                Vec::new(),
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let source = format!(
                "use library/chain\n\
                 fn project(via head: Chain::Node) -> infer Chain::Node {{ {projection} }}\n\
                 fn copy(mut target: Chain::Node, ref reader: Chain::Node) &mut -> () {{ target.value = reader.value }}\n\
                 fn run(count: int) -> () {{\n\
                    let mut tail = Chain::Node::(.{{ value: 1, next: None }})\n\
                    let ref found = ref Chain::relay(project, ^mut tail, count)\n\
                    {spare}\n\
                    copy(mut {target}, ref found)\n\
                 }}"
            );
            let mut client = VirtualPackage::new(Unit::Lib);
            client.insert(client.entry.clone(), source.into_bytes());
            client.insert(path.into(), bytes.to_vec());
            let diagnostics = Driver.check_stage(&client, Stage::Access).diagnostics;
            let codes: Vec<_> = diagnostics
                .iter()
                .map(|diagnostic| diagnostic.code)
                .collect();
            assert_eq!(
                codes, expected,
                "{path}, callback, {target}: {diagnostics:?}"
            );
            if let Some(oracle) = callback_oracle {
                assert_eq!(diagnostics.is_empty(), oracle[case], "{path}, {target}");
            }
        }
        let mut client = VirtualPackage::new(Unit::Lib);
        client.insert(
            client.entry.clone(),
            br#"
use library/chain
fn copy(mut target: Chain::Node, ref reader: Chain::Node) &mut -> () { target.value = reader.value }
fn run(count: int) -> () {
    let mut tail = Chain::Node::(.{ value: 1, next: None })
    let mut first = Chain::Node::(.{ value: 2, next: None })
    let mut second = Chain::Node::(.{ value: 3, next: None })
    first.value += 1
    second.value += 1
    let mut pair = Chain::Pair.{ left: ^mut first, right: ^mut second }
    Chain::publish(mut pair, ^mut tail, count)
    copy(mut pair.left, ref pair.right)
}
"#
            .to_vec(),
        );
        client.insert(path.into(), bytes.to_vec());
        let diagnostics = Driver.check_stage(&client, Stage::Access).diagnostics;
        let codes: Vec<_> = diagnostics
            .iter()
            .map(|diagnostic| diagnostic.code)
            .collect();
        assert_eq!(codes, [Some(Code::E0524)], "{path}: {diagnostics:?}");
    }
}

#[test]
fn a_dependency_can_be_checked_using_only_its_published_interface() {
    use ril_source::diag::Code;

    let mut provider = VirtualPackage::new(Unit::Lib);
    provider.entry = "pkg/store.ril".into();
    provider.insert(
        "pkg/model.ril".into(),
        br#"
pub type Cell = .{ var count: int }
pub type Shelf = .{ var ^mut item: Cell }
"#
        .to_vec(),
    );
    provider.insert(
        provider.entry.clone(),
        br#"
use pkg/model
pub type Cell = Model::Cell
pub type Shelf = Model::Shelf
pub type ReadShelf = .{ var ref item: Cell }
pub fn store_ref(ref source: Cell, mut shelf: ReadShelf) &mut -> () { shelf.item = source }
pub fn replace(mut shelf: Shelf, ^mut next: Cell) &mut &^mut -> ref(shelf) Cell {
    let ref previous = ref shelf.item
    shelf.item = ^mut next
    previous
}
pub fn change(via cell: Cell) -> () { cell.count += 1 }
pub fn identity(via cell: Cell) -> infer Cell { cell }
pub fn never_returns() -> () { panic("ended") }
pub eff Meter { fn read() -> int; fn reset() -> () }
pub fn read_meter() @Meter -> int { Meter::read() }
pub eff Extended { ..Meter; fn record() -> () }
pub fn read_extended() @Extended -> int { Meter::read() }
pub opaque type Handle(.{ id: int })
pub fn open() -> new Handle { Handle::(.{ id: 1 }) }
pub fn close(new handle: Handle) @Meter -> () { let _ = Meter::read() }
pub fn apply(via action: fn(via Cell) @& -> infer Cell, via cell: Cell) -> infer Cell { action(cell) }
pub fn observe_after(via action: fn(via Cell) @& -> int, via cell: Cell) -> int {
    let result = action(cell)
    result + cell.count
}
pub fn change_member(mut shelf: .{ via item: Cell }) &mut -> () { shelf.item.count += 1 }
"#
        .to_vec(),
    );
    let artifact = Driver.interface(&provider).unwrap().encode().unwrap();
    let directory = tempfile::tempdir().unwrap();
    let module = directory.path().join("library");
    let package = directory.path().join("pkg");
    fs::create_dir(&module).unwrap();
    fs::create_dir(&package).unwrap();
    fs::write(module.join("store.rili"), artifact).unwrap();
    let entry = package.join("client.ril");
    let oracle_accepts = std::env::var_os("RIL_HORN_ORACLE").map(|oracle| {
        serde_json::from_slice::<bool>(&query(&oracle, "summary-reuse", b"[]").unwrap()).unwrap()
    });
    for (source, expected) in [
        (
            r#"
fn replace_and_read(mut shelf: Store::Shelf, ^mut next: Store::Cell) &mut &^mut -> ref(next) Store::Cell {
    let replace = Store::replace
    let ref previous = replace(mut shelf, ^mut next)
    assert(previous.count >= 0)
    ref shelf.item
}
fn check_new() -> int {
    let mut cell = Store::Cell.{ count: 41 }
    Store::change(mut cell)
    let mut received = Store::identity(new cell)
    received.count += 1
    received.count
}
"#,
            None,
        ),
        (
            r#"
fn relay(ref source: Store::Cell, mut shelf: Store::ReadShelf) &mut -> () {
    Store::store_ref(ref source, mut shelf)
}
"#,
            None,
        ),
        (
            r#"
fn relay(mut source: Store::Cell, mut shelf: Store::ReadShelf) &mut -> () {
    source.count += 1
    let store = Store::store_ref
    store(ref source, mut shelf)
}
"#,
            Some(Code::E0604),
        ),
        (
            r#"
fn after_call(mut shelf: Store::Shelf, ^mut next: Store::Cell) &mut &^mut -> ref(next) Store::Cell {
    Store::replace(mut shelf, ^mut next)
}
"#,
            Some(Code::E0545),
        ),
        (
            r#"
fn replace_twice(mut shelf: Store::Shelf, ^mut discarded: Store::Cell, ^mut next: Store::Cell) &mut &^mut -> () {
    shelf.item = ^mut discarded
    let _ = Store::replace(mut shelf, ^mut next)
}
"#,
            Some(Code::E0527),
        ),
        (
            r#"
fn incompatible(ref cell: Store::Cell) -> () { Store::change(ref cell) }
"#,
            Some(Code::E0520),
        ),
        (
            r#"
fn unreachable_write(mut cell: Store::Cell) &mut -> () {
    Store::never_returns()
    cell.count += 1
}
"#,
            Some(Code::E0527),
        ),
        (
            r#"
fn read() -> int {
    with Store::Meter::read = \-> 42
    let call = Store::read_meter
    call() + Store::read_extended()
}
fn clean() -> () {
    with Store::Meter::read = \-> 42
    let mut handle = Store::open()
    defer Store::close(new handle)
}
"#,
            None,
        ),
        (
            r#"
fn read() -> int {
    with Store::Meter::reset = \-> ()
    Store::read_meter()
}
"#,
            Some(Code::E0612),
        ),
        (
            r#"
fn relay(via action: fn(via Store::Cell) @& -> infer Store::Cell, via cell: Store::Cell) -> infer Store::Cell {
    Store::apply(action, cell)
}
fn run() -> int {
    let identity = \via value: Store::Cell -> value
    let mut cell = Store::Cell.{ count: 40 }
    let ref view = relay(identity, ref cell)
    cell.count += 1
    assert(view.count == 41)
    let mut handed = Store::apply(identity, new cell)
    handed.count += 1
    let mut again = Store::apply(Store::identity, new handed)
    again.count += 1
    again.count
}
"#,
            None,
        ),
        (
            r#"
fn change(via cell: Store::Cell) -> infer Store::Cell { cell.count += 1; cell }
fn invalid(ref cell: Store::Cell) -> int { Store::apply(change, ref cell).count }
"#,
            Some(Code::E0520),
        ),
        (
            r#"
fn take(via cell: Store::Cell) -> int { let moved = new cell; moved.count }
fn invalid() -> int { Store::observe_after(take, Store::Cell.{ count: 21 }) }
"#,
            Some(Code::E0549),
        ),
        (
            r#"
fn relay(via action: fn(via Store::Cell) @& -> int, via cell: Store::Cell) -> int {
    Store::observe_after(action, cell)
}
fn take(via cell: Store::Cell) -> int { let moved = new cell; moved.count }
fn invalid() -> int { relay(take, Store::Cell.{ count: 21 }) }
"#,
            Some(Code::E0549),
        ),
        (
            r#"
fn relay(mut shelf: .{ via item: Store::Cell }) &mut -> () { Store::change_member(mut shelf) }
fn invalid() -> () {
    let mut shelf = .{ item: Store::Cell.{ count: 42 } }
    relay(mut shelf)
}
"#,
            Some(Code::E0520),
        ),
    ] {
        fs::write(&entry, format!("use library/store\n{source}")).unwrap();
        let consumer = ril_driver::load_package(&entry, Unit::Lib).unwrap();
        assert!(!consumer.files.contains_key(Path::new("library/store.ril")));
        assert!(consumer.files.contains_key(Path::new("library/store.rili")));
        assert!(consumer.files.contains_key(Path::new("library/model.rili")));
        let diagnostics = Driver.check_stage(&consumer, Stage::Access).diagnostics;
        if let Some(code) = expected {
            assert!(
                diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.code == Some(code)),
                "{diagnostics:?}"
            );
        } else {
            assert!(diagnostics.is_empty(), "{diagnostics:?}");
            if let Some(accepted) = oracle_accepts {
                assert_eq!(diagnostics.is_empty(), accepted);
            }
        }
    }
}

#[test]
fn wide_via_domains_share_summaries_and_suffixes() {
    let mut package = VirtualPackage::new(Unit::Lib);
    package.entry = "pkg/catalog.ril".into();
    package.insert(
        package.entry.clone(),
        br#"
pub type Item = .{ count: int }
pub fn total(via a: Item, via b: Item, via c: Item, via d: Item, via e: Item,
             via f: Item, via g: Item, via h: Item, via i: Item) -> int {
    a.count + b.count + c.count + d.count + e.count + f.count + g.count + h.count + i.count
}
"#
        .to_vec(),
    );
    let encoded = Driver.interface(&package).unwrap().encode().unwrap();
    let interface = Interface::decode(&encoded).unwrap();
    let export = &interface.functions["pkg/catalog.ril::total"];
    assert_eq!(export.domain.len(), 5_usize.pow(9));
    assert_eq!(encoded, interface.encode().unwrap());
    assert!(encoded.len() < 10_000);

    let json_encoded = interface.encode_json().unwrap();
    let mut wire: serde_json::Value = serde_json::from_slice(&json_encoded).unwrap();
    let domain = wire
        .pointer_mut("/functions/pkg~1catalog.ril::total/domain")
        .unwrap();
    assert_eq!(domain["summaries"].as_array().unwrap().len(), 1);
    let nodes = domain["nodes"].as_array_mut().unwrap();
    assert_eq!(nodes.len(), 10);
    let root = nodes.last_mut().unwrap();
    let child = root.pointer_mut("/Branch/0/1").unwrap();
    *child = serde_json::json!(9);
    let corrupt = serde_json::to_vec(&wire).unwrap();
    assert!(
        Interface::decode(&corrupt)
            .unwrap_err()
            .contains("invalid via branch reference")
    );
}

#[test]
fn interface_roundtrip_is_stable_and_detects_corruption() {
    let suite = parse_suite(Path::new("via.ril"), include_str!("../../../tests/via.ril")).unwrap();
    let baseline = suite
        .cases
        .iter()
        .find(|case| case.id == "changing_published_result_array_length_breaks_compatibility")
        .and_then(|case| case.baseline.as_ref())
        .unwrap();
    let interface = Driver.interface(baseline).unwrap();
    let encoded = interface.encode().unwrap();
    let readback = Interface::decode(&encoded).unwrap();
    assert_eq!(encoded, readback.encode().unwrap());
    let mut corrupt_bin = encoded.clone();
    if let Some(last) = corrupt_bin.last_mut() {
        *last ^= 0xff;
    }
    assert!(Interface::decode(&corrupt_bin).is_err());

    let text = String::from_utf8(interface.encode_json().unwrap()).unwrap();
    let other_version = text.replace(
        &format!("\"format_version\": {FORMAT_VERSION}"),
        "\"format_version\": 0",
    );
    assert!(Interface::decode(other_version.as_bytes()).is_err());
    let corrupted = text.replace("\"array_len\": 2", "\"array_len\": 3");
    assert_ne!(text, corrupted);
    assert!(Interface::decode(corrupted.as_bytes()).is_err());
}

#[test]
fn forwarded_via_identity_publishes_new_guarantee_only_for_new_input() {
    use ril_sema::access::Input;

    let suite = parse_suite(Path::new("via.ril"), include_str!("../../../tests/via.ril")).unwrap();
    let case = suite
        .cases
        .iter()
        .find(|case| case.id == "replacing_inline_via_body_with_forwarding_is_compatible")
        .unwrap();
    let interface = Driver.interface(&case.pkg).unwrap();
    let decoded = Interface::decode(&interface.encode().unwrap()).unwrap();
    assert_eq!(decoded.functions.len(), 1);
    let relay = decoded.functions.values().next().unwrap();
    for input in [Input::Plain, Input::Ref, Input::New] {
        assert!(relay.domain.iter().any(|row| row.modes == [input]));
    }
    for row in &relay.domain {
        assert_eq!(row.summary.constructs, row.modes == [Input::New]);
    }
}

#[test]
fn composite_via_rows_publish_the_attenuated_member_source() {
    use ril_sema::access::{Coordinate, Input, ReturnSource};

    let suite = parse_suite(Path::new("via.ril"), include_str!("../../../tests/via.ril")).unwrap();
    let case = suite
        .cases
        .iter()
        .find(|case| case.id == "record_member_via_can_be_bound_and_forwarded")
        .unwrap();
    let interface = Driver.interface(&case.pkg).unwrap();
    let decoded = Interface::decode(&interface.encode().unwrap()).unwrap();
    let export = decoded.functions.values().next().unwrap();
    assert_eq!(export.domain.len(), 4);
    for (mode, access) in [
        (Input::Plain, Access::Immutable),
        (Input::Ref, Access::Ref),
        (Input::Mut, Access::Ref),
        (Input::Shared, Access::Ref),
    ] {
        let row = export
            .domain
            .iter()
            .find(|row| row.modes == [mode])
            .unwrap();
        assert!(!row.summary.constructs);
        assert_eq!(
            row.summary.return_sources,
            [ReturnSource {
                formal: 0,
                source_path: vec![Coordinate::Field("child".into())],
                result_path: Vec::new(),
                access,
            }]
        );
    }
}

#[test]
fn published_storage_updates_keep_the_destination_and_written_source() {
    use ril_sema::access::{Coordinate, ReturnSource};

    let suite = parse_suite(Path::new("via.ril"), include_str!("../../../tests/via.ril")).unwrap();
    let case = suite
        .cases
        .iter()
        .find(|case| case.id == "a_helper_can_keep_the_same_published_storage_contract")
        .unwrap();
    let interface = Driver.interface(&case.pkg).unwrap();
    let decoded = Interface::decode(&interface.encode().unwrap()).unwrap();
    let export = decoded.functions.values().next().unwrap();
    let [update] = export.summary.storage_updates.as_slice() else {
        panic!("missing forwarded storage update");
    };
    assert!(update.definite);
    assert_eq!(update.formal, 0);
    assert_eq!(update.path, [Coordinate::Field("item".into())]);
    assert_eq!(
        update.sources,
        [ReturnSource {
            formal: 1,
            source_path: Vec::new(),
            result_path: Vec::new(),
            access: Access::Shared,
        }]
    );
}

#[test]
fn storage_contracts_agree_with_lean() {
    use ril_sema::access::Coordinate;

    let Some(oracle) = std::env::var_os("RIL_HORN_ORACLE") else {
        return;
    };
    let suite = parse_suite(Path::new("via.ril"), include_str!("../../../tests/via.ril")).unwrap();
    let output = query(&oracle, "recursive-storage", b"[]").unwrap();
    let contracts = serde_json::from_slice::<Vec<(String, (bool, Vec<usize>))>>(&output).unwrap();
    assert_eq!(contracts.len(), 5);
    for (case_id, (definite, formals)) in contracts {
        let case = suite.cases.iter().find(|case| case.id == case_id).unwrap();
        let interface = Driver.interface(&case.pkg).unwrap();
        let decoded = Interface::decode(&interface.encode().unwrap()).unwrap();
        assert_eq!(decoded.functions.len(), 1, "{case_id}");
        let export = decoded.functions.values().next().unwrap();
        let update = export
            .summary
            .storage_updates
            .iter()
            .find(|update| update.formal == 0 && update.path == [Coordinate::Field("item".into())])
            .unwrap();
        assert_eq!(update.definite, definite, "{case_id}");
        assert!(!update.constructs, "{case_id}");
        assert!(update.callback_returns.is_empty(), "{case_id}");
        assert_eq!(update.sources.len(), formals.len(), "{case_id}");
        for (source, formal) in update.sources.iter().zip(formals) {
            assert_eq!(source.formal, formal, "{case_id}");
            assert_eq!(source.access, Access::Shared, "{case_id}");
            assert!(source.source_path.is_empty(), "{case_id}");
            assert!(source.result_path.is_empty(), "{case_id}");
        }
    }
}

#[test]
fn higher_order_via_rows_publish_callback_reception() {
    use ril_sema::access::{Input, Invocation, InvocationMode};

    let suite = parse_suite(Path::new("via.ril"), include_str!("../../../tests/via.ril")).unwrap();
    let case = suite
        .cases
        .iter()
        .find(|case| case.id == "forwarding_preserves_higher_order_mode_requirements")
        .unwrap();
    let interface = Driver.interface(&case.pkg).unwrap();
    let decoded = Interface::decode(&interface.encode().unwrap()).unwrap();
    let export = decoded.functions.values().next().unwrap();
    let invocation = |mode| Invocation {
        receiver: 0,
        parameter: 0,
        mode,
        preserves_input: false,
    };
    assert_eq!(
        export.summary.invocations,
        [invocation(InvocationMode::Formal(1))]
    );
    assert_eq!(export.domain.len(), 25);
    for row in &export.domain {
        let [_, input]: [Input; 2] = row.modes.as_slice().try_into().unwrap();
        assert_eq!(
            row.summary.invocations,
            [invocation(InvocationMode::Input(input))]
        );
    }
}

#[test]
fn exported_callback_preservation_is_required_only_for_new_reception() {
    use ril_sema::access::Input;

    let suite = parse_suite(Path::new("via.ril"), include_str!("../../../tests/via.ril")).unwrap();
    let case = suite
        .cases
        .iter()
        .find(|case| {
            case.id == "requiring_a_callback_to_preserve_new_qualification_breaks_compatibility"
        })
        .unwrap();
    let interface = Driver.interface(&case.pkg).unwrap();
    let decoded = Interface::decode(&interface.encode().unwrap()).unwrap();
    let export = decoded.functions.values().next().unwrap();
    let [contract] = export.summary.invocations.as_slice() else {
        panic!("missing callback contract");
    };
    assert!(contract.preserves_input);
    for row in &export.domain {
        let [_, input]: [Input; 2] = row.modes.as_slice().try_into().unwrap();
        let [contract] = row.summary.invocations.as_slice() else {
            panic!("missing specialized callback contract");
        };
        assert_eq!(contract.preserves_input, input == Input::New);
    }
}

#[test]
fn exported_callback_results_retain_their_call_entry_sources() {
    use ril_sema::access::{Input, InvocationMode, ReturnSource};

    let suite = parse_suite(Path::new("via.ril"), include_str!("../../../tests/via.ril")).unwrap();
    let case = suite
        .cases
        .iter()
        .find(|case| case.id == "forwarding_preserves_callback_result_sources")
        .unwrap();
    let interface = Driver.interface(&case.pkg).unwrap();
    let decoded = Interface::decode(&interface.encode().unwrap()).unwrap();
    let export = decoded.functions.values().next().unwrap();
    let [result] = export.summary.callback_returns.as_slice() else {
        panic!("missing callback return");
    };
    assert_eq!(result.receiver, 0);
    assert!(result.result_path.is_empty());
    let [argument] = result.arguments.as_slice() else {
        panic!("missing forwarded argument");
    };
    assert_eq!(argument.modes, [InvocationMode::Formal(1)]);
    assert_eq!(
        argument
            .sources
            .iter()
            .map(|source| source.formal)
            .collect::<Vec<_>>(),
        [1]
    );
    let row = export
        .domain
        .iter()
        .find(|row| row.modes == [Input::Plain, Input::Ref])
        .unwrap();
    let [result] = row.summary.callback_returns.as_slice() else {
        panic!("missing specialized return");
    };
    let [argument] = result.arguments.as_slice() else {
        panic!("missing specialized argument");
    };
    assert_eq!(argument.modes, [InvocationMode::Input(Input::Ref)]);
    assert_eq!(
        argument.sources,
        [ReturnSource {
            formal: 1,
            source_path: Vec::new(),
            result_path: Vec::new(),
            access: Access::Ref,
        }]
    );
}

#[test]
fn exported_horn_facts_agree_with_lean() {
    let Some(oracle) = std::env::var_os("RIL_HORN_ORACLE") else {
        return;
    };
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests");
    let mut cases = Vec::new();
    for suite in ril_test::discover(&root).unwrap() {
        for case in suite.cases {
            let inputs: Vec<_> = if let Some(baseline) = &case.baseline {
                vec![("baseline", baseline), ("revision", &case.pkg)]
            } else {
                vec![("source", &case.pkg)]
            };
            for (label, package) in inputs {
                if let Ok(rules) = Driver.horn_rules(package) {
                    cases.push((format!("{}::{} ({label})", suite.name, case.id), rules));
                }
            }
        }
    }
    assert!(cases.len() >= 75);
    let requests = cases.iter().map(|(_, rules)| rules).collect::<Vec<_>>();
    let mut child = Command::new(oracle)
        .arg("batch")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    let input = serde_json::to_vec(&requests).unwrap();
    child.stdin.take().unwrap().write_all(&input).unwrap();
    let output = child.wait_with_output().unwrap();
    assert!(output.status.success());
    let expected: Vec<BTreeSet<usize>> = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(cases.len(), expected.len());
    for ((case, rules), expected) in cases.into_iter().zip(expected) {
        assert_eq!(horn::solve(&rules), expected, "{case}");
    }
}

#[test]
fn exported_summaries_and_via_domains_agree_with_lean() {
    use ril_sema::access::{
        CallbackArgument, CallbackReturn, Coordinate, Input, InvocationMode, ModeAxis,
        ReturnAllocation, ReturnSource, SnapshotArgument, SnapshotCall, SnapshotGraph,
        SnapshotInput, SnapshotOrigin, SnapshotProjection, SnapshotProvider, StorageStep,
        StorageTransfer, StorageUpdate, Summary, ViaDomain,
    };
    use serde_json::{Value, json};

    let Some(oracle) = std::env::var_os("RIL_HORN_ORACLE") else {
        return;
    };
    let source = include_str!("../../../tests/via.ril");
    let suite = parse_suite(Path::new("via.ril"), source).unwrap();
    let mut summaries = vec![
        Summary::default(),
        Summary {
            retained: vec![0],
            effects: vec!["io".into()],
            ..Summary::default()
        },
        Summary {
            return_sources: vec![ReturnSource {
                formal: 2,
                source_path: vec![Coordinate::Field("count".into())],
                result_path: vec![Coordinate::Index("0".into())],
                access: Access::Ref,
            }],
            constructs: true,
            ..Summary::default()
        },
    ];
    let mut copy_library = VirtualPackage::new(Unit::Lib);
    copy_library.insert(
        copy_library.entry.clone(),
        b"pub fn duplicate(values: []int) -> new []int { clone(values) }".to_vec(),
    );
    summaries.extend(
        Driver
            .interface(&copy_library)
            .unwrap()
            .functions
            .into_values()
            .map(|export| export.summary),
    );
    for live_callable_state in [false, true] {
        summaries.push(Summary {
            snapshot_returns: vec![SnapshotProjection {
                path: vec![Coordinate::Index("0".into())],
                origin: SnapshotOrigin {
                    source: None,
                    provider: None,
                    access: Access::Immutable,
                    new: false,
                    call_scoped: false,
                    forwarded: false,
                    detached: false,
                },
                qualified: false,
                live_callable_state,
                allocation: None,
                observation: None,
            }],
            ..Summary::default()
        });
    }
    let calls_provider = |provider| SnapshotCall {
        factory_steps: Vec::new(),
        receiver: ModeAxis {
            parameter: 0,
            path: Vec::new(),
        },
        recursive_path: None,
        arguments: vec![SnapshotArgument {
            position: 0,
            mode: Some(Input::Plain),
            whole_graph: false,
            graph: SnapshotGraph {
                new_root: false,
                environment: false,
                replaced: Vec::new(),
                members: Vec::new(),
                roots: vec![SnapshotOrigin {
                    source: None,
                    access: Access::Immutable,
                    new: false,
                    call_scoped: false,
                    forwarded: false,
                    detached: false,
                    provider: Some(provider),
                }],
            },
        }],
    };
    let cyclic_summary = |root, constrained| {
        let inputs = if constrained {
            vec![SnapshotInput {
                formal: 1,
                path: Vec::new(),
                replaced: Vec::new(),
            }]
        } else {
            Vec::new()
        };
        let mut snapshot_providers = vec![
            SnapshotProvider {
                via_parameters: vec![false, false],
                inputs: Vec::new(),
                calls: vec![calls_provider(1 - root)],
                captured_slots: Vec::new(),
                storage_updates: Vec::new(),
                storage_flow: None,
                returns: Vec::new(),
                callback_returns: Vec::new(),
                returns_new: false,
            },
            SnapshotProvider {
                via_parameters: vec![false, false],
                inputs,
                calls: vec![calls_provider(root)],
                captured_slots: Vec::new(),
                storage_updates: Vec::new(),
                storage_flow: None,
                returns: Vec::new(),
                callback_returns: Vec::new(),
                returns_new: false,
            },
        ];
        if root == 1 {
            snapshot_providers.swap(0, 1);
        }
        Summary {
            snapshot_providers,
            snapshot_calls: vec![calls_provider(root)],
            ..Summary::default()
        }
    };
    let old = cyclic_summary(0, false);
    let renumbered = cyclic_summary(1, false);
    let tightened = cyclic_summary(1, true);
    assert!(old.subsumes(&renumbered) && renumbered.subsumes(&old));
    assert!(!old.subsumes(&tightened) && tightened.subsumes(&old));
    summaries.extend([old, renumbered, tightened]);
    let shared = ReturnAllocation {
        path: vec![Coordinate::Field("next".into())],
        index: 0,
        access: Access::Shared,
        new: false,
        qualified: false,
        summarized: true,
        clone_member: false,
        array_len: None,
        array_extent: None,
    };
    for index in [0, 1] {
        let allocations = vec![
            shared.clone(),
            ReturnAllocation {
                path: vec![
                    Coordinate::Field("next".into()),
                    Coordinate::Field("next".into()),
                ],
                index,
                ..shared.clone()
            },
        ];
        summaries.push(Summary {
            return_allocations: allocations.clone(),
            storage_updates: vec![StorageUpdate {
                formal: 0,
                path: vec![Coordinate::Field("head".into())],
                sources: Vec::new(),
                callback_returns: Vec::new(),
                snapshot_projections: Vec::new(),
                allocations: allocations.clone(),
                definite: true,
                constructs: false,
            }],
            ..Summary::default()
        });
        summaries.push(Summary {
            callback_returns: vec![CallbackReturn {
                invocation: 0,
                receiver: 0,
                receiver_path: Vec::new(),
                source_path: Vec::new(),
                result_path: Vec::new(),
                cap: None,
                arguments: vec![CallbackArgument {
                    position: 0,
                    modes: vec![InvocationMode::Input(Input::Shared)],
                    sources: Vec::new(),
                    callback_returns: Vec::new(),
                    snapshot_projections: Vec::new(),
                    allocations,
                    constructs: false,
                }],
            }],
            ..Summary::default()
        });
    }
    let mut domains = vec![ViaDomain::default()];
    for case in suite.cases {
        for pkg in case.baseline.iter().chain(std::iter::once(&case.pkg)) {
            if let Ok(interface) = Driver.interface(pkg) {
                let decoded = Interface::decode(&interface.encode().unwrap()).unwrap();
                for function in decoded.functions.into_values() {
                    summaries.push(function.summary);
                    for instance in &function.domain {
                        if !summaries.contains(instance.summary) {
                            summaries.push(instance.summary.clone());
                        }
                    }
                    if !domains.contains(&function.domain) {
                        domains.push(function.domain);
                    }
                }
            }
        }
    }
    let effects: std::collections::BTreeMap<_, _> = summaries
        .iter()
        .flat_map(|summary| &summary.effects)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .enumerate()
        .map(|(index, effect)| (effect, index))
        .collect();
    let wire_coordinate = |coordinate: &Coordinate| match coordinate {
        Coordinate::Field(key) => json!({"kind": "field", "key": key}),
        Coordinate::Index(key) => json!({"kind": "index", "key": key}),
        Coordinate::Dynamic => json!({"kind": "dynamic", "key": ""}),
        Coordinate::MapKey => json!({"kind": "map-key", "key": ""}),
        Coordinate::ArrayTail(start) => json!({"kind": "array-tail", "key": start.to_string()}),
    };
    let wire_source = |source: &ReturnSource| {
        json!({
            "formal": source.formal,
            "source_path": source.source_path.iter().map(wire_coordinate).collect::<Vec<_>>(),
            "result_path": source.result_path.iter().map(wire_coordinate).collect::<Vec<_>>(),
            "access": access_number(source.access),
        })
    };
    let wire_snapshot_input = |input: &SnapshotInput| {
        json!({
            "formal": input.formal,
            "path": input.path.iter().map(wire_coordinate).collect::<Vec<_>>(),
            "replaced": input.replaced.iter()
                .map(|path| path.iter().map(wire_coordinate).collect::<Vec<_>>())
                .collect::<Vec<_>>(),
        })
    };
    fn wire_snapshot_origin(root: &SnapshotOrigin) -> Value {
        json!({
            "shape": [&json!(root.source), &json!(root.access), &json!(root.new), &json!(root.call_scoped), &json!(root.forwarded), &json!(root.detached)],
            "provider": root.provider,
        })
    }
    fn wire_projection(projection: &SnapshotProjection) -> Value {
        json!({
            "shape": [&json!(projection.path), &json!(projection.qualified), &json!(projection.allocation), &json!(projection.observation)],
            "live_callable_state": projection.live_callable_state,
            "origin": wire_snapshot_origin(&projection.origin),
        })
    }
    fn wire_callback_return(callback: &CallbackReturn) -> Value {
        fn take_projections(callback: &mut CallbackReturn, projections: &mut Vec<Vec<Value>>) {
            for argument in &mut callback.arguments {
                projections.push(
                    std::mem::take(&mut argument.snapshot_projections)
                        .iter()
                        .map(wire_projection)
                        .collect(),
                );
                for nested in &mut argument.callback_returns {
                    take_projections(nested, projections);
                }
            }
        }
        let mut shape = callback.clone();
        let mut projections = Vec::new();
        take_projections(&mut shape, &mut projections);
        json!({"shape": shape, "projections": projections})
    }
    fn wire_snapshot_nodes(
        graph: &SnapshotGraph,
        path: &mut Vec<Coordinate>,
        nodes: &mut Vec<Value>,
    ) {
        let roots: Vec<_> = graph.roots.iter().map(wire_snapshot_origin).collect();
        nodes.push(json!({
            "shape": [&json!(path), &json!(graph.new_root), &json!(graph.environment), &json!(graph.replaced)],
            "roots": roots,
        }));
        for (key, child) in &graph.members {
            path.push(key.clone());
            wire_snapshot_nodes(child, path, nodes);
            path.pop();
        }
    }
    let wire_snapshot_arguments = |arguments: &[SnapshotArgument]| {
        arguments.iter().map(|argument| {
            let mut graph = Vec::new();
            wire_snapshot_nodes(&argument.graph, &mut Vec::new(), &mut graph);
            json!({
                "shape": [&json!(argument.position), &json!(argument.mode), &json!(argument.whole_graph)],
                "graph": graph,
            })
        }).collect::<Vec<_>>()
    };
    let wire_snapshot_call = |call: &SnapshotCall| {
        let factory_steps: Vec<_> = call
            .factory_steps
            .iter()
            .map(|step| {
                json!({
                    "shape": [&json!(step.path), &json!(step.cap)],
                    "arguments": wire_snapshot_arguments(&step.arguments),
                })
            })
            .collect();
        json!({
            "shape": [&json!(call.receiver), &json!(call.recursive_path)],
            "arguments": wire_snapshot_arguments(&call.arguments),
            "factory_steps": factory_steps,
        })
    };
    let wire_storage_update = |update: &StorageUpdate| {
        json!({
            "formal": update.formal,
            "path": update.path.iter().map(wire_coordinate).collect::<Vec<_>>(),
            "sources": update.sources.iter().map(wire_source).collect::<Vec<_>>(),
            "callback_returns": update.callback_returns.iter().map(wire_callback_return).collect::<Vec<_>>(),
            "snapshot_projections": update.snapshot_projections.iter().map(wire_projection).collect::<Vec<_>>(),
            "allocations": update.allocations,
            "definite": update.definite,
            "constructs": update.constructs,
        })
    };
    let wire_storage_operand = |operand: &CallbackArgument| {
        json!({
            "shape": [&json!(operand.position), &json!(operand.modes), &json!(operand.sources), &json!(operand.allocations), &json!(operand.constructs)],
            "projections": operand.snapshot_projections.iter().map(wire_projection).collect::<Vec<_>>(),
            "callback_returns": operand.callback_returns.iter().map(wire_callback_return).collect::<Vec<_>>(),
        })
    };
    let wire_storage_step = |step: &StorageStep| match step {
        StorageStep::Write(update) => {
            json!({"write": wire_storage_update(update), "invoke": null, "read": null})
        }
        StorageStep::Invoke {
            receiver,
            arguments,
        } => json!({"write": null, "read": null, "invoke": {
            "receiver": wire_storage_operand(receiver),
            "arguments": arguments.iter().map(wire_storage_operand).collect::<Vec<_>>(),
        }}),
        StorageStep::Read {
            index,
            base,
            coordinate,
            mode,
        } => json!({"write": null, "invoke": null, "read": {
            "shape": [json!(index), json!(coordinate), json!(mode)],
            "base": wire_storage_operand(base),
        }}),
        StorageStep::WriteObserved {
            parent,
            member,
            value,
            definite,
        } => json!({
            "write_observed": {
                "shape": [json!(parent), json!(member)],
                "value": wire_storage_operand(value),
                "definite": definite,
            }
        }),
        StorageStep::Derive {
            index,
            base,
            updater,
        } => json!({
            "derivation": {
                "index": index,
                "base": wire_storage_operand(base),
                "updater": wire_storage_operand(updater),
            }
        }),
        StorageStep::Clone { index, base } => json!({"read": {
            "shape": [json!("clone"), json!(index)],
            "base": wire_storage_operand(base),
        }}),
    };
    let wire_storage_flow = |flow: &StorageTransfer| match flow {
        StorageTransfer::Paths(paths) => {
            json!({"interleaved": false, "paths": paths.iter().map(|path| path.iter().map(wire_storage_step).collect::<Vec<_>>()).collect::<Vec<_>>() })
        }
        StorageTransfer::Interleaved(steps) => {
            json!({"interleaved": true, "paths": [steps.iter().map(wire_storage_step).collect::<Vec<_>>()] })
        }
    };
    let wire = |summary: &Summary| -> Value {
        let effects: Vec<_> = summary
            .effects
            .iter()
            .map(|name| effects.get(name).copied().unwrap())
            .collect();
        let return_sources: Vec<_> = summary.return_sources.iter().map(wire_source).collect();
        let snapshot_inputs: Vec<_> = summary
            .snapshot_inputs
            .iter()
            .map(wire_snapshot_input)
            .collect();
        let snapshot_calls: Vec<_> = summary
            .snapshot_calls
            .iter()
            .map(wire_snapshot_call)
            .collect();
        let snapshot_providers: Vec<_> = summary
            .snapshot_providers
            .iter()
            .map(|provider| {
                json!({
                    "via_parameters": provider.via_parameters,
                    "inputs": provider.inputs.iter().map(wire_snapshot_input).collect::<Vec<_>>(),
                    "calls": provider.calls.iter().map(wire_snapshot_call).collect::<Vec<_>>(),
                    "captured_slots": provider.captured_slots,
                    "storage_updates": provider.storage_updates.iter().map(wire_storage_update).collect::<Vec<_>>(),
                    "storage_flow": provider.storage_flow.as_ref().map(wire_storage_flow),
                    "returns": provider.returns.iter().map(wire_projection).collect::<Vec<_>>(),
                    "callback_returns": provider.callback_returns.iter().map(wire_callback_return).collect::<Vec<_>>(),
                    "returns_new": provider.returns_new,
                })
            })
            .collect();
        let invocations: Vec<_> = summary
            .invocations
            .iter()
            .map(|invoke| {
                let (input, formal) = match invoke.mode {
                    InvocationMode::Input(input) => (Some(input), None),
                    InvocationMode::Formal(formal) => (None, Some(formal)),
                };
                json!({
                    "receiver": invoke.receiver,
                    "parameter": invoke.parameter,
                    "input": input,
                    "formal": formal,
                    "preserves_input": invoke.preserves_input,
                })
            })
            .collect();
        let storage_updates: Vec<_> = summary
            .storage_updates
            .iter()
            .map(wire_storage_update)
            .collect();
        json!({
            "writes": summary.writes,
            "retained": summary.retained,
            "independent_retention": summary.independent_retention,
            "snapshot_inputs": snapshot_inputs,
            "snapshot_calls": snapshot_calls,
            "snapshot_providers": snapshot_providers,
            "snapshot_returns": summary.snapshot_returns.iter().map(wire_projection).collect::<Vec<_>>(),
            "return_sources": return_sources,
            "return_allocations": summary.return_allocations,
            "effects": effects,
            "effect_uses": summary.effect_uses,
            "invocations": invocations,
            "mode_calls": summary.mode_calls,
            "invoked": summary.invoked,
            "callback_returns": summary.callback_returns.iter().map(wire_callback_return).collect::<Vec<_>>(),
            "storage_updates": storage_updates,
            "storage_flow": summary.storage_flow.as_ref().map(wire_storage_flow),
            "captures": summary.captures,
            "constructs": summary.constructs,
            "nonreturning": summary.nonreturning,
        })
    };
    let cases: Vec<_> = summaries
        .iter()
        .flat_map(|baseline| summaries.iter().map(move |revision| (baseline, revision)))
        .collect();
    let input: Vec<_> = cases
        .iter()
        .map(|(baseline, revision)| json!({"baseline": wire(baseline), "revision": wire(revision)}))
        .collect();
    let expected: Vec<_> = cases
        .iter()
        .map(|(baseline, revision)| baseline.subsumes(revision))
        .collect();

    let output = query(&oracle, "summary", &serde_json::to_vec(&input).unwrap()).unwrap();
    assert_eq!(
        serde_json::from_slice::<Vec<bool>>(&output).unwrap(),
        expected
    );

    assert!(domains.len() > 4);
    let domain_wire = |rows: &ViaDomain| {
        rows.iter()
            .map(|row| json!({"modes": row.modes, "summary": wire(row.summary)}))
            .collect::<Vec<_>>()
    };
    let cases: Vec<_> = domains
        .iter()
        .flat_map(|baseline| domains.iter().map(move |revision| (baseline, revision)))
        .collect();
    let input: Vec<_> = cases.iter().map(|(baseline, revision)| {
        json!({"baseline": domain_wire(baseline), "revision": domain_wire(revision)})
    }).collect();
    let actual = query(&oracle, "domain", &serde_json::to_vec(&input).unwrap()).unwrap();
    let expected: Vec<_> = cases
        .iter()
        .map(|(baseline, revision)| baseline.subsumes(revision))
        .collect();
    assert_eq!(
        serde_json::from_slice::<Vec<bool>>(&actual).unwrap(),
        expected
    );
}

fn access_number(access: Access) -> u8 {
    match access {
        Access::Immutable => 0,
        Access::Ref => 1,
        Access::Mut => 2,
        Access::Shared => 3,
    }
}

#[test]
fn path_attenuation_agrees_with_lean() {
    let Some(oracle) = std::env::var_os("RIL_HORN_ORACLE") else {
        return;
    };
    const MODES: [Access; 4] = [Access::Immutable, Access::Ref, Access::Mut, Access::Shared];
    let mut paths = Vec::new();
    let mut depth = vec![Vec::new()];
    for _ in 0..4 {
        depth = depth
            .into_iter()
            .flat_map(|prefix| {
                MODES.map(|mode| {
                    let mut path = prefix.clone();
                    path.push(mode);
                    path
                })
            })
            .collect();
        paths.extend(depth.iter().cloned());
    }
    let input: Vec<_> = paths
        .iter()
        .map(|path| path.iter().copied().map(access_number).collect::<Vec<_>>())
        .collect();
    let expected: Vec<_> = paths
        .iter()
        .map(|path| {
            let (&root, members) = path.split_first().unwrap();
            access_number(members.iter().copied().fold(root, Access::project))
        })
        .collect();
    let mut child = Command::new(oracle)
        .arg("path-access")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .take()
        .unwrap()
        .write_all(&serde_json::to_vec(&input).unwrap())
        .unwrap();
    let output = child.wait_with_output().unwrap();
    assert!(output.status.success());
    assert_eq!(
        serde_json::from_slice::<Vec<u8>>(&output.stdout).unwrap(),
        expected
    );
}

#[test]
fn call_entry_examples_agree_with_lean() {
    let Some(oracle) = std::env::var_os("RIL_HORN_ORACLE") else {
        return;
    };
    let suite = parse_suite(
        Path::new("access.ril"),
        include_str!("../../../tests/access.ril"),
    )
    .unwrap();
    let output = query(&oracle, "call-entry", b"[]").unwrap();
    let results: Vec<(String, bool)> = serde_json::from_slice(&output).unwrap();
    assert_eq!(results.len(), 4);
    for (name, accepted) in results {
        let case = suite.cases.iter().find(|case| case.id == name).unwrap();
        let diagnostics = Driver.check_stage(&case.pkg, Stage::Access).diagnostics;
        assert_eq!(diagnostics.is_empty(), accepted, "{name}: {diagnostics:?}");
    }
}

#[test]
fn ctl_linearity_examples_agree_with_lean() {
    let Some(oracle) = std::env::var_os("RIL_HORN_ORACLE") else {
        return;
    };
    let compile = parse_suite(
        Path::new("isolation.ril"),
        include_str!("../../../tests/concurrency_isolation.ril"),
    )
    .unwrap();
    let runtime = parse_suite(
        Path::new("fifo.ril"),
        include_str!("../../../tests/concurrency_fifo.ril"),
    )
    .unwrap();
    let output = query(&oracle, "ctl-linearity", b"[]").unwrap();
    let results: Vec<(String, bool)> = serde_json::from_slice(&output).unwrap();
    assert_eq!(results.len(), 11);
    let temporary = tempfile::tempdir().unwrap();
    for (name, accepted) in results {
        let case = compile
            .cases
            .iter()
            .chain(&runtime.cases)
            .find(|case| case.id == name)
            .unwrap();
        if matches!(case.mode, CaseMode::RunPass) {
            let executable = temporary.path().join(&name);
            Driver.build_aot(&case.pkg, &executable).unwrap();
            let execution = run_worker(&mut Command::new(executable)).unwrap();
            assert_eq!(
                execution.status.success(),
                accepted,
                "{name}: {:?}",
                String::from_utf8_lossy(&execution.stderr)
            );
        } else {
            let diagnostics = Driver.check_stage(&case.pkg, Stage::Access).diagnostics;
            assert_eq!(diagnostics.is_empty(), accepted, "{name}: {diagnostics:?}");
        }
    }
}

#[test]
fn draft_path_updates_agree_with_lean() {
    let Some(oracle) = std::env::var_os("RIL_HORN_ORACLE") else {
        return;
    };
    let runtime = parse_suite(
        Path::new("effects.ril"),
        include_str!("../../../tests/runtime_effects.ril"),
    )
    .unwrap();
    let output = query(&oracle, "draft", b"[]").unwrap();
    let results: Vec<(String, Option<Vec<u64>>)> = serde_json::from_slice(&output).unwrap();
    assert_eq!(results.len(), 6);
    let temporary = tempfile::tempdir().unwrap();
    for (name, observation) in results {
        let values = observation.unwrap_or_else(|| panic!("{name}: Lean produced no observation"));
        let expected = format!(
            "{}\n",
            values
                .iter()
                .map(u64::to_string)
                .collect::<Vec<_>>()
                .join(":")
        );
        let case = runtime.cases.iter().find(|case| case.id == name).unwrap();
        let executable = temporary.path().join(&name);
        Driver.build_aot(&case.pkg, &executable).unwrap();
        // Each source case also checks identical AOT and JIT results in the
        // main suite, whose executable serves as the JIT worker.
        let output = run_worker(&mut Command::new(executable)).unwrap();
        let stderr = String::from_utf8_lossy(&output.stderr);
        if let CaseMode::RunPanic(Some(message)) = &case.mode {
            assert_eq!(output.status.code(), Some(1), "{name}: {stderr}");
            assert!(
                stderr.lines().any(|line| {
                    line.strip_prefix("[RIL_RT_PANIC]").map(str::trim) == Some(message)
                }),
                "{name}: {stderr}"
            );
        } else {
            assert!(output.status.success(), "{name}: {stderr}");
        }
        assert_eq!(output.stdout, expected.as_bytes(), "{name}");
    }
}

#[test]
fn draft_root_and_constructor_checks_agree_with_lean() -> Result<(), Box<dyn std::error::Error>> {
    check_access_examples("draft-roots", 9)
}

#[test]
fn access_ledger_examples_agree_with_lean() -> Result<(), Box<dyn std::error::Error>> {
    check_access_examples("access-ledger", 53)
}

#[test]
fn visibility_examples_agree_with_lean() -> Result<(), Box<dyn std::error::Error>> {
    check_access_examples("visibility", 12)
}

#[test]
fn boundary_examples_agree_with_lean() -> Result<(), Box<dyn std::error::Error>> {
    check_access_examples("boundary", 7)
}

#[test]
fn call_authority_examples_agree_with_lean() -> Result<(), Box<dyn std::error::Error>> {
    check_access_examples("call-authority", 40)
}

#[test]
fn published_call_obligations_agree_with_lean() -> Result<(), Box<dyn std::error::Error>> {
    let Some(oracle) = std::env::var_os("RIL_HORN_ORACLE") else {
        return Ok(());
    };
    let suite = parse_suite(
        Path::new("access.ril"),
        include_str!("../../../tests/access.ril"),
    )?;
    let output = query(&oracle, "call-obligations", b"[]")?;
    type Obligations = (Vec<usize>, Vec<usize>);
    let expected: Vec<(String, Obligations)> = serde_json::from_slice(&output)?;
    assert_eq!(expected.len(), 4);
    for (case_id, (writes, retained)) in expected {
        let case = suite.cases.iter().find(|case| case.id == case_id).unwrap();
        let interface = Driver.interface(&case.pkg).unwrap();
        let decoded = Interface::decode(&interface.encode()?)?;
        assert_eq!(decoded.functions.len(), 1, "{case_id}");
        let summary = &decoded.functions.values().next().unwrap().summary;
        assert_eq!(summary.writes, writes, "{case_id}");
        let returned: BTreeSet<_> = summary
            .return_sources
            .iter()
            .filter(|source| source.access == Access::Shared)
            .map(|source| source.formal)
            .collect();
        let retained: BTreeSet<_> = retained.into_iter().collect();
        assert_eq!(returned, retained, "{case_id}: returned writers");
        let all_retained: BTreeSet<_> = returned
            .into_iter()
            .chain(summary.retained.iter().copied())
            .collect();
        assert_eq!(all_retained, retained, "{case_id}: retained writers");
    }
    Ok(())
}

#[test]
fn handoff_examples_agree_with_lean() -> Result<(), Box<dyn std::error::Error>> {
    check_access_examples("handoff", 9)
}

#[test]
fn provenance_examples_agree_with_lean() -> Result<(), Box<dyn std::error::Error>> {
    check_access_examples("provenance", 34)
}

#[test]
fn graph_authority_examples_agree_with_lean() -> Result<(), Box<dyn std::error::Error>> {
    check_access_examples("graph", 25)
}

#[test]
fn cleanup_composition_examples_agree_with_lean() -> Result<(), Box<dyn std::error::Error>> {
    check_access_examples("cleanup-composition", 3)
}

#[test]
fn scoped_resource_examples_agree_with_lean() -> Result<(), Box<dyn std::error::Error>> {
    check_access_examples("scoped", 12)
}

#[test]
fn summary_signatures_agree_with_lean() -> Result<(), Box<dyn std::error::Error>> {
    check_access_examples("summary-signatures", 21)
}

#[test]
fn result_patterns_agree_with_lean() -> Result<(), Box<dyn std::error::Error>> {
    check_access_examples("result-patterns", 62)
}

fn check_access_examples(operation: &str, count: usize) -> Result<(), Box<dyn std::error::Error>> {
    let Some(oracle) = std::env::var_os("RIL_HORN_ORACLE") else {
        return Ok(());
    };
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests");
    let suites = ril_test::discover(&root)?;
    let output = query(&oracle, operation, b"[]")?;
    let results: Vec<(String, bool)> = serde_json::from_slice(&output)?;
    assert_eq!(results.len(), count);
    for (name, accepted) in results {
        let case = suites
            .iter()
            .flat_map(|suite| &suite.cases)
            .find(|case| case.id == name)
            .ok_or_else(|| format!("no Ril case named {name} for Lean operation {operation}"))?;
        let diagnostics = match &case.baseline {
            Some(baseline) => Driver.check_compat(baseline, &case.pkg).diagnostics,
            None => Driver.check_stage(&case.pkg, Stage::Access).diagnostics,
        };
        assert_eq!(diagnostics.is_empty(), accepted, "{name}: {diagnostics:?}");
        if let CaseMode::CompileFail(code) | CaseMode::CompatFail(code) = case.mode {
            assert!(
                diagnostics.iter().any(|diag| diag.code == Some(code)),
                "{name}: {diagnostics:?}"
            );
        }
    }
    Ok(())
}

fn query(
    oracle: &OsStr,
    operation: &str,
    input: &[u8],
) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
    let mut child = Command::new(oracle)
        .arg(operation)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()?;
    child
        .stdin
        .take()
        .ok_or("missing oracle input pipe")?
        .write_all(input)?;
    let output = child.wait_with_output()?;
    if output.status.success() {
        Ok(output.stdout)
    } else {
        Err(format!("Lean oracle failed for {operation}").into())
    }
}

#[test]
fn nine_param_via_forwarding_builds_compact_mdd_without_cartesian_explosion() {
    let source = r#"
pub type Box = .{ var value: int }

pub fn pick_first(
    via a: Box,
    via b: Box,
    via c: Box,
    via d: Box,
    via e: Box,
    via f: Box,
    via g: Box,
    via h: Box,
    via i: Box,
) -> infer Box {
    let _ = b.value + c.value + d.value + e.value + f.value + g.value + h.value + i.value
    a
}
"#;
    let mut pkg = VirtualPackage::new(Unit::Lib);
    pkg.insert(pkg.entry.clone(), source.as_bytes().to_vec());
    let start = std::time::Instant::now();
    let iface = Driver.interface(&pkg).unwrap();
    let elapsed = start.elapsed();
    assert!(
        elapsed.as_secs_f64() < 2.0,
        "9-param via MDD should compile in milliseconds, took {elapsed:?}"
    );
    let export = iface
        .functions
        .get("pkg/main.ril::pick_first")
        .expect("pick_first export");
    assert_eq!(export.domain.len_u128(), 5_u128.pow(9));
    assert!(export.domain.uses_graph());
    let encoded = iface.encode().unwrap();
    let decoded = Interface::decode(&encoded).unwrap();
    assert!(iface.compare(&decoded).is_empty());
}
