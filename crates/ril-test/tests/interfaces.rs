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
fn compound_result_obligations_survive_an_interface_only_boundary() {
    use ril_base::diag::Code;

    let provider_source = br#"
fn get(value: int) -> new !<int, str> { Ok(value) }
pub nominal type Packet<T> = .{ payload: T }
pub fn packet() -> new Packet<!<int, str>> { Packet.{ payload: get(1) } }
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
    use ril_base::diag::Code;

    let provider_source = br#"
pub nominal type Node = .{ var value: int, var ^mut next: ?Node }
pub type Shelf = .{ var mut head: Node }
pub type Pair = .{ var ^mut left: Node, var ^mut right: Node }
pub fn build(^mut tail: Node, count: int) &mut &^mut &return(^mut tail) -> new Node {
    var ^mut head = tail
    for 0..count as i {
        let mut node = Node.{ value: i, next: Some(^mut head) }
        node.value += 1
        head = ^mut node
    }
    head.value += 1
    Node.{ value: 0, next: Some(^mut head) }
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
                "let mut shelf = Chain::Shelf.{ head: Chain::Node.{ value: 0, next: None } }\nChain::store(mut shelf, ^mut tail, count)",
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
                    "let mut spare = Chain::Node.{ value: 0, next: None }",
                    Vec::new(),
                ),
            ] {
                let read = read_chain(head, format!("copy(mut {target}, ref link9)"), "()");
                let source = format!(
                    "use library/chain\n\
                     fn identity(via node: Chain::Node) -> infer Chain::Node {{ node }}\n\
                     fn copy(mut target: Chain::Node, ref reader: Chain::Node) &mut -> () {{ target.value = reader.value }}\n\
                     fn run(count: int) -> () {{\n\
                        let mut tail = Chain::Node.{{ value: 1, next: None }}\n\
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
                "let mut spare = Chain::Node.{ value: 0, next: None }",
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
                    let mut tail = Chain::Node.{{ value: 1, next: None }}\n\
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
    let mut tail = Chain::Node.{ value: 1, next: None }
    let mut first = Chain::Node.{ value: 2, next: None }
    let mut second = Chain::Node.{ value: 3, next: None }
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
    use ril_base::diag::Code;

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
pub opaque type Handle use(close) = .{ id: int }
pub fn open() -> new Handle { Handle.{ id: 1 } }
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
    use handle = Store::open()
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
    let mut owned = Store::apply(identity, new cell)
    owned.count += 1
    let mut again = Store::apply(Store::identity, new owned)
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
fn interface_roundtrip_is_stable_and_detects_corruption() {
    let suite = parse_suite(
        Path::new("via.ril"),
        include_str!("../../../tests/08_via_compat/via.ril"),
    )
    .unwrap();
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
    let text = String::from_utf8(encoded).unwrap();
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
fn forwarded_via_identity_publishes_new_guarantee_only_for_owned_input() {
    use ril_sema::access::Input;

    let suite = parse_suite(
        Path::new("via.ril"),
        include_str!("../../../tests/08_via_compat/via.ril"),
    )
    .unwrap();
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

    let suite = parse_suite(
        Path::new("via.ril"),
        include_str!("../../../tests/08_via_compat/via.ril"),
    )
    .unwrap();
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

    let suite = parse_suite(
        Path::new("via.ril"),
        include_str!("../../../tests/08_via_compat/via.ril"),
    )
    .unwrap();
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
    let suite = parse_suite(
        Path::new("via.ril"),
        include_str!("../../../tests/08_via_compat/via.ril"),
    )
    .unwrap();
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

    let suite = parse_suite(
        Path::new("via.ril"),
        include_str!("../../../tests/08_via_compat/via.ril"),
    )
    .unwrap();
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

    let suite = parse_suite(
        Path::new("via.ril"),
        include_str!("../../../tests/08_via_compat/via.ril"),
    )
    .unwrap();
    let case = suite
        .cases
        .iter()
        .find(|case| case.id == "requiring_a_callback_to_preserve_ownership_breaks_compatibility")
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

    let suite = parse_suite(
        Path::new("via.ril"),
        include_str!("../../../tests/08_via_compat/via.ril"),
    )
    .unwrap();
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
        CallbackArgument, CallbackReturn, Coordinate, Input, Instance, InvocationMode,
        ReturnAllocation, ReturnSource, StorageUpdate, Summary,
    };
    use serde_json::{Value, json};

    let Some(oracle) = std::env::var_os("RIL_HORN_ORACLE") else {
        return;
    };
    let source = include_str!("../../../tests/08_via_compat/via.ril");
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
    let shared = ReturnAllocation {
        path: vec![Coordinate::Field("next".into())],
        index: 0,
        access: Access::Shared,
        new: false,
        qualified: false,
        summarized: true,
        array_len: None,
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
                    allocations,
                    constructs: false,
                }],
            }],
            ..Summary::default()
        });
    }
    let mut domains = vec![Vec::new()];
    for case in suite.cases {
        for pkg in case.baseline.iter().chain(std::iter::once(&case.pkg)) {
            if let Ok(interface) = Driver.interface(pkg) {
                let decoded = Interface::decode(&interface.encode().unwrap()).unwrap();
                for function in decoded.functions.into_values() {
                    summaries.push(function.summary);
                    for instance in &function.domain {
                        if !summaries.contains(&instance.summary) {
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
    };
    let wire_source = |source: &ReturnSource| {
        json!({
            "formal": source.formal,
            "source_path": source.source_path.iter().map(wire_coordinate).collect::<Vec<_>>(),
            "result_path": source.result_path.iter().map(wire_coordinate).collect::<Vec<_>>(),
            "access": access_number(source.access),
        })
    };
    let wire = |summary: &Summary| -> Value {
        let effects: Vec<_> = summary
            .effects
            .iter()
            .map(|name| effects.get(name).copied().unwrap())
            .collect();
        let return_sources: Vec<_> = summary.return_sources.iter().map(wire_source).collect();
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
            .map(|update| {
                json!({
                    "formal": update.formal,
                    "path": update.path.iter().map(wire_coordinate).collect::<Vec<_>>(),
                    "sources": update.sources.iter().map(wire_source).collect::<Vec<_>>(),
                    "callback_returns": update.callback_returns,
                    "allocations": update.allocations,
                    "definite": update.definite,
                    "constructs": update.constructs,
                })
            })
            .collect();
        json!({
            "writes": summary.writes,
            "retained": summary.retained,
            "independent_retention": summary.independent_retention,
            "return_sources": return_sources,
            "return_allocations": summary.return_allocations,
            "effects": effects,
            "effect_uses": summary.effect_uses,
            "invocations": invocations,
            "invoked": summary.invoked,
            "callback_returns": summary.callback_returns,
            "storage_updates": storage_updates,
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
    let domain_wire = |rows: &[Instance]| {
        rows.iter()
            .map(|row| json!({"modes": row.modes, "summary": wire(&row.summary)}))
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
        .map(|(baseline, revision)| Instance::domain_subsumes(baseline, revision))
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
        include_str!("../../../tests/07_access/access.ril"),
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
fn task_join_examples_agree_with_lean() {
    let Some(oracle) = std::env::var_os("RIL_HORN_ORACLE") else {
        return;
    };
    let compile = parse_suite(
        Path::new("isolation.ril"),
        include_str!("../../../tests/12_concurrency_isolation/isolation.ril"),
    )
    .unwrap();
    let runtime = parse_suite(
        Path::new("fifo.ril"),
        include_str!("../../../tests/13_concurrency_deterministic/fifo.ril"),
    )
    .unwrap();
    let output = query(&oracle, "task-joins", b"[]").unwrap();
    let results: Vec<(String, bool)> = serde_json::from_slice(&output).unwrap();
    assert_eq!(results.len(), 6);
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
        include_str!("../../../tests/11_runtime_effects_panic/effects.ril"),
    )
    .unwrap();
    let output = query(&oracle, "draft", b"[]").unwrap();
    let results: Vec<(String, bool)> = serde_json::from_slice(&output).unwrap();
    assert_eq!(results.len(), 2);
    let temporary = tempfile::tempdir().unwrap();
    for (name, valid) in results {
        let case = runtime.cases.iter().find(|case| case.id == name).unwrap();
        let executable = temporary.path().join(&name);
        Driver.build_aot(&case.pkg, &executable).unwrap();
        let execution = run_worker(&mut Command::new(executable)).unwrap();
        assert_eq!(
            execution.status.success(),
            valid,
            "{name}: {:?}",
            String::from_utf8_lossy(&execution.stderr)
        );
    }
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
    check_access_examples("boundary", 6)
}

#[test]
fn call_authority_examples_agree_with_lean() -> Result<(), Box<dyn std::error::Error>> {
    check_access_examples("call-authority", 36)
}

#[test]
fn published_call_obligations_agree_with_lean() -> Result<(), Box<dyn std::error::Error>> {
    let Some(oracle) = std::env::var_os("RIL_HORN_ORACLE") else {
        return Ok(());
    };
    let suite = parse_suite(
        Path::new("access.ril"),
        include_str!("../../../tests/07_access/access.ril"),
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
    check_access_examples("graph", 18)
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
    check_access_examples("summary-signatures", 20)
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
