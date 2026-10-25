//! Real native `.d.ril` bindings through an isolated typed provider process.
use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
};

const PROVIDER: &str = r###"
use ril_runtime_api::foreign::*;
use std::io::{Read,Write};
fn send(value:ProviderMessage){let bytes=serde_json::to_vec(&value).unwrap();let mut out=std::io::stdout().lock();out.write_all(&(bytes.len() as u64).to_le_bytes()).unwrap();out.write_all(&bytes).unwrap();out.flush().unwrap();}
fn receive()->ClientMessage{let mut input=std::io::stdin().lock();let mut header=[0;8];input.read_exact(&mut header).unwrap();let mut bytes=vec![0;u64::from_le_bytes(header) as usize];input.read_exact(&mut bytes).unwrap();serde_json::from_slice(&bytes).unwrap()}
fn integer(value:i128)->Graph{Graph{nodes:vec![Node::Integer{decimal:value.to_string(),bits:64,signed:true}],roots:vec![0]}}
fn argument(values:&Graph,arguments:&[Argument],index:usize)->i128{let Argument::Value(id)=arguments[index] else{panic!("ordinary argument")};let Node::Integer{decimal,..}=&values.nodes[id as usize] else{panic!("integer argument")};decimal.parse().unwrap()}
fn main(){
 std::env::set_current_dir(std::env::current_exe().unwrap().parent().unwrap()).unwrap();
 send(ProviderMessage::Ready{version:PROTOCOL_VERSION});
 let ClientMessage::Invoke{version,call,entry,export,static_arguments,signature,values,arguments,..}=receive() else{panic!("invoke")};assert_eq!(version,PROTOCOL_VERSION);
 let result=match export.as_str(){
  "VALUE"=>{assert_eq!(entry,EntryKind::Constant);assert!(arguments.is_empty());integer(41)},
  "add"=>integer(argument(&values,&arguments,0)+argument(&values,&arguments,1)),
  "echo"=>{let Argument::Value(root)=arguments[0] else{panic!("echo")};Graph{nodes:values.nodes,roots:vec![root]}},
  "last"=>{let Argument::Value(root)=arguments[arguments.len()-1] else{panic!("last")};Graph{nodes:values.nodes,roots:vec![root]}},
  "length"=>{let Argument::Value(root)=arguments[0] else{panic!("length")};let Node::Array(items)=&values.nodes[root as usize] else{panic!("array")};integer(items.len() as i128)},
  "nullary"|"nullary_twice"=>{let Argument::Callback(token)=arguments[0] else{panic!("callback")};let mut result=integer(0);for request in 1..=if export=="nullary_twice"{2}else{1}{send(ProviderMessage::Callback{call,request,token,arguments:Graph{nodes:vec![],roots:vec![]}});let ClientMessage::CallbackReturn{call:returned,request:answered,values}=receive() else{panic!("callback answer")};assert_eq!((returned,answered),(call,request));if request>1{assert_eq!(values,result);}result=values;}result},
  "zero"=>{assert!(arguments.is_empty());let [StaticArgument{name,value:StaticArgumentValue::Type{identity,schema:Some(ty)}}]=static_arguments.as_slice() else{panic!("concrete type argument")};assert_eq!(name,"T");assert!(!identity.is_empty());assert_eq!(*ty,signature.result);match signature.arena[*ty as usize]{TypeNode::Integer{bits:64,signed:true}=>integer(0),TypeNode::String=>Graph{nodes:vec![Node::String(String::new())],roots:vec![0]},_=>panic!("zero shape")}},
  "number"=>{let [StaticArgument{name,value:StaticArgumentValue::Value{identity,value:StaticValue::Integer{decimal,bits,signed}}}]=static_arguments.as_slice() else{panic!("concrete value argument")};assert_eq!(name,"n");assert!(!identity.is_empty());Graph{nodes:vec![Node::Integer{decimal:decimal.clone(),bits:*bits,signed:*signed}],roots:vec![0]}},
  "mark"=>{let [StaticArgument{name,value:StaticArgumentValue::Type{identity,schema:None}}]=static_arguments.as_slice() else{panic!("phantom non-exchange type")};assert_eq!(name,"T");assert!(!identity.is_empty());integer(77)},
  "shared"=>Graph{nodes:vec![Node::Tuple(vec![1,1]),Node::Array(vec![2]),Node::Integer{decimal:"1".into(),bits:64,signed:true}],roots:vec![0]},
  "business"=>Graph{nodes:vec![Node::Variant{tag:"Err".into(),fields:vec![1]},Node::String("business".into())],roots:vec![0]},
  "cycle"=>Graph{nodes:vec![Node::Record(vec![Field{name:"id".into(),node:1},Field{name:"link".into(),node:2}]),Node::Integer{decimal:"42".into(),bits:64,signed:true},Node::Variant{tag:"Some".into(),fields:vec![0]}],roots:vec![0]},
  "apply"=>{let Argument::Callback(token)=arguments[1] else{panic!("callback")};send(ProviderMessage::Callback{call,request:1,token,arguments:integer(argument(&values,&arguments,0))});let ClientMessage::CallbackReturn{call:returned,request,values}=receive() else{panic!("callback answer")};assert_eq!((returned,request),(call,1));values},
  "twice"|"three"=>{let Argument::Callback(token)=arguments[0] else{panic!("callback")};let mut value=integer(10);for request in 1..=if export=="twice"{2}else{3}{send(ProviderMessage::Callback{call,request,token,arguments:value});let ClientMessage::CallbackReturn{call:returned,request:answered,values}=receive() else{panic!("callback answer")};assert_eq!((returned,answered),(call,request));value=values;}value},
  "skip"=>integer(40),
  "replay"|"wrong_call"|"unknown_token"|"bad_callback_type"=>{let Argument::Callback(token)=arguments[1] else{panic!("callback")};if export=="replay"{send(ProviderMessage::Callback{call,request:1,token,arguments:integer(1)});let _=receive();}send(ProviderMessage::Callback{call:if export=="wrong_call"{call+1}else{call},request:1,token:if export=="unknown_token"{token+1000}else{token},arguments:if export=="bad_callback_type"{Graph{nodes:vec![Node::String("wrong".into())],roots:vec![0]}}else{integer(1)}});let _=receive();integer(0)},
  "panic"=>{send(ProviderMessage::Panic{call,message:"provider panic".into()});return;},
  "crash"=>std::process::abort(),
  "wait"=>loop{std::thread::sleep(std::time::Duration::from_secs(1));},
  "bad_graph"=>Graph{nodes:vec![Node::Array(vec![99])],roots:vec![0]},
  "wrong_type"=>Graph{nodes:vec![Node::String("wrong".into())],roots:vec![0]},
  _=>panic!("unknown export"),
 };
 send(ProviderMessage::Return{call,values:result});
}
"###;

fn library(dependencies: &Path, crate_name: &str) -> PathBuf {
    // Cargo's fingerprint graph identifies the exact dependency build. File
    // timestamps can mix feature/profile variants with incompatible serde traits.
    let fingerprints = dependencies.parent().unwrap().join(".fingerprint");
    let mut index = std::collections::BTreeMap::<(String, u64), Vec<PathBuf>>::new();
    let directories = fs::read_dir(&fingerprints)
        .unwrap()
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| path.is_dir())
        .collect::<Vec<_>>();
    for directory in &directories {
        for entry in fs::read_dir(directory).unwrap().filter_map(Result::ok) {
            let path = entry.path();
            let Some(name) = path
                .file_name()
                .and_then(|name| name.to_str())
                .and_then(|name| name.strip_prefix("lib-"))
            else {
                continue;
            };
            if name.contains('.') {
                continue;
            }
            let Ok(contents) = fs::read_to_string(&path) else {
                continue;
            };
            let Ok(value) = u64::from_str_radix(contents.trim(), 16) else {
                continue;
            };
            index
                .entry((name.to_owned(), value.swap_bytes()))
                .or_default()
                .push(path.with_extension("json"));
        }
    }
    let executable = std::env::current_exe().unwrap();
    let (_, hash) = executable
        .file_stem()
        .unwrap()
        .to_str()
        .unwrap()
        .rsplit_once('-')
        .unwrap();
    let mut roots = directories
        .iter()
        .filter(|path| {
            path.file_name()
                .unwrap()
                .to_string_lossy()
                .ends_with(&format!("-{hash}"))
        })
        .flat_map(|path| {
            fs::read_dir(path)
                .unwrap()
                .filter_map(Result::ok)
                .map(|entry| entry.path())
        })
        .filter(|path| {
            path.extension()
                .is_some_and(|extension| extension == "json")
        })
        .collect::<Vec<_>>();
    assert_eq!(
        roots.len(),
        1,
        "test dependency fingerprint is ambiguous: {roots:?}"
    );
    let mut seen = std::collections::BTreeSet::new();
    let mut found = std::collections::BTreeSet::new();
    while let Some(path) = roots.pop() {
        if !seen.insert(path.clone()) {
            continue;
        }
        let data: serde_json::Value = serde_json::from_slice(&fs::read(&path).unwrap()).unwrap();
        for dependency in data["deps"].as_array().unwrap() {
            let name = dependency[1].as_str().unwrap();
            let fingerprint = dependency[3].as_u64().unwrap();
            let Some(candidates) = index.get(&(name.to_owned(), fingerprint)) else {
                continue;
            };
            assert_eq!(
                candidates.len(),
                1,
                "dependency fingerprint is ambiguous: {name}"
            );
            let metadata = &candidates[0];
            if name == crate_name {
                let (_, artifact) = metadata
                    .parent()
                    .unwrap()
                    .file_name()
                    .unwrap()
                    .to_str()
                    .unwrap()
                    .rsplit_once('-')
                    .unwrap();
                let library = dependencies.join(format!("lib{crate_name}-{artifact}.rlib"));
                assert!(
                    library.is_file(),
                    "resolved dependency is missing: {}",
                    library.display()
                );
                found.insert(library);
            }
            roots.push(metadata.clone());
        }
    }
    assert_eq!(
        found.len(),
        1,
        "no unique resolved fixture dependency for {crate_name}: {found:?}"
    );
    found.pop_first().unwrap()
}

fn provider(directory: &Path) -> PathBuf {
    let source = directory.join("provider.rs");
    let executable = directory.join(if cfg!(windows) {
        "provider.exe"
    } else {
        "provider"
    });
    fs::write(&source, PROVIDER).unwrap();
    let current = std::env::current_exe().unwrap();
    let dependencies = current.parent().unwrap();
    let rustc = std::env::var_os("RUSTC")
        .or_else(|| {
            std::env::var_os("CARGO").and_then(|cargo| {
                let cargo = PathBuf::from(cargo);
                let rustc = cargo
                    .parent()?
                    .join(if cfg!(windows) { "rustc.exe" } else { "rustc" });
                rustc.is_file().then(|| rustc.into_os_string())
            })
        })
        .unwrap_or_else(|| "rustc".into());
    let output = Command::new(rustc)
        .args(["--edition=2024", "--crate-name=ril_external_fixture"])
        .arg("--extern")
        .arg(format!(
            "serde_json={}",
            library(dependencies, "serde_json").display()
        ))
        .arg("--extern")
        .arg(format!(
            "ril_runtime_api={}",
            library(dependencies, "ril_runtime_api").display()
        ))
        .arg("-L")
        .arg(format!("dependency={}", dependencies.display()))
        .arg(source)
        .arg("-o")
        .arg(&executable)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    executable
}

fn execute(
    directory: &Path,
    executable: &Path,
    declarations: &str,
    bindings: &[(&str, &str)],
    source: &str,
    expected: &str,
) {
    fs::write(directory.join("foreign.d.ril"), declarations).unwrap();
    let input = directory.join("root.ril");
    fs::write(&input, source).unwrap();
    let bindings: std::collections::BTreeMap<_, _> = bindings
        .iter()
        .map(|(name, export)| (format!("foreign::{name}"), *export))
        .collect();
    let manifest = directory.join("bindings.json");
    fs::write(&manifest, serde_json::to_vec(&serde_json::json!({"version":1,"providers":[{"id":"fixture","program":executable,"args":[],"bindings":bindings,"max_frame_bytes":1048576}]})).unwrap()).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_ril"))
        .arg("test")
        .arg(&input)
        .args(["--entry", "test_native", "--bindings"])
        .arg(manifest)
        .arg("--json")
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let report: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(report["status"], "executed", "{report}");
    assert_eq!(report["runtime"], expected, "{report}");
}

#[test]
fn external_defaults_labels_constants_and_ordinary_alias_graphs_execute_natively() {
    let directory = tempfile::tempdir().unwrap();
    let executable = provider(directory.path());
    execute(
        directory.path(),
        &executable,
        "pub fn add(left: int, right: int = 2) -> int\npub let VALUE: int\npub fn echo(data: bytes) -> bytes\npub fn shared() -> ([]int, []int)\npub fn business() -> Result<int, str>\npub fn defaults(items: []int = Array::map([1, 2], \\value -> value + 1)) -> []int",
        &[
            ("add", "add"),
            ("VALUE", "VALUE"),
            ("echo", "echo"),
            ("shared", "shared"),
            ("business", "business"),
            ("defaults", "echo"),
        ],
        r#"
use foreign
let FROM_CONSTANT = Foreign::VALUE + 1
pub fn test_native() &{FROM_CONSTANT} {
    assert(FROM_CONSTANT == 42)
    assert(Foreign::add(40) == 42)
    let add = Foreign::add
    assert(add(right: 3, left: 39) == 42)
    assert(Foreign::echo(b"a\x00\xFF") == b"a\x00\xFF")
    assert(Foreign::business() is Err("business"))
    assert(Foreign::defaults() == [2, 3])
    let mut copy = ^mut clone(Foreign::shared())
    copy.0 !> Array::push(2)
    assert(copy.1 == [1, 2])
}
"#,
        "returned-unit",
    );
    execute(
        directory.path(),
        &executable,
        "pub type Node = { mut id: int, link: ?Node }\npub fn cycle() -> Node",
        &[("cycle", "cycle")],
        r#"
use foreign
pub fn test_native() {
    let value = Foreign::cycle()
    assert(value.link?.id == Some(42))
    let mut copy = ^mut clone(value)
    copy.id = 7
    assert(copy.link?.id == Some(7))
    assert(value.id == 42)
}
"#,
        "returned-unit",
    );
    fs::write(
        directory.path().join("helper.ril"),
        "pub eff Read { get() -> int }\npub fn value() -> int @Read { Read::get() }",
    )
    .unwrap();
    execute(
        directory.path(),
        &executable,
        "use helper\npub fn compute(value: int = { with Helper::Read::get() -> resume 7; with Div::exhausted() -> 0; Div::budget(3, Helper::value) }) -> int\npub fn short(value: int = { with Helper::Read::get() -> resume 7; with Div::exhausted() -> 0; Div::budget(2, Helper::value) }) -> int",
        &[("compute", "echo"), ("short", "echo")],
        "use foreign\npub fn test_native(){assert(Foreign::compute()==7);assert(Foreign::short()==0)}",
        "returned-unit",
    );
}

#[test]
fn temporary_foreign_callbacks_stay_on_the_owner_effect_and_mutation_context() {
    let directory = tempfile::tempdir().unwrap();
    let executable = provider(directory.path());
    execute(
        directory.path(),
        &executable,
        "pub fn apply(value: int, callback: fn(int) -> int) -> int\npub fn twice(mut callback: fn(int) -> int) -> int",
        &[("apply", "apply"), ("twice", "twice")],
        r#"
use foreign
eff Offset { get() -> int }
type Counter = { mut value: int }
pub fn test_native() {
    let result = {
        with Offset::get() -> resume 2
        Foreign::apply(40, \number -> number + Offset::get())
    }
    assert(result == 42)
    let mut counter = Counter.{ value: 0 }
    let mut action = \number: int -> { counter.value += 1; number + counter.value }
    assert(Foreign::twice(mut action) == 13)
    assert(counter.value == 2)
}
"#,
        "returned-unit",
    );
    execute(
        directory.path(),
        &executable,
        "pub fn apply(value: int, callback: fn(int) -> int) -> int\npub fn add(left: int, right: int) -> int",
        &[("apply", "apply"), ("add", "add")],
        r#"
use foreign
eff Stop { now() -> int }
pub fn test_native() {
    let retained = [40, 2]
    let value = Foreign::apply(40, \number -> {
        for 0..1200 as index { let unused = [index, index + 1] }
        Foreign::add(number, retained[1])
    })
    assert(value == 42 && retained == [40, 2])
    let retained_answer = {
        with Stop::now() -> 7
        Foreign::apply(1, \number -> { Stop::now(); panic("abandoned callback resumed") }) + 100
    }
    assert(retained_answer == 107)
    assert(Foreign::add(40, 2) == 42)
}
"#,
        "returned-unit",
    );
}

#[test]
fn a_live_handler_abort_abandons_the_foreign_invocation() {
    let directory = tempfile::tempdir().unwrap();
    let executable = provider(directory.path());
    execute(
        directory.path(),
        &executable,
        "pub fn apply(value: int, callback: fn(int) -> int) -> int",
        &[("apply", "apply")],
        r#"
use foreign
eff Stop { now() -> int }
fn stop_callback(number: int) -> int @Stop { Stop::now(); panic("abandoned callback resumed") }
pub fn test_native() {
    let aborted = {
        with Stop::now() -> 7
        Foreign::apply(1, stop_callback) + 100
    }
    assert(aborted == 7)
}
"#,
        "returned-unit",
    );
}

#[test]
fn mixed_callback_returns_and_later_abort_preserve_zero_or_many_invocations() {
    let directory = tempfile::tempdir().unwrap();
    let executable = provider(directory.path());
    for body in [
        "if number >= 12 { Stop::now(); panic(\"abandoned callback resumed\") } else { number + 1 }",
        "if number < 12 { return number + 1 }; Stop::now(); panic(\"abandoned callback resumed\")",
        "match number { 12 -> { Stop::now(); panic(\"abandoned callback resumed\") }, _ -> number + 1 }",
    ] {
        execute(
            directory.path(),
            &executable,
            "pub fn repeated(callback: fn(int) -> int) -> int\npub fn skipped(callback: fn(int) -> int) -> int",
            &[("repeated", "three"), ("skipped", "skip")],
            &format!(
                r#"
use foreign
eff Stop {{ now() -> int }}
fn mixed(number: int) -> int @Stop {{ {body} }}
pub fn test_native() {{
    let absent = {{ with Stop::now() -> 7; Foreign::skipped(mixed) + 100 }}
    assert(absent == 140)
    let repeated = {{ with Stop::now() -> 7; Foreign::repeated(mixed) + 100 }}
    assert(repeated == 7)
}}
"#
            ),
            "returned-unit",
        );
    }
}

#[test]
fn foreign_process_faults_and_malformed_values_are_contained_language_panics() {
    let directory = tempfile::tempdir().unwrap();
    let executable = provider(directory.path());
    for export in ["panic", "crash", "bad_graph", "wrong_type"] {
        execute(
            directory.path(),
            &executable,
            "pub fn fail() -> int",
            &[("fail", export)],
            "use foreign\npub fn test_native(){let _ = Foreign::fail()}",
            "language-panic",
        );
    }
    for export in ["replay", "wrong_call", "unknown_token", "bad_callback_type"] {
        execute(
            directory.path(),
            &executable,
            "pub fn apply(value: int, callback: fn(int) -> int) -> int",
            &[("apply", export)],
            "use foreign\npub fn test_native(){let _ = Foreign::apply(1, \\number -> number + 1)}",
            "language-panic",
        );
    }
    execute(
        directory.path(),
        &executable,
        "pub fn apply(value: int, callback: fn(int) -> int) -> int @{} &{}",
        &[("apply", "apply")],
        r#"
use foreign
use ril/concurrent::{scope, TaskFault}
pub fn test_native() @Concurrent {
    let result = scope \mut s -> {
        let child = s.fork(\-> Foreign::apply(1, \number -> panic("callback panic")))
        child.join()
    }
    match result {
        Err(TaskFault::Panicked(info)) -> assert(info.message == "callback panic"),
        _ -> panic("callback fault was replaced"),
    }
}
"#,
        "returned-unit",
    );
}

#[test]
fn an_external_body_never_gains_budget_coverage_from_closed_effect_rows() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(
        directory.path().join("foreign.d.ril"),
        "pub fn value() -> int",
    )
    .unwrap();
    let input = directory.path().join("root.ril");
    fs::write(
        &input,
        "use foreign\nfn protected()->int{with Div::exhausted()->0;Div::budget(10,Foreign::value)}",
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_ril"))
        .arg("check")
        .arg(input)
        .arg("--json")
        .output()
        .unwrap();
    let report: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(report["status"], "rejected", "{report}");
    assert!(
        report["diagnostics"]
            .as_array()
            .unwrap()
            .iter()
            .any(|diagnostic| diagnostic["code"] == "E0822"),
        "{report}"
    );
}

#[test]
fn explicit_foreign_instances_transmit_phantom_static_arguments() {
    let directory = tempfile::tempdir().unwrap();
    let executable = provider(directory.path());
    execute(
        directory.path(),
        &executable,
        "pub fn zero<T>() -> T\npub fn number<n: int>() -> int\npub fn identity<T>(value: T) -> T\npub fn mark<T>() -> int",
        &[
            ("zero", "zero"),
            ("number", "number"),
            ("identity", "echo"),
            ("mark", "mark"),
        ],
        r#"
use foreign
type BytePair = [2]u8
type Callback = fn() -> int
type Integer = int
fn first() -> int { Foreign::zero<int>() }
fn second() -> str {
    assert(local() == 2)
    let increment = \number: int -> number + 1
    assert(increment(local()) == 3)
    Foreign::zero<str>()
    where fn local() -> int { 2 }
}

pub fn test_native() {
    assert(first() == 0 && second() == "")
    assert(Foreign::zero<int>() == 0)
    assert(Foreign::zero<Integer>() == 0)
    assert(Foreign::zero<int>() == 0)
    assert(Foreign::zero<str>() == "")
    assert(Foreign::number<7>() == 7)
    assert(Foreign::number<9>() == 9)
    assert(Foreign::number<3 + 4>() == 7)
    let copy = Foreign::identity<BytePair>
    assert(copy([1u8, 2u8]) == [1u8, 2u8])
    assert(Foreign::mark<Callback>() == 77)
}
"#,
        "returned-unit",
    );
}

#[test]
fn computed_foreign_instance_bases_run_once_before_written_operands() {
    let case = ril_test::case_by_id(
        "tests/regressions/callable-instances.ril::foreign-runtime-selection-pointer64",
    );
    let declaration = case
        .files
        .iter()
        .find(|file| file.name == "foreign.d.ril")
        .unwrap();
    let source = ril_test::case_source(
        "tests/regressions/callable-instances.ril::foreign-runtime-selection-pointer64",
    );
    let directory = tempfile::tempdir().unwrap();
    let executable = provider(directory.path());
    execute(
        directory.path(),
        &executable,
        std::str::from_utf8(&declaration.bytes).unwrap(),
        &[("identity", "echo"), ("zero", "zero"), ("number", "number")],
        source,
        "returned-unit",
    );
}

#[test]
fn generic_default_callable_instances_keep_their_own_native_bodies_and_captures() {
    let directory = tempfile::tempdir().unwrap();
    let executable = provider(directory.path());
    execute(
        directory.path(),
        &executable,
        r#"
pub fn number<n:int>(base:int=n,value:int=base+n)->int
pub fn shadow<n:int>(value:int={let n=n+1;n})->int
pub fn apply<n:int>(base:int=0,callback:fn(int)->int=\n->n+1)->int
pub fn fixed<n:int>(callback:fn()->int=\->n)->int
pub fn immediate<n:int>(value:int=(\->n)())->int
pub fn named<n:int>(value:int={read() where fn read()->int{n}})->int
pub fn captured<n:int>(base:int=n,value:int={read() where fn read()->int &{closure,base}{base}})->int
pub fn nested<n:int>(callback:fn()->int=\->{let inner=\->n;inner()})->int
pub fn nested_named<n:int>(value:int={outer() where fn outer()->int{inner() where fn inner()->int{n}}})->int
pub fn handled<n:int>(value:int={with Read::get()->resume n;Read::get() where eff Read{get()->int}})->int
pub fn budgeted<n:int>(value:int={with Div::exhausted()->0;Div::budget(1,\->n)})->int
pub fn budget_named<n:int>(value:int={with Div::exhausted()->0;Div::budget(1,read) where fn read()->int{n}})->int
pub fn empty<T>(items:[]T=[])->int
pub fn text<message:str>(value:str=message)->str
pub fn small<n:u8>(value:u8=n)->u8
"#,
        &[
            ("number", "last"),
            ("shadow", "echo"),
            ("apply", "apply"),
            ("fixed", "nullary"),
            ("immediate", "echo"),
            ("named", "echo"),
            ("captured", "last"),
            ("nested", "nullary"),
            ("nested_named", "echo"),
            ("handled", "echo"),
            ("budgeted", "echo"),
            ("budget_named", "echo"),
            ("empty", "length"),
            ("text", "echo"),
            ("small", "echo"),
        ],
        r#"
use foreign
fn one()->int{1}
pub fn test_native(){
    assert(Foreign::number<7>()==14 && Foreign::number<7>(10)==17 && Foreign::number<9>()==18)
    assert(Foreign::shadow<7>()==8)
    assert(Foreign::apply<99>()==1)
    assert(Foreign::fixed<7>()==7 && Foreign::fixed<9>()==9)
    assert(Foreign::immediate<7>()==7 && Foreign::immediate<9>()==9)
    assert(Foreign::named<7>()==7 && Foreign::named<9>()==9)
    assert(Foreign::captured<7>()==7 && Foreign::captured<9>(11)==11)
    assert(Foreign::nested<7>()==7 && Foreign::nested<9>()==9)
    assert(Foreign::nested_named<7>()==7 && Foreign::nested_named<9>()==9)
    assert(Foreign::handled<7>()==7 && Foreign::handled<9>()==9)
    assert(Foreign::budgeted<7>()==7 && Foreign::budgeted<9>()==9)
    assert(Foreign::budget_named<7>()==7 && Foreign::budget_named<9>()==9)
    assert(Foreign::empty<int>()==0 && Foreign::empty<str>()==0)
    assert(Foreign::text<"hello">()=="hello" && Foreign::text<"other">()=="other")
    assert(Foreign::small<7u8>()==7u8 && Foreign::small<9u8>()==9u8)
    with Div::exhausted()->panic("ordinary budget entry was corrupted")
    assert(Div::budget(1,one)==1)
}
"#,
        "returned-unit",
    );
}

#[test]
fn generic_defaults_retain_each_instances_handler_recipe_after_creation() {
    let directory = tempfile::tempdir().unwrap();
    let executable = provider(directory.path());
    fs::write(
        directory.path().join("helper.ril"),
        "pub eff Read { get() -> int }",
    )
    .unwrap();
    execute(
        directory.path(),
        &executable,
        r#"
use helper
pub type Reader = fn() -> int &closure
pub fn retained<n:int>(callback:Reader={with Helper::Read::get()->resume n;\->Helper::Read::get()})->int
pub fn shadowed<n:int>(callback:Reader={let value=n;with Helper::Read::get()->resume value;{let value=99;\->Helper::Read::get()}})->int
pub fn nested<n:int>(callback:Reader={with Helper::Read::get()->resume n;{with Helper::Read::get()->{let outer=Helper::Read::get();resume (outer+1)};\->Helper::Read::get()}})->int
pub fn named<n:int>(callback:Reader={with Helper::Read::get()->resume n;{reader where fn reader()->int{Helper::Read::get()}}})->int
pub fn measured<n:int>(callback:Reader={with Helper::Read::get()->resume n;let reader=\->Helper::Read::get();\->{with Div::exhausted()->-1;Div::budget(3,reader)}})->int
pub fn exhausted<n:int>(callback:Reader={with Helper::Read::get()->resume n;let reader=\->Helper::Read::get();\->{with Div::exhausted()->-1;Div::budget(2,reader)}})->int
"#,
        &[
            ("retained", "nullary_twice"),
            ("shadowed", "nullary_twice"),
            ("nested", "nullary_twice"),
            ("named", "nullary_twice"),
            ("measured", "nullary_twice"),
            ("exhausted", "nullary_twice"),
        ],
        r#"
use foreign
use helper
fn factory()->Foreign::Reader &capture{with Helper::Read::get()->resume 7;{reader where fn reader()->int{Helper::Read::get()}}}
fn other_factory()->Foreign::Reader &capture{with Helper::Read::get()->resume 9;{reader where fn reader()->int{Helper::Read::get()}}}
pub fn test_native(){
    let seven=factory()
    let again=factory()
    let nine=other_factory()
    with Helper::Read::get()->resume 100
    assert(seven()==7 && again()==7 && nine()==9 && seven()==7)
    assert(Foreign::retained<7>()==7 && Foreign::retained<9>()==9)
    assert(Foreign::retained<7>()==7)
    assert(Foreign::shadowed<7>()==7 && Foreign::shadowed<9>()==9)
    assert(Foreign::nested<7>()==8 && Foreign::nested<9>()==10)
    assert(Foreign::named<7>()==7 && Foreign::named<9>()==9)
    assert(Foreign::measured<7>()==7 && Foreign::measured<9>()==9)
    assert(Foreign::exhausted<7>() == -1 && Foreign::exhausted<9>() == -1)
    with Div::exhausted()->panic("named retained budget entry was corrupted")
    assert(Div::budget(3,seven)==7 && Div::budget(3,nine)==9)
}
"#,
        "returned-unit",
    );
}

#[test]
fn structured_cancellation_terminates_and_reaps_an_unresponsive_foreign_provider() {
    let directory = tempfile::tempdir().unwrap();
    let executable = provider(directory.path());
    execute(
        directory.path(),
        &executable,
        "pub fn wait() -> int @Fiber",
        &[("wait", "wait")],
        r#"
use foreign
use ril/concurrent::{scope, TaskFault}
use ril/time
pub fn test_native() @Async {
    let result = scope \mut s -> {
        s.fork(\-> { Time::sleep(Time::duration_nanos(50000000i64)); panic("stop provider") })
        let _ = Foreign::wait()
        Ok()
    }
    match result {
        Err(TaskFault::Panicked(info)) -> assert(info.message == "stop provider"),
        _ -> panic("foreign wait did not observe task cancellation"),
    }
}
"#,
        "returned-unit",
    );
}

#[test]
fn provider_callbacks_keep_transitive_host_continuations() {
    let directory = tempfile::tempdir().unwrap();
    let executable = provider(directory.path());
    execute(
        directory.path(),
        &executable,
        "pub fn invoke(action:fn()->int @Fiber)->int @Fiber",
        &[("invoke", "nullary_twice")],
        r#"
use foreign
use ril/time
fn leaf()->int @Fiber{Time::sleep(Time::duration_nanos(1000000i64));7}
fn middle()->int @Fiber{leaf()}
pub fn test_native() @Fiber{assert(Foreign::invoke(middle)==7)}
"#,
        "returned-unit",
    );
}
