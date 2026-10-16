use std::{fs, process::Command};

fn execute(source: &str) -> serde_json::Value {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("numeric-pending.ril");
    fs::write(&path, source).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_ril"))
        .arg("test")
        .arg(&path)
        .args(["--entry", "test_native", "--json"])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    serde_json::from_slice(&output.stdout).unwrap()
}

const PREFIX: &str = r#"
type Counter={mut value:int}
type Guard={mut on_close:fn()->()}
fn choose<T>(left:T,right:T)->T{left}
fn peer<T>(value:T,mut counter:Counter)->T &mut{counter.value+=1;value}
"#;

#[test]
fn delayed_type_choice_keeps_early_integer_fault_before_later_argument_effects() {
    for (left, peer, message) in [
        ("1/0", "3int", "division by zero"),
        ("127+1", "3i8", "integer overflow"),
        ("-(-128)", "3i8", "integer overflow"),
    ] {
        for peer_first in [false, true] {
            let call = if peer_first {
                format!("choose(right:peer({peer},mut counter),left:{left})")
            } else {
                format!("choose({left},peer({peer},mut counter))")
            };
            let count = usize::from(peer_first);
            let source = format!(
                "{PREFIX}\npub fn test_native(){{let mut counter=Counter.{{value:0}};let scoped mut guard=Guard.{{on_close:\\->assert(counter.value=={count})}};let value={call};panic(\"arithmetic did not fault\")}}"
            );
            let report = execute(&source);
            assert_eq!(report["runtime"], "language-panic", "{left}: {report}");
            assert_eq!(report["message"], message, "{left}: {report}");
        }
    }
}

#[test]
fn delayed_floating_selection_preserves_rounding_and_runs_the_peer_once() {
    let source = [
        PREFIX,
        r#"
eff Read<T>{get(value:T)->T}
fn read<T>(left:T,right:T)->T @Read<T>{Read<T>::get(left)}
meta let STORED:f32=16777217
pub fn test_native() &{STORED}{
    let mut counter=Counter.{value:0}
    let divided=choose(1/0,peer(3.0f32,mut counter))
    assert("{divided}"=="inf" && counter.value==1)
    let rounded=choose(16777217+1,peer(3.0f32,mut counter))
    assert(rounded==16777216.0f32 && counter.value==2)
    let expected:f32=0X80000080000000000000000000000001
    let huge=choose(0X80000080000000000000000000000001,peer(3.0f32,mut counter))
    assert(huge==expected && counter.value==3)
    let committed=choose(STORED+1,peer(3.0f32,mut counter))
    assert(committed==rounded && counter.value==4)
    let arithmetic=(16777217+1)+peer(3.0f32,mut counter)
    assert(arithmetic==16777220.0f32 && counter.value==5)
    let values=[3.0f32]
    let projected=16777217+values[0]
    assert(projected==arithmetic)
    {
        with Read<int>::get(value)->panic("wrong integer instance")
        with Read<f32>::get(value)->resume value
        let answer=read(16777217+1,peer(3.0f32,mut counter))
        assert(answer==rounded && counter.value==6)
    }
}
"#,
    ]
    .concat();
    let report = execute(&source);
    assert_eq!(report["runtime"], "returned-unit", "{report}");
    assert_eq!(report["exit"], 0, "{report}");
}

#[test]
fn scope_body_numeric_fault_propagates_instead_of_returning_a_recovery_value() {
    let report = execute(
        r#"
use ril/concurrent::{scope}
type Counter={mut value:int}
type Guard={mut on_close:fn()->()}
fn choose<T>(left:T,right:T)->T{left}
fn inspect<T>(value:T,result:Result<int,str>,mut counter:Counter)->T &mut {
    counter.value+=1
    assert(result is Err(_))
    value
}
pub fn test_native() @Concurrent {
    let result:Result<int,str>=Err("uninspected")
    let mut counter=Counter.{value:0}
    let scoped mut guard=Guard.{on_close:\->assert(counter.value==0)}
    let outcome=scope \mut s->{s.fork(\->());Ok(choose(1/0,inspect(3int,result,mut counter)))}
    assert(outcome is Ok(_)|Err(_))
}
"#,
    );
    assert_eq!(report["runtime"], "language-panic", "{report}");
    assert_eq!(report["message"], "division by zero", "{report}");
}

#[test]
fn delayed_numeric_resolution_adds_no_budget_events() {
    let report = execute(
        r#"
fn identity<T>(value:T)->T{value}
fn choose<T>(left:T,right:T)->T{left}
fn pending(limit:int)->?f32 {
    with Div::exhausted()->None
    Div::budget(limit,\->Some(choose(16777217+1,identity(3.0f32))))
}

fn ready(limit:int)->?f32 {
    with Div::exhausted()->None
    Div::budget(limit,\->Some(choose(16777216.0f32+1.0f32,identity(3.0f32))))
}
pub fn test_native(){
    for [0,1,2,3,4,5,6,7,8,9,10,11,12] as limit {assert(pending(limit)==ready(limit))}
    assert(pending(0) is None)
    assert(pending(32)==Some(16777216.0f32))
}
"#,
    );
    assert_eq!(report["runtime"], "returned-unit", "{report}");
    assert_eq!(report["exit"], 0, "{report}");
}
