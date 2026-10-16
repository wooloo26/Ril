//! Static application results must survive lowering and native constant loading.
use std::{fs, process::Command};

fn run(command: &str, source: &str, budget: u64) -> serde_json::Value {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("static_applications.ril");
    fs::write(&path, source).unwrap();
    let mut compiler = Command::new(env!("CARGO_BIN_EXE_ril"));
    compiler
        .arg(command)
        .arg(path)
        .args(["--json", "--static-budget", &budget.to_string()]);
    if command == "test" {
        compiler.args(["--entry", "test_native"]);
    }
    let output = compiler.output().unwrap();
    serde_json::from_slice(&output.stdout).unwrap_or_else(|_| {
        panic!(
            "{:?}\n{}\n{}",
            output.status,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        )
    })
}

fn executes(source: &str, budget: u64) {
    let report = run("test", source, budget);
    assert_eq!(report["status"], "executed", "{report}");
    assert_eq!(report["runtime"], "returned-unit", "{report}");
}

#[test]
fn labelled_defaults_and_destination_interfaces_emit_their_actual_values() {
    executes(
        r#"
meta fn pair(first:int=1,second:int=first)->int{first*10+second}
meta fn choose(value:int=7)->int{value}
meta fn observe()->(int,int,int,int){
    let renamed:fn(other:int)->int=choose
    let declared=choose
    (pair(second:9,3),pair(first:4),renamed(other:11),declared())
}
meta let VALUES=observe()
pub fn test_native() &{VALUES}{assert(VALUES==(39,44,11,7))}
"#,
        100,
    );
}

#[test]
fn default_helpers_retain_each_factory_environment() {
    executes(
        r#"
meta fn make(value:int)->fn()->int{
    read
    where
    meta fn read()->int{choose()}
    meta fn choose(selected:int=sibling())->int{selected}
    meta fn sibling()->int{value}
}
meta fn observe()->(int,int,int){
    let first=make(7)
    let second=make(9)
    (first(),second(),first())
}
meta let VALUES=observe()
pub fn test_native() &{VALUES}{assert(VALUES==(7,9,7))}
"#,
        100,
    );
}

#[test]
fn omitted_reference_defaults_reuse_the_original_constant_node() {
    executes(
        r#"
meta fn pair<T>(first:T,second:T=first)->(T,T){(first,second)}
meta let ROOT=pair([1,2])
pub fn test_native() &{ROOT}{
    let mut copied= ^mut clone(ROOT)
    copied.0[0]=9
    assert(copied.1[0]==9 && ROOT.0[0]==1)
}
"#,
        1,
    );
}

#[test]
fn default_return_skips_body_entry_and_nested_return_stays_local() {
    executes(
        r#"
meta fn take(value:int={return 7})->int{99}
meta fn caller()->int{take()+1}
meta let VALUE=caller()
pub fn test_native() &{VALUE}{assert(VALUE==8)}
"#,
        1,
    );
    executes(
        r#"
meta fn take(value:int=(\->{return 7})())->int{value+1}
meta let VALUE=take()
pub fn test_native() &{VALUE}{assert(VALUE==8)}
"#,
        2,
    );
}

#[test]
fn quota_and_explicit_value_order_keep_precise_static_failures() {
    for (source, budget, code) in [
        (
            "meta fn one()->int{1}\nmeta fn take(value:int=one())->int{value}\nmeta let VALUE=take()",
            1,
            "E0811",
        ),
        (
            "meta fn failed()->int{assert(false);0}\nmeta fn take(value:int=failed())->int{value}\nmeta let VALUE=take()",
            1,
            "E0830",
        ),
        (
            "meta fn failed()->int{assert(false);0}\nmeta fn divided()->int{1/0}\nmeta fn take(first:int,second:int)->int{first+second}\nmeta let VALUE=take(second:failed(),first:divided())",
            100,
            "E0830",
        ),
        (
            "meta fn choose(value:int=7)->int{value}\nmeta let CHOSEN:fn(other:int)->int=choose\nmeta let VALUE=CHOSEN()",
            100,
            "E0314",
        ),
    ] {
        let report = run("check", source, budget);
        assert_eq!(report["status"], "rejected", "{report}");
        assert!(
            report["diagnostics"]
                .as_array()
                .unwrap()
                .iter()
                .any(|diagnostic| diagnostic["code"] == code),
            "{report}"
        );
    }
}
