//! Compiler subprocesses ensure an interpreter stack failure is a real failure,
//! rather than an unwinding panic that a unit test could accidentally hide.
use std::{fs, process::Command};

fn check(source: &str) -> serde_json::Value {
    run("check", source)
}
fn run(command: &str, source: &str) -> serde_json::Value {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("static_tail.ril");
    fs::write(&path, source).unwrap();
    let mut compiler = Command::new(env!("CARGO_BIN_EXE_ril"));
    compiler.arg(command).arg(path).arg("--json");
    if command == "test" {
        compiler.args(["--entry", "test_native"]);
    }
    let output = compiler.output().unwrap();
    serde_json::from_slice(&output.stdout).unwrap_or_else(|_| {
        panic!(
            "compiler exit {:?}\n{}\n{}",
            output.status.code(),
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        )
    })
}

#[test]
fn finite_meta_tail_calls_do_not_consume_the_host_stack() {
    for source in [
        "meta fn count(n:int,total:int)->int{if n>0{count(n-1,total+1)}else{total}}\nmeta let _=assert(count(1024,0)==1024)",
        "meta fn even(n:int)->bool{if n==0{true}else{odd(n-1)}}\nmeta fn odd(n:int)->bool{if n==0{false}else{even(n-1)}}\nmeta let _=assert(even(1024) && odd(1023))",
        "meta fn relay(n:int,value:int)->int{if n>0{(\\step:int->relay(step,value))(n-1)}else{value}}\nmeta let _=assert(relay(512,7)==7)",
        "meta fn count(n:int,total:int)->int{if n>0{return count(n-1,total+1)};total}\nmeta let _=assert(count(1024,0)==1024)",
        "meta fn count(n:int,total:int)->int{match n{0->total,_->count(n-1,total+1)}}\nmeta let _=assert(count(512,0)==512)",
        "meta fn make(n:int,value:int)->fn()->int{if n>0{make(n-1,value)}else{\\->value}}\nmeta let GET=make(512,23)\nmeta let _=assert(GET()==23)",
    ] {
        let report = check(source);
        assert_eq!(report["status"], "accepted", "{source}\n{report}");
    }
}

#[test]
fn tail_calls_keep_reference_identity_and_return_shape_contracts() {
    let report = run(
        "test",
        r#"
meta fn carry(n:int,value:([2]int,[2]int))->([2]int,[2]int){
    if n>0{carry(n-1,value)}else{value}
}

meta let ROOT={let child:[2]int=[1,2];carry(512,(child,child))}
pub fn test_native() &{ROOT}{
    let mut copied= ^mut clone(ROOT)
    copied.0[0]=9
    assert(copied.1[0]==9 && ROOT.0[0]==1)
}
"#,
    );
    assert_eq!(report["status"], "executed", "{report}");
    assert_eq!(report["runtime"], "returned-unit", "{report}");
}

#[test]
fn type_tail_results_reach_the_native_program() {
    let report = run(
        "test",
        r#"
meta fn prior(n:int)->int{n-1}
type Count=\n:int->if n==0{type<int>}else{Count<prior(n)>}
type Selected=Count<512>
meta let SIZE=byte_size(type<Selected>)
pub fn test_native() &{SIZE}{assert(SIZE==8)}
"#,
    );
    assert_eq!(report["status"], "executed", "{report}");
    assert_eq!(report["runtime"], "returned-unit", "{report}");
}

#[test]
fn infinite_tail_calls_exhaust_evaluation_instead_of_the_host_stack() {
    let report = check("meta fn spin(n:int)->int{spin(n+1)}\nmeta let NEVER=spin(0)");
    assert_eq!(report["status"], "rejected", "{report}");
    assert!(
        report["diagnostics"]
            .as_array()
            .unwrap()
            .iter()
            .any(|d| d["code"] == "E0811"),
        "{report}"
    );
}

#[test]
fn unsupported_deep_non_tail_computation_is_reported_without_aborting() {
    let report =
        check("meta fn count(n:int)->int{if n>0{1+count(n-1)}else{0}}\nmeta let VALUE=count(1024)");
    assert_eq!(report["status"], "not-implemented", "{report}");
    assert!(report.to_string().contains("stack"), "{report}");
}

#[test]
fn tail_and_direct_anonymous_calls_keep_type_and_family_rejections() {
    for (source, code) in [
        (
            "meta fn bad()->int{(\\value:str->value)(1)}\nmeta let VALUE=bad()",
            "E0301",
        ),
        (
            "fn ordinary()->int{1}\nmeta fn bad()->int{ordinary()}\nmeta let VALUE=bad()",
            "E0810",
        ),
        (
            "meta fn bad()->type<int>{(\\->type<int>)()}\nmeta let VALUE=bad()",
            "E0812",
        ),
    ] {
        let report = check(source);
        assert_eq!(report["status"], "rejected", "{source}: {report}");
        assert!(
            report["diagnostics"]
                .as_array()
                .unwrap()
                .iter()
                .any(|d| d["code"] == code),
            "{report}"
        );
    }
}
