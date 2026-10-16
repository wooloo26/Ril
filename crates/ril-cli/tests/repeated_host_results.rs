//! Repetition retains escaped lexical cells and checks fresh host Results.
use std::{fs, process::Command};

fn execute(source: &str) {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("repeated.ril");
    fs::write(&path, source).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_ril"))
        .arg("test")
        .arg(path)
        .args(["--entry", "test_native", "--json"])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let report: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(report["runtime"], "returned-unit", "{report}");
    assert_eq!(report["exit"], 0, "{report}");
}

#[test]
fn original_host_result_callback_executes_unchanged() {
    execute(ril_test::case_source(
        "tests/regressions/results.ril::repeated-host-results",
    ));
}

#[test]
fn completed_factory_formals_and_local_scalar_cells_survive_repetition() {
    execute(
        r#"
type Action=fn(int)->int &closure
type MutAction=fn(int)->int &mut &closure
fn make(base:int)->Action &capture{\number->base+number}
fn make_named(base:int)->Action &capture{action where fn action(number:int)->int &{closure,base}{base+number}}
fn make_counter(base:int)->MutAction &capture{var count=base;count+=0;\number->{count+=number;count}}
pub fn test_native(){
    let action=make(3)
    assert(Array::map([1,2],action)==[4,5])
    let named=make_named(5)
    assert(Array::map([1,2],named)==[6,7])
    let mut counter=make_counter(0)
    assert(Array::map([1,2],mut counter)==[1,3])
    assert(counter(4)==7)
}
"#,
    );
}

#[test]
fn retained_handler_and_cleanup_captures_survive_their_factory() {
    execute(
        r#"
eff Read{get()->int}
type Reader=fn()->int &closure
type Guard={mut on_close:fn()->()}
type Action=fn(int)->int &mut &closure
fn make_reader()->Reader &capture{let base=3;with Read::get()->resume base;\->Read::get()}
fn make_counter(base:int)->Action &capture{var count=base;count+=0;\number->{count+=0;{let scoped mut guard=Guard.{on_close:\->{count+=1}}};count+number}}
pub fn test_native(){
    let reader=make_reader()
    let action=\number:int->reader()+number
    assert(Array::map([1,2],action)==[4,5])
    let mut counter=make_counter(0)
    assert(Array::map([1,2],mut counter)==[2,4])
    assert(counter(3)==6)
}
"#,
    );
}
