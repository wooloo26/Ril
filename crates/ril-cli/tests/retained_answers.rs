use std::{fs, process::Command};

fn execute(source_text: &str) {
    let directory = tempfile::tempdir().unwrap();
    let source = directory.path().join("retained.ril");
    fs::write(&source, source_text).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_ril"))
        .arg("test")
        .arg(&source)
        .args(["--entry", "test_retained", "--json"])
        .output()
        .unwrap();
    assert_eq!(
        output.status.code(),
        Some(0),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let result: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(result["runtime"], "returned-unit", "{result}");
}

#[test]
fn parametric_identity_suffix_executes_after_each_fresh_continuation() {
    execute(
        r#"eff Read{get()->int}
type Reader=fn()->int &closure
fn make_reader()->Reader &capture{with Read::get()->{let answer=resume 7;answer};\->Read::get()}
pub fn test_retained(){let reader=make_reader();with Read::get()->resume 99;assert(reader()==7&&reader()==7)}"#,
    );
}

#[test]
fn fixed_copy_suffix_and_abort_keep_the_creation_answer_constraint() {
    execute(
        r#"eff Read{get()->int}
type Reader=fn()->int &closure
fn make_suffix()->Reader &capture{var reader:Reader=\->0;{with Read::get()->{let answer=resume 7;answer+1};reader=\->Read::get();0};reader}
fn make_abort()->Reader &capture{var reader:Reader=\->0;{with Read::get()->7;reader=\->{Read::get();panic("aborted continuation executed")};0};reader}
pub fn test_retained(){let suffix=make_suffix();let abort=make_abort();with Read::get()->resume 99;assert(suffix()==8&&suffix()==8&&abort()==7&&abort()==7)}"#,
    );
}

#[test]
fn retained_suffix_runs_after_body_cleanup_and_before_arm_cleanup() {
    execute(
        r#"eff Read{get()->int}
type Guard={on_close:fn()->()}
var trace=0
type Reader=fn()->int &closure &{mut trace}
fn close_body() &{mut trace}{trace=trace*10+1}
fn close_arm() &{mut trace}{trace=trace*10+3}
fn make_reader()->Reader &capture{var reader:Reader=\->0;{with Read::get()->{let scoped arm=Guard.{on_close:close_arm};let answer=resume 7;trace=trace*10+2;answer};reader=\->{let scoped body=Guard.{on_close:close_body};Read::get()};0};reader}
pub fn test_retained() &{mut trace}{let reader=make_reader();assert(reader()==7&&trace==123)}"#,
    );
}

#[test]
fn retained_abort_cleans_its_new_arm_and_abandoned_body_once_per_call() {
    execute(
        r#"eff Read{get()->int}
type Guard={on_close:fn()->()}
var trace=0
type Reader=fn()->int &closure &{mut trace}
fn close_body() &{mut trace}{trace=trace*10+1}
fn close_arm() &{mut trace}{trace=trace*10+2}
fn make_reader()->Reader &capture{var reader:Reader=\->0;{with Read::get()->{let scoped arm=Guard.{on_close:close_arm};7};reader=\->{let scoped body=Guard.{on_close:close_body};Read::get();panic("aborted body continued")};0};reader}
pub fn test_retained() &{mut trace}{let reader=make_reader();assert(reader()==7&&trace==21);assert(reader()==7&&trace==2121)}"#,
    );
}

#[test]
fn identity_suffix_preserves_ordinary_graph_sharing_and_fresh_activations() {
    execute(
        r#"eff Read{get()->int}
type Graph={left:[]int,right:[]int}
type Reader=fn()->Graph &closure
fn make_reader()->Reader &capture{
    with Read::get()->{let answer=resume 7;answer}
    \->{let shared=[Read::get()];.{left:shared,right:shared}}
}
pub fn test_retained(){
    let reader=make_reader()
    with Read::get()->resume 99
    let value=reader()
    let mut copied=^mut clone(value)
    copied.left[0]=9
    assert(copied.right[0]==9&&value.left[0]==7)
    let again=reader()
    assert(again.left[0]==7&&again.right[0]==7)
}"#,
    );
}

#[test]
fn identity_suffix_forwards_result_duties_and_reference_payloads() {
    execute(
        r#"eff Read{get()->int}
type Reader=fn()->Result<[]int,str> &closure
fn make_reader()->Reader &capture{with Read::get()->{let answer=resume 7;answer};\->Ok([Read::get()])}
pub fn test_retained(){
    let reader=make_reader()
    for 0..3 as index{
        let result=reader()
        assert(result is Ok(_))
        let values=result ?? \message->panic(message)
        assert(values[0]==7)
    }
}"#,
    );
}

#[test]
fn identity_suffix_keeps_ended_operation_loans_separate_from_the_callers_authority() {
    execute(
        r#"type Cell={mut count:int}
eff Edit{apply(mut Cell)->() &mut}
type Reader=fn(mut Cell)->[]int &closure &mut
fn make_reader()->Reader &capture{with Edit::apply(mut item)->{item.count+=1;let answer=resume();answer};\mut cell:Cell->{Edit::apply(mut cell);[cell.count]}}
pub fn test_retained(){let reader=make_reader();let mut cell=Cell.{count:0};let answer=reader(mut cell);cell.count+=10;assert(answer[0]==1&&cell.count==11)}"#,
    );
}

#[test]
fn identity_result_payload_survives_body_and_arm_cleanup_collections() {
    execute(
        r#"eff Read{get()->int}
type Guard={on_close:fn()->()}
type Reader=fn()->Result<[]int,str> &closure
halt fn churn(){for 0..1200 as index{let unused=[index,index+1]}}
fn make_reader()->Reader &capture{
    with Read::get()->{let scoped arm=Guard.{on_close:churn};let answer=resume 7;answer}
    \->{let scoped body=Guard.{on_close:churn};Ok([Read::get()])}
}

pub fn test_retained(){
    let reader=make_reader()
    let first=reader() ?? \message->panic(message)
    let second=reader() ?? \message->panic(message)
    assert(first[0]==7&&second[0]==7)
}"#,
    );
}

#[test]
fn identity_suffix_preserves_both_result_tags_after_the_continuation() {
    execute(
        r#"eff Read{get()->int}
type Reader=fn(bool)->Result<[]int,str> &closure
fn make_reader()->Reader &capture{with Read::get()->{let answer=resume 7;answer};\success:bool->{let number=Read::get();if success{Ok([number])}else{Err("no")}}}
pub fn test_retained(){
    let reader=make_reader()
    for 0..4 as index{
        let result=reader(index%2==0)
        match result{
            Ok(values)->assert(values[0]==7&&index%2==0),
            Err(message)->assert(message=="no"&&index%2!=0),
        }
    }
}"#,
    );
}
