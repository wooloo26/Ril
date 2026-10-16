use std::{fs, process::Command};

fn execute(source: &str) {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("answers.ril");
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
fn original_non_tail_reference_answer_executes() {
    execute(include_str!(
        "../../ril-compiler/tests/fixtures/non_tail_reference_answer.ril"
    ));
}

#[test]
fn ordinary_suffixes_keep_aliases_fresh_graphs_and_allocation_recency() {
    execute(
        r#"
eff Read{get()->int}
fn graph()->{left:[]int,right:[]int}{with Read::get()->{let answer=resume 7;let alias=answer;assert(alias.left[0]==7);alias};let shared=[Read::get()];.{left:shared,right:shared}}
fn data(number:int)->[]int{[number]}
fn answer()->[]int{with Read::get()->{let answer=resume 7;let other=data(99);assert(other[0]==99&&answer[0]==7);clone(answer)};data(Read::get())}
fn edited()->[]int{with Read::get()->{let mut answer=resume 7;answer[0]+=1;answer};[Read::get()]}
pub fn test_native(){
    let original=graph()
    let mut copied=^mut clone(original)
    copied.left[0]=9
    assert(copied.right[0]==9&&original.left[0]==7)
    assert(edited()==[8])
    for [0,1] as index{assert(answer()==[7])}
}
"#,
    );
}

#[test]
fn retained_reference_suffixes_execute_in_each_fresh_invocation() {
    execute(
        r#"
eff Read{get()->int}
type Reader=fn()->[]int &closure
fn make_reader()->Reader &capture{var reader:Reader=\->[0];{with Read::get()->{let answer=resume 7;assert(answer[0]>=0);clone(answer)};reader=\->[Read::get()];[0]};reader}
pub fn test_native(){let reader=make_reader();let first=reader();let second=reader();assert(first==[7]&&second==[7])}
"#,
    );
}

#[test]
fn operation_loans_end_while_outer_and_retained_paths_keep_their_authority() {
    execute(
        r#"
type Cell={mut count:int}
eff Edit{apply(mut Cell)->() &mut}
eff Retain{apply(^mut Cell)->() &^mut}
fn edited(mut cell:Cell)->[]int &mut{with Edit::apply(mut target)->{target.count+=1;let saved=target.count;let answer=resume();assert(answer[0]==saved+1);clone(answer)};Edit::apply(mut cell);cell.count+=1;[cell.count]}
fn retained(^mut cell:Cell)->[]int &mut{with Retain::apply(^mut target)->{target.count+=1;let answer=resume();target.count+=1;clone(answer)};Retain::apply(^mut cell);[cell.count]}
pub fn test_native(){
    let mut cell=Cell.{count:0}
    assert(edited(mut cell)==[2])
    cell.count+=10
    assert(cell.count==12)
    assert(retained(^mut cell)==[13])
    assert(cell.count==14)
}
"#,
    );
}

#[test]
fn private_body_writers_end_before_receiving_the_continuation_answer() {
    execute(&format!(
        "{}\npub fn test_native(){{assert(answer()==[8])}}",
        include_str!("../../ril-compiler/tests/fixtures/non_tail_private_local_answer.ril")
    ));
    execute(
        r#"
eff Read{get()->int}
type Action=fn()->() &mut &closure
type Holder={mut action:Action}
fn idle(){}
fn make(^mut values:[]int)->Action &capture &^mut{\->{values[0]+=1}}
pub fn test_native(){
    let mut holder=Holder.{action:idle}
    let result={with Read::get()->{var answer=resume 7;answer=answer;clone(answer)};let mut values=[Read::get()];holder.action=make(^mut values);values[0]+=1;values}
    holder.action()
    assert(result==[8])
}
"#,
    );
    execute(
        r#"
type Cell={mut value:int}
type Graph={mut count:int,child:Cell}
eff Read{get()->int}
fn answer(child:Immut<Cell>)->Graph{with Read::get()->{let answer=resume 7;assert(answer.count==8&&answer.child.value==3);clone(answer)};let mut graph=Graph.{count:Read::get(),child:child};graph.count+=1;graph}
pub fn test_native(){let child=Cell.{value:3};let result=answer(child);assert(result.count==8&&result.child.value==3&&child.value==3)}
"#,
    );
}
