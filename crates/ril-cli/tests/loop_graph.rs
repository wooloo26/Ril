//! Native checks for the ordinary-data may-graph fixed point.
use std::{fs, process::Command};

fn executes(source: &str) {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("loop-graph.ril");
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
    let report: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(report["runtime"], "returned-unit", "{report}");
    assert_eq!(report["exit"], 0, "{report}");
}

#[test]
fn ordinary_loop_roots_and_nested_shared_data_keep_actual_identity() {
    executes(
        r#"
type Cell={mut count:int}
fn make(value:int)->[]int{[value]}
fn rebuild(values:[]int)->[]int{
    var state=[0]
    for values as value{state=if value>0{make(value)}else{make(0)}}
    state
}
pub fn test_native(){
    assert(rebuild([1,2,3])==[3])
    assert(rebuild([-1,0])==[0])
    let mut shared=Cell.{count:0}
    let mut aliases:[]Cell=[]
    for [1,2,3] as index{aliases !> Array::push(^mut shared)}
    shared.count=7
    assert(aliases[0].count==7 && aliases[1].count==7 && aliases[2].count==7)
    let seed=.{value:10}
    let mut nested:[][]{value:int}=[]
    for [1,2,3] as value{nested !> Array::push([seed,.{value:value}])}
    assert(nested[0][0].value==10 && nested[2][1].value==3)
}
"#,
    );
}

#[test]
fn repeated_cyclic_copies_keep_backedges_and_separate_runtime_instances() {
    executes(
        r#"
type Node={mut value:int,mut following:?Node}
pub fn test_native(){
    let mut original=Node.{value:0,following:None}
    original.following=Some(^mut original)
    let mut copies:[]Node=[]
    for [1,2,3] as value{
        let mut copy=^mut clone(original)
        copy.value=value
        copies !> Array::push(^mut copy)
    }
    let view first=copies[0].following ?? panic("backedge")
    let view last_copy=copies[2].following ?? panic("backedge")
    assert(first.value==1 && last_copy.value==3 && original.value==0)
    copies[0].value=9
    assert(first.value==9 && last_copy.value==3)
}
"#,
    );
}

#[test]
fn terminal_result_families_keep_both_propagated_and_successful_outcomes() {
    executes(
        r#"
fn read(flag:bool)->Result<int,str>{if flag{Ok(1)}else{Err("failed")}}
fn example(flag:bool)->Result<(),str>{
    loop{let number=read(flag)?;assert(number==1);if flag{last}}
    Ok()
}
pub fn test_native(){
    assert(example(true) is Ok())
    assert(example(false) is Err("failed"))
}
"#,
    );
}

#[test]
fn copies_of_previous_copies_keep_cycles_aliases_and_old_graph_isolation() {
    executes(
        r#"
type Node={mut value:int,mut following:?Node}
type Cell={mut count:int}
type Wrapper={child:Cell}
fn repeated_array(values:[]int)->[][]int{
    var current=[[1],[2]]
    for values as index{current=clone(current)}
    current
}
pub fn test_native(){
    assert(repeated_array([1,2,3,4])==[[1],[2]])
    let mut original=Node.{value:0,following:None}
    original.following=Some(^mut original)
    var mut current=^mut clone(original)
    for [1,2,3,4] as index{
        current=^mut clone(current)
        current.value+=index
        let view back=current.following ?? panic("lost cycle")
        assert(back.value==current.value)
    }
    assert(current.value==10 && original.value==0)
    let mut old=Cell.{count:0}
    let mut shells:[]Wrapper=[]
    for [1,2,3] as index{
        let mut shell=^mut Wrapper.{child:^mut old}
        shells !> Array::push(^mut shell)
    }
    let mut copied=^mut clone(shells)
    copied[0].child.count=7
    assert(copied[1].child.count==7 && copied[2].child.count==7)
    assert(old.count==0 && shells[0].child.count==0)
}
"#,
    );
}
