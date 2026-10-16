use std::{fs, process::Command};

fn executes(source: &str) {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("static_records.ril");
    fs::write(&path, source).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_ril"))
        .arg("test")
        .arg(path)
        .args(["--entry", "test_native", "--json"])
        .output()
        .unwrap();
    let report: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap_or_else(|_| {
        panic!(
            "{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        )
    });
    assert_eq!(report["status"], "executed", "{report}");
    assert_eq!(report["runtime"], "returned-unit", "{report}");
}

#[test]
fn static_record_modes_and_shared_children_survive_native_cloning() {
    executes(
        r#"
type Cell={mut count:int,label:str}
meta fn make()->Cell{Cell.{count:7,label:"source"}}
meta fn identity<T>(value:T)->T{value}
meta let CELL=identity(make())
meta let ROOT=(CELL,[CELL,CELL],["first":CELL],Some(CELL))
meta let SPREAD=.{..CELL}
meta let OVERRIDE=.{count:2,..CELL}
meta let REST={let .{label,..rest}=CELL;assert(label=="source");rest}
meta let TYPED:Cell=.{count:21,label:"typed"}
meta fn contextual()->Cell{let cell:Cell=.{count:31,label:"local"};cell}
meta let LOCAL=contextual()
meta fn choose(flag:bool)->Cell{if flag {.{count:41,label:"first"}}else{.{count:42,label:"second"}}}
meta let CHOSEN=choose(false)
pub fn test_native() &{CELL,ROOT,SPREAD,OVERRIDE,REST,TYPED,LOCAL,CHOSEN}{
    let mut copied= ^mut clone(ROOT)
    copied.0.count=9
    assert((copied.1)[0].count==9 && (copied.1)[1].count==9)
    assert(((copied.2)["first"] ?? panic("map")).count==9)
    assert((copied.3 ?? panic("option")).count==9)
    assert(CELL.count==7 && ROOT.0.count==7)
    let mut spread=clone(SPREAD)
    spread.count=10
    assert(spread.count==10 && spread.label=="source" && SPREAD.count==7)
    assert(OVERRIDE.count==2 && OVERRIDE.label=="source")
    let mut rest=clone(REST)
    rest.count=11
    assert(rest.count==11 && REST.count==7 && CELL.count==7)
    let mut typed=clone(TYPED)
    let mut local=clone(LOCAL)
    typed.count=22
    local.count=32
    assert(typed.count==22 && local.count==32 && TYPED.count==21 && LOCAL.count==31)
    let mut chosen=clone(CHOSEN)
    chosen.count=43
    assert(chosen.count==43 && CHOSEN.count==42 && chosen.label=="second")
}
"#,
    );
}

#[test]
fn fixed_array_element_writes_and_fresh_dynamic_shells_execute() {
    executes(
        r#"
fn replace(mut values:[2]int) &mut {values[0]=7}
pub fn test_native(){
    let mut values:[2]int=[1,2]
    replace(mut values)
    values[1]=8
    let mut reversed=Array::reverse(values)
    reversed !> Array::push(9)
    assert(values==[7,8] && reversed==[8,7,9])
    let mut combined=Array::concat(values,values)
    combined !> Array::truncate(1)
    assert(combined==[7])
}
"#,
    );
}
