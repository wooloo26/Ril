use std::{fs, process::Command};

#[test]
fn written_argument_and_container_order_preserves_independent_writers() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("evaluation-recency.ril");
    fs::write(&path,r#"
type Cell={mut value:int}
fn cell()->Cell{Cell.{value:0}}
fn independent()->Cell{Cell.{value:0}}
fn both(mut left:Cell,padding:int,mut right:Cell)&mut{left.value+=1;right.value+=2}
fn defaults(left:Cell,mut right:Cell,padding:int={let unused=cell();1})&mut{right.value+=left.value+padding}
pub fn test_native(){
    for [0,1] as index {
        let mut left=cell()
        let mut right=independent()
        both(mut left,{let unused=cell();1},mut right)
        assert(left.value==1 && right.value==2)
        left !> both({let unused=cell();1},mut right)
        let mut pair=^mut (^mut left,{let unused=cell();^mut right})
        both(mut pair.0,0,mut pair.1)
        let mut record=^mut .{left:^mut left,right:{let unused=cell();^mut right}}
        both(mut record.left,0,mut record.right)
        let mut array=^mut [^mut left,{let unused=cell();^mut right}]
        both(mut array[0],0,mut array[1])
        defaults(left,mut right)
        assert(left.value==5 && right.value==16)
    }
}
"#).unwrap();
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
