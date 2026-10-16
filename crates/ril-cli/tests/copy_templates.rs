//! Conditional private copy templates execute only after concrete call proofs.
use std::{fs, process::Command};

#[test]
fn private_copy_templates_preserve_graph_aliases_and_distinct_result_producers() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("copy-templates.ril");
    fs::write(
        &path,
        r#"
type Node={mut value:int,mut following:?Node}
fn duplicate<T>(source:T)->T{clone(source)}
fn forward<T>(source:T)->T{duplicate(source)}
fn twice<T>(source:T)->T{clone(clone(source))}
fn pair<T>(source:T)->(T,T){(clone(source),clone(source))}
fn row<R>(source:{..R})->{..R}{clone(source)}
fn seven()->int{7}
pub fn test_native(){
    assert(duplicate(7)==7 && duplicate("text")=="text")
    let function=duplicate(seven)
    assert(function()==7)
    let mut original=Node.{value:1,following:None}
    original.following=Some(^mut original)
    let mut copied=^mut forward(original)
    copied.value=9
    assert(copied.following?.value==Some(9))
    assert(original.following?.value==Some(1))
    let mut two=pair([1,2])
    two.0[0]=8
    assert(two.1[0]==1)
    assert(twice([3,4])==[3,4])
    let source=.{answer:Ok(5)}
    assert(source.answer is Ok(_)|Err(_))
    let result=row(source)
    assert(result.answer is Ok(5))
}
"#,
    )
    .unwrap();
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
