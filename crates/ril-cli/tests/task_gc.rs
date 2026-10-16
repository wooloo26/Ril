use std::{fs, process::Command};

#[test]
fn completed_task_graph_survives_collection_by_another_child() {
    let directory = tempfile::tempdir().unwrap();
    let source = directory.path().join("task_gc.ril");
    fs::write(
        &source,
        r#"
use ril/concurrent::{scope, TaskFault}
pub fn test_task_gc() @Concurrent {
    let result = scope \mut s -> {
        let first = s.fork(\-> [40,2])
        let churn = s.fork(\-> {
            for 0..3000 as index {
                let values = [index,index+1]
                assert(len(values)==2)
            }
        })
        churn.join()?
        let values = first.join()?
        assert(values==[40,2])
        Ok()
    }
    assert(result is Ok())
}
"#,
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_ril"))
        .arg("test")
        .arg(&source)
        .args(["--entry", "test_task_gc", "--json"])
        .output()
        .unwrap();
    let report: serde_json::Value =
        serde_json::from_slice(&output.stdout).unwrap_or_else(|error| {
            panic!(
                "{error}: {} {}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            )
        });
    assert!(output.status.success(), "{report}");
    assert_eq!(report["status"], "executed", "{report}");
    assert_eq!(report["runtime"], "returned-unit", "{report}");
}
