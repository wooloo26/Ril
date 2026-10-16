//! A later abort in one handler group abandons the earlier resumed body.
use std::{fs, process::Command};

#[test]
fn a_later_handler_abort_marks_body_cleanup_before_the_saved_arm_answer() {
    let directory = tempfile::tempdir().unwrap();
    let input = directory.path().join("cleanup_boundary.ril");
    fs::write(
        &input,
        r#"
eff Tick { first() -> (), second() -> () }
type Guard = { on_close: fn() -> () }
fn body() @Tick {
    let scoped guard = Guard.{on_close: \-> panic("discarded body cleanup")}
    Tick::first()
    Tick::second()
}
pub fn test_native() {
    with {
        Tick::first() -> { let scoped arm = Guard.{on_close: \-> ()}; resume () },
        Tick::second() -> ()
    }
    body()
}
"#,
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_ril"))
        .arg("test")
        .arg(input)
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
    assert_eq!(report["status"], "executed", "{report}");
    assert_eq!(report["runtime"], "double-fault", "{report}");
    assert!(
        report["cause"]["primary"]["message"]
            .as_str()
            .is_some_and(|message| message.contains("aborted")),
        "{report}"
    );
    assert_eq!(
        report["cause"]["cleanup"]["message"], "discarded body cleanup",
        "{report}"
    );
}
