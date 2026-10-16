use std::{fs, process::Command};

#[test]
fn generic_helpers_clone_sender_authority_for_the_same_channel_and_child_task() {
    let directory = tempfile::tempdir().unwrap();
    let source = directory.path().join("sender-helper.ril");
    fs::write(
        &source,
        include_str!("fixtures/resource_clone/private_helpers.ril"),
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_ril"))
        .arg("test")
        .arg(&source)
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
    assert_eq!(report["exit"], 0, "{report}");
}

#[test]
fn native_build_rejects_missing_effects_consumed_authority_and_wrapped_resources() {
    for (helper, body, code) in [
        (
            "fn duplicate<T>(value:T)->T{clone(value)}",
            "fn bad(tx:Channel::Sender<int>) @Fiber{let _=duplicate(tx)}",
            "E0612",
        ),
        (
            "fn duplicate<T>(value:T)->T @Fiber{clone(value)}",
            "fn bad(tx:Channel::Sender<int>) @Fiber{Channel::close(tx);let _=duplicate(tx)}",
            "E0603",
        ),
        (
            "fn duplicate<T>(value:T)->T @Fiber{clone(value)}",
            "fn bad(tx:Channel::Sender<int>) @Fiber{let _=duplicate(.{sender:tx})}",
            "E0530",
        ),
        (
            "fn duplicate<T>(value:T)->T @Fiber{clone(value)}",
            "fn bad(file:File::Handle,tx:Channel::Sender<int>) @Fiber{let own=duplicate(tx);Channel::close(own);let _=duplicate(file)}",
            "E0530",
        ),
    ] {
        let directory = tempfile::tempdir().unwrap();
        let source = directory.path().join("invalid-sender-helper.ril");
        fs::write(&source,format!("use ril/concurrent/channel\nuse ril/file\n{helper}\n{body}\npub fn test_native(){{}}" )).unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_ril"))
            .arg("test")
            .arg(&source)
            .args(["--entry", "test_native", "--json"])
            .output()
            .unwrap();
        let report: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(report["status"], "rejected", "{report}");
        assert!(
            report["diagnostics"]
                .as_array()
                .unwrap()
                .iter()
                .any(|item| item["code"] == code),
            "{report}"
        );
    }
}
