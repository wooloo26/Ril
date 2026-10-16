use std::{
    fs,
    process::{Command, Stdio},
    thread,
    time::{Duration, Instant},
};

fn probe(source: &str, execute: bool) -> serde_json::Value {
    probe_at_entry(source, execute, "test_native")
}

fn probe_at_entry(source: &str, execute: bool, entry: &str) -> serde_json::Value {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("message.ril");
    fs::write(&path, source).unwrap();
    let mut command = Command::new(env!("CARGO_BIN_EXE_ril"));
    command
        .arg(if execute { "test" } else { "check" })
        .arg(path)
        .arg("--json");
    if execute {
        command.args(["--entry", entry]);
    }
    let mut child = command
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let deadline = Instant::now() + Duration::from_secs(20);
    loop {
        if child.try_wait().unwrap().is_some() {
            break;
        }
        if Instant::now() >= deadline {
            let _ = child.kill();
            let _ = child.wait();
            panic!("channel probe exceeded 20 seconds");
        }
        thread::sleep(Duration::from_millis(10));
    }
    let output = child.wait_with_output().unwrap();
    serde_json::from_slice(&output.stdout).unwrap_or_else(|error| {
        panic!(
            "{error}: {}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        )
    })
}

#[test]
fn actual_formal_inline_nested_captured_and_ordered_messages_execute() {
    for source in [
        ril_test::case_source("tests/regressions/channels.ril::channel-formal-result"),
        ril_test::case_source("tests/regressions/channels.ril::channel-message-inline-control"),
        ril_test::case_source("tests/regressions/channels.ril::channel-message-nested-formal"),
        ril_test::case_source("tests/regressions/channels.ril::channel-message-captured-formal"),
        ril_test::case_source("tests/regressions/channels.ril::channel-message-same-sender"),
        ril_test::case_source("tests/regressions/channels.ril::channel-message-fallback"),
        ril_test::case_source("tests/regressions/channels.ril::channel-message-question-checked"),
        ril_test::case_source(
            "tests/regressions/channels.ril::channel-message-conditional-returns",
        ),
        ril_test::case_source("tests/regressions/channels.ril::channel-message-finite-graphs"),
        ril_test::case_source(
            "tests/regressions/channels.ril::channel-message-formal-nested-checked",
        ),
        ril_test::case_source(
            "tests/regressions/channels.ril::channel-message-formal-two-branches-checked",
        ),
        ril_test::case_source("tests/regressions/channels.ril::channel-message-optional-scalar"),
        ril_test::case_source(
            "tests/regressions/channels.ril::channel-message-formal-optional-checked",
        ),
        ril_test::case_source(
            "tests/regressions/channels.ril::channel-message-formal-optional-clone-checked",
        ),
        ril_test::case_source(
            "tests/regressions/channels.ril::channel-message-formal-two-optionals-checked",
        ),
        ril_test::case_source(
            "tests/regressions/channels.ril::channel-message-optional-scalar-source-controls",
        ),
        ril_test::case_source(
            "tests/regressions/channels.ril::channel-message-optional-callback-source-controls",
        ),
    ] {
        let report = probe(source, true);
        assert_eq!(report["status"], "executed", "{report}");
        assert_eq!(report["runtime"], "returned-unit", "{report}");
        assert_eq!(report["exit"], 0, "{report}");
    }
    // Keep the three input routes in separate entry activations. Each run has
    // a fresh compiler process and native test directory, while the complete
    // shared source still passes verification before every entry executes.
    let callbacks = ril_test::case_source(
        "tests/regressions/channels.ril::channel-message-optional-callback-source-controls",
    );
    for entry in ["test_named_native", "test_single_map_native"] {
        let report = probe_at_entry(callbacks, true, entry);
        assert_eq!(report["status"], "executed", "{entry}: {report}");
        assert_eq!(report["runtime"], "returned-unit", "{entry}: {report}");
        assert_eq!(report["exit"], 0, "{entry}: {report}");
    }
}

#[test]
fn unpaid_messages_are_checked_without_executing_the_negative_sources() {
    for source in [
        ril_test::case_source(
            "tests/regressions/channels.ril::channel-message-formal-failed-send-loses-original",
        ),
        ril_test::case_source(
            "tests/regressions/channels.ril::channel-message-inline-closed-send-loses-original",
        ),
        ril_test::case_source("tests/regressions/channels.ril::channel-message-inline-outer-only"),
        ril_test::case_source(
            "tests/regressions/channels.ril::channel-message-inline-unread-close",
        ),
        ril_test::case_source(
            "tests/regressions/channels.ril::channel-message-formal-nested-graph-gap",
        ),
    ] {
        let report = probe(source, false);
        assert_eq!(report["status"], "rejected", "{report}");
        assert!(
            report["diagnostics"]
                .as_array()
                .unwrap()
                .iter()
                .any(|diagnostic| diagnostic["code"] == "E0720"),
            "{report}"
        );
    }
}

#[test]
fn representative_message_multiplicity_is_checked_without_execution() {
    for source in [
        ril_test::case_source(
            "tests/regressions/channels.ril::channel-message-repeated-cardinality-gap",
        ),
        ril_test::case_source(
            "tests/regressions/channels.ril::channel-message-loop-cardinality-gap",
        ),
    ] {
        let report = probe(source, false);
        assert_eq!(report["status"], "not-implemented", "{report}");
        assert!(report.to_string().contains("iteration-indexed"), "{report}");
    }
}

#[test]
fn optional_tag_tests_and_original_inspections_cannot_pay_a_cloned_result() {
    let ordinary = ril_test::case_source(
        "tests/regressions/channels.ril::channel-message-formal-optional-checked",
    )
    .replace("Some(inner)->assert(inner is Ok(_)|Err(_))", "Some(_)->()");
    let cloned = ril_test::case_source(
        "tests/regressions/channels.ril::channel-message-formal-optional-clone-checked",
    )
    .replace(
        "Some(inner)->assert(inner is Ok(_)|Err(_)),\n                None->()",
        "Some(_)->(),\n                None->()",
    );
    for source in [ordinary, cloned] {
        let report = probe(&source, false);
        assert_eq!(report["status"], "rejected", "{report}");
        assert!(
            report["diagnostics"]
                .as_array()
                .unwrap()
                .iter()
                .any(|diagnostic| diagnostic["code"] == "E0720"),
            "{report}"
        );
    }
}
