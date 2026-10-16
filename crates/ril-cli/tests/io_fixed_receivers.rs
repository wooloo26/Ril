use std::{fs, process::Command};

#[test]
fn declared_fixed_receiver_schemas_execute_with_the_existing_stream_callbacks() {
    for source in [
        ril_test::case_source("tests/regressions/io.ril::io-fixed-receiver"),
        ril_test::case_source("tests/regressions/io.ril::io-dynamic-receiver-control"),
        ril_test::case_source("tests/regressions/io.ril::io-nested-fixed-receiver"),
        ril_test::case_source("tests/regressions/io.ril::io-fixed-writer"),
        ril_test::case_source("tests/regressions/io.ril::io-dynamic-fixed-backing"),
        ril_test::case_source("tests/regressions/io.ril::io-readonly-capture"),
        ril_test::case_source("tests/regressions/io.ril::io-resource-fixed-receiver"),
    ] {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("io-fixed.ril");
        fs::write(&path, source).unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_ril"))
            .arg("test")
            .arg(path)
            .args(["--entry", "test_native", "--json"])
            .output()
            .unwrap();
        let report: serde_json::Value =
            serde_json::from_slice(&output.stdout).unwrap_or_else(|_| {
                panic!(
                    "{}\n{}",
                    String::from_utf8_lossy(&output.stdout),
                    String::from_utf8_lossy(&output.stderr)
                )
            });
        assert!(output.status.success(), "{source}: {report}");
        assert_eq!(report["status"], "executed", "{report}");
        assert_eq!(report["runtime"], "returned-unit", "{report}");
    }
}
