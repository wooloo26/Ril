use std::{fs, process::Command};

#[test]
fn complete_source_type_identity_executes_across_generic_and_retained_calls() {
    for source in [
        ril_test::case_source("tests/regressions/source-types.ril::forwarding"),
        ril_test::case_source("tests/regressions/source-types.ril::empty-nested"),
        ril_test::case_source("tests/regressions/source-types.ril::returned-callable"),
        ril_test::case_source("tests/regressions/source-types.ril::modes"),
        ril_test::case_source("tests/regressions/source-types.ril::dynamic-view"),
        ril_test::case_source("tests/regressions/source-types.ril::effect-instance"),
        ril_test::case_source("tests/regressions/source-types.ril::type-forwarding"),
        ril_test::case_source("tests/regressions/source-types.ril::carriers"),
        ril_test::case_source("tests/regressions/source-types.ril::interfaces"),
    ] {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("source-schema.ril");
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
