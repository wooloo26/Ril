use std::{fs, process::Command};

#[test]
fn complete_source_type_identity_executes_across_generic_and_retained_calls() {
    for source in [
        include_str!("../../ril-compiler/tests/fixtures/source_type_witness/forwarding.ril"),
        include_str!("../../ril-compiler/tests/fixtures/source_type_witness/empty_nested.ril"),
        include_str!("../../ril-compiler/tests/fixtures/source_type_witness/returned_callable.ril"),
        include_str!("../../ril-compiler/tests/fixtures/source_type_witness/modes.ril"),
        include_str!("../../ril-compiler/tests/fixtures/source_type_witness/dynamic_view.ril"),
        include_str!("../../ril-compiler/tests/fixtures/source_type_witness/effect_instance.ril"),
        include_str!("../../ril-compiler/tests/fixtures/source_type_witness/type_forwarding.ril"),
        include_str!("../../ril-compiler/tests/fixtures/source_type_witness/carriers.ril"),
        include_str!("../../ril-compiler/tests/fixtures/source_type_witness/interfaces.ril"),
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
