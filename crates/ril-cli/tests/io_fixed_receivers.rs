use std::{fs, process::Command};

#[test]
fn declared_fixed_receiver_schemas_execute_with_the_existing_stream_callbacks() {
    for source in [
        include_str!("../../ril-compiler/tests/fixtures/io_fixed_receiver.ril"),
        include_str!("../../ril-compiler/tests/fixtures/io_dynamic_receiver_control.ril"),
        include_str!("../../ril-compiler/tests/fixtures/io_nested_fixed_receiver.ril"),
        include_str!("../../ril-compiler/tests/fixtures/io_fixed_writer.ril"),
        include_str!("../../ril-compiler/tests/fixtures/io_dynamic_fixed_backing.ril"),
        include_str!("../../ril-compiler/tests/fixtures/io_readonly_capture.ril"),
        include_str!("../../ril-compiler/tests/fixtures/io_resource_fixed_receiver.ril"),
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
