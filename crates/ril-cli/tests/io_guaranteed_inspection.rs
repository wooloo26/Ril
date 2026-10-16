#[path = "support/native_probe.rs"]
mod native_probe;

#[test]
fn guaranteed_read_and_empty_write_inspections_execute() {
    for (label, original) in [
        (
            "read_all",
            ril_test::case_source("tests/regressions/io.ril::io-callback-result-inspection"),
        ),
        (
            "empty write_all",
            ril_test::case_source("tests/regressions/io.ril::io-callback-empty-write-inspection"),
        ),
    ] {
        let source = format!("{original}\npub fn test_native(){{example()}}");
        native_probe::executes(&source, label);
    }
}
