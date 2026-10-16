#[path = "support/native_probe.rs"]
mod native_probe;

#[test]
fn guaranteed_read_and_empty_write_inspections_execute() {
    for (label, original) in [
        (
            "read_all",
            include_str!("../../ril-compiler/tests/fixtures/io_callback_result_inspection.ril"),
        ),
        (
            "empty write_all",
            include_str!(
                "../../ril-compiler/tests/fixtures/io_callback_empty_write_inspection.ril"
            ),
        ),
    ] {
        let source = format!("{original}\npub fn test_native(){{example()}}");
        native_probe::executes(&source, label);
    }
}
