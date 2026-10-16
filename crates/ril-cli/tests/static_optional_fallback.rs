#[path = "support/native_probe.rs"]
mod native_probe;

#[test]
fn reached_fallback_and_original_result_transport_execute() {
    native_probe::executes(
        include_str!("../../ril-compiler/tests/fixtures/static_optional_result_fallback.ril"),
        "optional fallback retains original and reached Result producers",
    );
}
