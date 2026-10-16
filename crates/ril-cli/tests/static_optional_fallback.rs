#[path = "support/native_probe.rs"]
mod native_probe;

#[test]
fn reached_fallback_and_original_result_transport_execute() {
    native_probe::executes(
        ril_test::case_source("tests/regressions/static.ril::static-optional-result-fallback"),
        "optional fallback retains original and reached Result producers",
    );
}
