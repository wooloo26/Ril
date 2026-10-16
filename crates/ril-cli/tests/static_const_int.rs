#[path = "support/native_probe.rs"]
mod native_probe;

#[test]
fn scalar_const_values_execute_from_real_named_selections() {
    native_probe::executes(
        ril_test::case_source("tests/regressions/static.ril::static-const-int"),
        "scalar Meta int constants",
    );
}
