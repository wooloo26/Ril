#[path = "support/native_probe.rs"]
mod native_probe;

#[test]
fn scalar_const_values_execute_from_real_named_selections() {
    native_probe::executes(
        include_str!("../../ril-compiler/tests/fixtures/static_const_int.ril"),
        "scalar Meta int constants",
    );
}
