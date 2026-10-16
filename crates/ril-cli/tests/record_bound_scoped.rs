#[path = "support/native_probe.rs"]
mod native_probe;

#[test]
fn fixed_empty_inner_callable_mode_and_immutable_scoped_sources_execute() {
    for (name, source) in [
        (
            "scoped fixed",
            include_str!("../../ril-compiler/tests/fixtures/record_bounds/scoped_fixed.ril"),
        ),
        (
            "scoped empty inner dimension",
            include_str!(
                "../../ril-compiler/tests/fixtures/record_bounds/scoped_empty_inner_dimension.ril"
            ),
        ),
        (
            "scoped callable mode",
            include_str!("../../ril-compiler/tests/fixtures/record_bounds/scoped_callable_mut.ril"),
        ),
        (
            "scoped immutable field",
            include_str!(
                "../../ril-compiler/tests/fixtures/record_bounds/scoped_immutable_field.ril"
            ),
        ),
    ] {
        native_probe::executes(source, name);
    }
}
