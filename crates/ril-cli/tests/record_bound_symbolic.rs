// The three positive sources passed Source/Core/native-IR before registration.
#[path = "support/native_probe.rs"]
mod native_probe;

#[test]
fn symbolic_array_empty_inner_and_callable_sources_execute() {
    for (source, name) in [
        (
            include_str!(
                "../../ril-compiler/tests/fixtures/record_bounds/scoped_symbolic_array.ril"
            ),
            "symbolic fixed array member",
        ),
        (
            include_str!(
                "../../ril-compiler/tests/fixtures/record_bounds/scoped_symbolic_empty.ril"
            ),
            "symbolic empty outer member retains inner dimension",
        ),
        (
            include_str!(
                "../../ril-compiler/tests/fixtures/record_bounds/scoped_symbolic_callable.ril"
            ),
            "symbolic callable parameter and return identity",
        ),
    ] {
        native_probe::executes(source, name);
    }
}
