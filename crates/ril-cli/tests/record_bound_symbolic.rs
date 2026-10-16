// The three positive sources passed Source/Core/native-IR before registration.
#[path = "support/native_probe.rs"]
mod native_probe;

#[test]
fn symbolic_array_empty_inner_and_callable_sources_execute() {
    for (source, name) in [
        (
            ril_test::case_source("tests/regressions/record-bounds.ril::scoped-symbolic-array"),
            "symbolic fixed array member",
        ),
        (
            ril_test::case_source("tests/regressions/record-bounds.ril::scoped-symbolic-empty"),
            "symbolic empty outer member retains inner dimension",
        ),
        (
            ril_test::case_source("tests/regressions/record-bounds.ril::scoped-symbolic-callable"),
            "symbolic callable parameter and return identity",
        ),
    ] {
        native_probe::executes(source, name);
    }
}
