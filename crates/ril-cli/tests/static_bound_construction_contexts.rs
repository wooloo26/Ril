#[path = "support/native_probe.rs"]
mod native_probe;

#[test]
fn fresh_structural_numeric_and_slot_contexts_execute() {
    native_probe::executes(
        ril_test::case_source("tests/regressions/static.ril::static-bound-fresh-construction"),
        "fresh structural constructors",
    );
}
