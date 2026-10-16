//! The frontend-independent control classification and managed-entry guard are
//! separate architecture layers, but must describe the same builtin ABI.
#[test]
fn native_step_classification_matches_the_managed_builtin_guard() {
    for name in ril_runtime_api::builtins::OPERATIONS {
        for candidate in [(*name).to_owned(), format!("Prelude::{name}")] {
            assert_eq!(
                ril_codegen::cps::native_step_builtin(&candidate),
                ril_runtime_api::builtins::requires_native_step(&candidate),
                "{candidate}"
            );
        }
    }
    for name in [
        "\0ril.foreign.invoke",
        "Channel::__bounded_0_10_20",
        "Channel::__bounded_0_bad_20",
        "String::join",
        "File::read_bytes_extra",
    ] {
        assert_eq!(
            ril_codegen::cps::native_step_builtin(name),
            ril_runtime_api::builtins::requires_native_step(name),
            "{name}"
        );
    }
}
