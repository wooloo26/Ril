//! Source/Core prerequisite for activating the seven native receiving entries.
//! This test never executes Ril; the CLI adapter must verify actual results.
use ril_compiler::{CheckOptions, Session};

const SOURCE: &str = include_str!("fixtures/source_receiving_native.ril.pending");
const ENTRIES: [&str; 7] = [
    "test_fresh_fixed",
    "test_empty_composites",
    "test_callback",
    "test_return_branches",
    "test_ordinary",
    "test_default",
    "test_explicit_generic",
];

#[test]
fn complete_native_receiving_fixture_has_real_source_and_core_proofs() {
    for target in ["pointer32", "pointer64"] {
        let verified = Session::with_options(
            SOURCE.as_bytes().to_vec(),
            CheckOptions {
                target: target.into(),
                ..CheckOptions::default()
            },
        )
        .verify()
        .unwrap_or_else(|outcome| panic!("{target}: {outcome:?}"));
        let core = ril_compiler::lower::lower_core(&verified).unwrap();
        if target == "pointer64" {
            for entry in ENTRIES {
                ril_codegen::lower::lower_native_with_entry(&core, entry)
                    .unwrap_or_else(|error| panic!("{entry}: {error:?}"));
            }
        }
    }
}
