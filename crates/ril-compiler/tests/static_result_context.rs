use ril_compiler::{CheckOptions, CompilationOutcome, Session};

fn session(source: &str, target: &str) -> Session {
    Session::with_options(
        source.as_bytes().to_vec(),
        CheckOptions {
            target: target.into(),
            ..Default::default()
        },
    )
}

#[test]
fn complete_result_contexts_select_missing_types_on_both_layouts_and_lower_to_core() {
    for target in ["pointer32", "pointer64"] {
        for source in [
            ril_test::case_source("tests/regressions/static.ril::positive"),
            ril_test::case_source("tests/regressions/static.ril::result-transfer"),
        ] {
            let verified = session(source, target).verify().unwrap();
            ril_compiler::lower::lower_core(&verified).unwrap();
        }
    }
}

#[test]
fn computed_alias_annotations_keep_their_frozen_full_source_and_original_root() {
    let source = ril_test::case_source("tests/regressions/static.ril::computed-alias");
    for target in ["pointer32", "pointer64"] {
        let verified = session(source, target).verify().unwrap();
        ril_compiler::lower::lower_core(&verified).unwrap();
    }
}

#[test]
fn result_contexts_do_not_replace_dynamic_inputs_explicit_types_or_return_shells() {
    for target in ["pointer32", "pointer64"] {
        for source in [
            ril_test::case_source("tests/regressions/static.ril::reject-dynamic-outer"),
            ril_test::case_source("tests/regressions/static.ril::reject-explicit-selection"),
            ril_test::case_source("tests/regressions/static.ril::reject-input-selection"),
        ] {
            let outcome = session(source, target).check();
            assert!(
                matches!(&outcome, CompilationOutcome::Rejected { diagnostics } if diagnostics.iter().any(|d| d.code == "E0301")),
                "{source}\n{outcome:?}"
            );
        }
    }
}

#[test]
fn receiving_views_still_erase_defaults_and_unsupported_callable_modes_stay_unproved() {
    let outcome = session(
        ril_test::case_source("tests/regressions/static.ril::reject-view-default"),
        "pointer64",
    )
    .check();
    assert!(
        matches!(&outcome, CompilationOutcome::Rejected { diagnostics } if diagnostics.iter().any(|d| d.code == "E0314")),
        "{outcome:?}"
    );
    let boundary = session(
        ril_test::case_source("tests/regressions/static.ril::reject-callable-mode"),
        "pointer64",
    )
    .check();
    assert!(
        matches!(boundary, CompilationOutcome::NotImplemented { .. }),
        "{boundary:?}"
    );
}

#[test]
fn result_contexts_do_not_inspect_returned_results_or_discharge_universal_some_paths() {
    for target in ["pointer32", "pointer64"] {
        for source in [
            ril_test::case_source("tests/regressions/static.ril::reject-result-inspection"),
            ril_test::case_source("tests/regressions/static.ril::reject-universal-some"),
        ] {
            let outcome = session(source, target).check();
            assert!(
                matches!(&outcome, CompilationOutcome::Rejected { diagnostics } if diagnostics.iter().any(|d| d.code == "E0720")),
                "{source}\n{outcome:?}"
            );
        }
    }
}
