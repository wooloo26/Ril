use ril_compiler::{CheckOptions, CompilationOutcome, ProjectSource, Session};

fn session(case: &str, target: &str) -> Session {
    let case = ril_test::case_by_id(&format!(
        "tests/regressions/testing-declarations.ril::{case}"
    ));
    Session::with_project(
        case.root.clone().into(),
        case.files
            .iter()
            .map(|file| ProjectSource {
                path: file.name.clone().into(),
                bytes: file.bytes.clone(),
            })
            .collect(),
        CheckOptions {
            target: target.into(),
            ..Default::default()
        },
    )
    .unwrap()
}

#[test]
fn testing_helpers_use_the_checked_library_bodies() {
    for target in ["pointer32", "pointer64"] {
        for case in ["helpers-native", "unused-conditional-equality"] {
            let program = session(case, target)
                .verify()
                .unwrap_or_else(|outcome| panic!("{case}/{target}: {outcome:?}"));
            ril_compiler::lower::lower_core(&program)
                .unwrap_or_else(|error| panic!("{case}/{target}: {error:?}"));
        }
    }
}

#[test]
fn testing_helpers_preserve_the_language_rules_at_actual_calls() {
    for target in ["pointer32", "pointer64"] {
        for (case, code) in [
            ("reject-callable", "E0327"),
            ("reject-nested-callable", "E0327"),
            ("reject-forwarded-callable", "E0327"),
            ("reject-higher-order-callable", "E0327"),
            ("reject-recursive-callable", "E0327"),
            ("reject-nested-resource", "E0327"),
            ("reject-generic-value-test-callable", "E0327"),
            ("reject-mismatched-types", "E0301"),
            ("reject-mismatched-dimensions", "E0301"),
            ("reject-uninspected-result", "E0720"),
            ("reject-mutable-argument", "E0405"),
            ("reject-static-helper", "E0810"),
        ] {
            let outcome = session(case, target).check();
            assert!(
                matches!(&outcome, CompilationOutcome::Rejected { diagnostics }
                    if diagnostics.iter().any(|diagnostic| diagnostic.code == code)),
                "{case}/{target}: {outcome:?}"
            );
        }
    }
}
