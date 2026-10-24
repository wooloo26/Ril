//! Original storage source schemas survive writes. These strict regressions
//! are intentionally active before the remaining storage correction is done.
use ril_compiler::{CheckOptions, CompilationOutcome, Session};

fn reject(source: &str) {
    for target in ["pointer32", "pointer64"] {
        let outcome = Session::with_options(
            source.as_bytes().to_vec(),
            CheckOptions {
                target: target.into(),
                ..Default::default()
            },
        )
        .check();
        assert!(
            matches!(&outcome, CompilationOutcome::Rejected { diagnostics }
                if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0301")),
            "{target}: {source}\n{outcome:?}"
        );
    }
}

#[test]
fn variable_replacement_preserves_the_original_inner_dimension() {
    reject(ril_test::case_source(
        "tests/regressions/source-receiving.ril::storage-receiving-variable",
    ));
}

#[test]
fn mutable_record_member_replacement_preserves_the_declared_inner_dimension() {
    reject(ril_test::case_source(
        "tests/regressions/source-receiving.ril::storage-receiving-field",
    ));
}

#[test]
fn array_element_replacement_preserves_the_declared_inner_dimension() {
    reject(ril_test::case_source(
        "tests/regressions/source-receiving.ril::storage-receiving-element",
    ));
}

#[test]
fn storage_primitives_preserve_the_declared_element_source_schema() {
    reject(ril_test::case_source(
        "tests/regressions/source-receiving.ril::storage-receiving-push",
    ));
}

#[test]
fn aliases_returned_by_functions_keep_their_declared_storage_dimensions() {
    reject(ril_test::case_source(
        "tests/regressions/source-receiving.ril::returned-alias-dimension-conflict",
    ));
    for target in ["pointer32", "pointer64"] {
        let verified = Session::with_options(
            ril_test::case_bytes(
                "tests/regressions/source-receiving.ril::returned-alias-matching-dimension",
            )
            .to_vec(),
            CheckOptions {
                target: target.into(),
                ..Default::default()
            },
        )
        .verify()
        .unwrap_or_else(|outcome| panic!("{target}: {outcome:?}"));
        ril_compiler::lower::lower_core(&verified).unwrap();
    }
}

#[test]
fn matching_storage_replacements_keep_their_existing_permissions_and_shapes() {
    for source in [
        ril_test::case_source(
            "tests/regressions/source-observations.ril::matching-variable-replacement",
        ),
        ril_test::case_source(
            "tests/regressions/source-observations.ril::matching-record-member-replacement",
        ),
        ril_test::case_source(
            "tests/regressions/source-observations.ril::matching-array-element-replacement",
        ),
        ril_test::case_source("tests/regressions/source-observations.ril::matching-array-push"),
    ] {
        for target in ["pointer32", "pointer64"] {
            let verified = Session::with_options(
                source.as_bytes().to_vec(),
                CheckOptions {
                    target: target.into(),
                    ..Default::default()
                },
            )
            .verify()
            .unwrap_or_else(|outcome| panic!("{target}: {source}\n{outcome:?}"));
            ril_compiler::lower::lower_core(&verified).unwrap();
        }
    }
}
