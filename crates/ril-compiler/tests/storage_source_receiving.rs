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
    reject(include_str!("fixtures/storage_receiving_variable.ril"));
}

#[test]
fn mutable_record_member_replacement_preserves_the_declared_inner_dimension() {
    reject(include_str!("fixtures/storage_receiving_field.ril"));
}

#[test]
fn array_element_replacement_preserves_the_declared_inner_dimension() {
    reject(include_str!("fixtures/storage_receiving_element.ril"));
}

#[test]
fn storage_primitives_preserve_the_declared_element_source_schema() {
    reject(include_str!("fixtures/storage_receiving_push.ril"));
}

#[test]
fn matching_storage_replacements_keep_their_existing_permissions_and_shapes() {
    for source in [
        "fn example(){var target:[0][2]int=[];let old:[0][2]int=[];target=old}",
        "type Box={mut item:[0][2]int}\nfn example(){let mut holder=Box.{item:[]};let old:[0][2]int=[];holder.item=old}",
        "fn example(){let mut values:[1][0][2]int=[[]];let old:[0][2]int=[];values[0]=old}",
        "fn example(){let mut values:[][0][2]int=[];let old:[0][2]int=[];Array::push(mut values,old)}",
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
