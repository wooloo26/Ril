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

#[test]
fn canonical_write_views_cannot_lose_their_graph_or_borrow_another_environment() {
    use ril_compiler::sema::validate::{ValidationIssueKind, solved_facts};
    let source = ril_test::case_bytes(
        "tests/regressions/source-observations.ril::matching-record-member-replacement",
    );
    for target in ["pointer32", "pointer64"] {
        let verified = Session::with_options(
            source.to_vec(),
            CheckOptions {
                target: target.into(),
                ..Default::default()
            },
        )
        .verify()
        .unwrap_or_else(|outcome| panic!("{target}: {outcome:?}"));
        let facts = verified.facts();
        let original = facts.storage_writes[0].expected.unwrap();
        let holder = facts
            .bindings
            .iter()
            .position(|binding| binding.name == "holder")
            .unwrap();
        let holder = facts.source_types.binding_view(holder).unwrap();
        let other = facts
            .bindings
            .iter()
            .position(|binding| binding.name == "old")
            .unwrap();
        let other = facts.source_types.binding_view(other).unwrap();
        assert_ne!(original.environment, other.environment);
        let core = ril_compiler::lower::lower_core(&verified).unwrap();
        let retained = core.provenance.storage_writes[0].expected.unwrap();
        assert!(matches!(
            core.provenance.source_types.nodes[retained.ty.0 as usize],
            ril_ir::provenance::SourceTypeNode::Array {
                length: ril_ir::provenance::SourceLength::Fixed(0),
                ..
            }
        ));
        for mutation in 0..3 {
            let mut changed = facts.clone();
            match mutation {
                0 => changed.storage_writes[0].expected = None,
                1 => changed.storage_writes[0].expected.as_mut().unwrap().ty = holder.ty,
                2 => {
                    changed.storage_writes[0]
                        .expected
                        .as_mut()
                        .unwrap()
                        .environment = other.environment
                }
                _ => unreachable!(),
            }
            let issues = solved_facts(&changed).unwrap_err();
            assert!(
                issues
                    .iter()
                    .any(|issue| matches!(issue.kind, ValidationIssueKind::StorageSource(_))),
                "{target}, mutation {mutation}: {issues:?}"
            );
        }
    }
}

#[test]
fn deleting_a_write_and_forging_a_never_rhs_cannot_erase_reception() {
    use ril_compiler::sema::{
        model::Ty,
        validate::{ValidationIssueKind, solved_facts},
    };
    for case in [
        "tests/regressions/source-observations.ril::matching-variable-replacement",
        "tests/regressions/source-observations.ril::matching-record-member-replacement",
        "tests/regressions/source-observations.ril::matching-array-element-replacement",
    ] {
        for target in ["pointer32", "pointer64"] {
            let verified = Session::with_options(
                ril_test::case_bytes(case).to_vec(),
                CheckOptions {
                    target: target.into(),
                    ..Default::default()
                },
            )
            .verify()
            .unwrap_or_else(|outcome| panic!("{case}, {target}: {outcome:?}"));
            let facts = verified.facts();
            solved_facts(facts).unwrap();
            let write = facts
                .storage_writes
                .first()
                .expect("fixture has an actual replacement");
            let rhs = write.rhs.expression;
            assert_ne!(facts.expressions[rhs].value.ty, Ty::Never);
            for forge_never in [false, true] {
                let mut changed = facts.clone();
                changed.storage_writes.remove(0);
                if forge_never {
                    changed.expressions[rhs].value.ty = Ty::Never;
                }
                let issues = solved_facts(&changed).unwrap_err();
                assert!(
                    issues
                        .iter()
                        .any(|issue| matches!(issue.kind, ValidationIssueKind::StorageSource(_))),
                    "{case}, {target}, forged Never={forge_never}: {issues:?}"
                );
            }
        }
    }
}

#[test]
fn forged_never_receivers_and_selectors_cannot_claim_an_aborted_write() {
    use ril_compiler::sema::{
        model::Ty,
        storage_sources::StorageDestination,
        validate::{ValidationIssueKind, solved_facts},
    };
    for case in [
        "tests/regressions/source-observations.ril::matching-record-member-replacement",
        "tests/regressions/source-observations.ril::matching-array-element-replacement",
    ] {
        for target in ["pointer32", "pointer64"] {
            let verified = Session::with_options(
                ril_test::case_bytes(case).to_vec(),
                CheckOptions {
                    target: target.into(),
                    ..Default::default()
                },
            )
            .verify()
            .unwrap_or_else(|outcome| panic!("{case}, {target}: {outcome:?}"));
            let facts = verified.facts();
            solved_facts(facts).unwrap();
            let original = facts
                .storage_writes
                .first()
                .expect("fixture has an actual replacement");
            assert!(original.completed && original.expected.is_some());
            let StorageDestination::Projection {
                receiver, selector, ..
            } = &original.destination
            else {
                panic!("fixture has an original member/index destination")
            };
            let (receiver, selector) = (*receiver, *selector);
            for corrupt_selector in [false, true] {
                let observation = if corrupt_selector {
                    let Some(selector) = selector else { continue };
                    selector
                } else {
                    receiver
                };
                assert_ne!(
                    facts.expressions[observation.expression].value.ty,
                    Ty::Never
                );
                let mut changed = facts.clone();
                changed.expressions[observation.expression].value.ty = Ty::Never;
                let write = &mut changed.storage_writes[0];
                write.completed = false;
                write.expected = None;
                if !corrupt_selector {
                    let StorageDestination::Projection { selector, .. } = &mut write.destination
                    else {
                        unreachable!()
                    };
                    *selector = None;
                }
                let issues = solved_facts(&changed).unwrap_err();
                assert!(
                    issues
                        .iter()
                        .any(|issue| matches!(issue.kind, ValidationIssueKind::StorageSource(_))),
                    "{case}, {target}, corrupt selector={corrupt_selector}: {issues:?}"
                );
            }
        }
    }
}
