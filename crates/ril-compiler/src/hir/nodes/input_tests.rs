use std::sync::Arc;

#[test]
fn declaration_input_authorization_follows_original_roots_and_cannot_be_deleted() {
    let case =
        ril_test::case_by_id("tests/conformance/external.ril::accept-declaration-initializer");
    let files = case
        .files
        .iter()
        .map(|file| crate::session::ProjectSource {
            path: std::path::PathBuf::from("virtual").join(&file.name),
            bytes: file.bytes.clone(),
        })
        .collect();
    let program = crate::Session::with_project(
        std::path::PathBuf::from("virtual").join(&case.root),
        files,
        crate::CheckOptions::default(),
    )
    .unwrap()
    .verify()
    .unwrap();
    let facts = program.facts();
    let hir = facts.semantic_hir.as_ref().unwrap();
    assert!(!hir.declaration_roots().is_empty());
    assert!(
        hir.declaration_roots()
            .iter()
            .all(|root| hir.roots().contains(root))
    );
    let mut diagnostics = facts.clone();
    for row in &facts.binding_sources {
        diagnostics.expressions[row.initializer.expression].span =
            ril_compiler_core::source::Span {
                file: ril_compiler_core::source::FileId(u32::MAX),
                start: 33,
                end: 77,
            };
    }
    crate::sema::validate::solved_facts(&diagnostics)
        .expect("diagnostic locations cannot reclassify declaration-unit inputs");
    let mut missing = facts.clone();
    Arc::make_mut(missing.semantic_hir.as_mut().unwrap())
        .declaration_roots
        .clear();
    let errors = crate::sema::validate::solved_facts(&missing)
        .expect_err("an ambient value survived deletion of its declaration input");
    assert!(
        format!("{errors:?}").contains("canonical input authorization"),
        "{errors:?}"
    );
    let mut erased = facts.clone();
    erased.bindings.clear();
    erased.binding_sources.clear();
    erased.source_types = Default::default();
    let errors = crate::sema::validate::solved_facts(&erased)
        .expect_err("declaration emissions lost all receiving metadata");
    assert!(
        format!("{errors:?}").contains("actual HIR initialization lost its binding reception"),
        "{errors:?}"
    );
    let mut budgeted = (**hir).clone();
    let original = budgeted.declaration_roots.clone();
    assert!(
        budgeted
            .classify_declaration_units(&Default::default(), &mut 0)
            .is_err()
    );
    assert_eq!(budgeted.declaration_roots, original);
}
