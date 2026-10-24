//! Source declaration views follow original HIR binders and typed projections.
use ril_compiler::{CheckOptions, Session, hir::VerifiedProgram};
use ril_compiler_core::projection::TypeProjection;

fn fixture(target: &str) -> VerifiedProgram {
    let source =
        ril_test::case_source("tests/conformance/rest-patterns.ril::record-rest-schema-pointer64");
    Session::with_options(
        source.as_bytes().to_vec(),
        CheckOptions {
            target: target.into(),
            ..Default::default()
        },
    )
    .verify()
    .unwrap_or_else(|error| panic!("{target}: {error:?}"))
}

#[test]
fn binding_introducers_and_record_remainders_reach_core_with_complete_source() {
    use ril_compiler::sema::effect_identity::ArgumentKey;
    for target in ["pointer32", "pointer64"] {
        let program = fixture(target);
        let facts = program.facts();
        let (rest, _) = facts
            .bindings
            .iter()
            .enumerate()
            .find(|(_, binding)| binding.name == "rest")
            .unwrap();
        let id = facts
            .bindings
            .iter()
            .position(|binding| binding.name == "id")
            .unwrap();
        let row = facts
            .binding_sources
            .iter()
            .find(|row| row.binding == id)
            .unwrap();
        assert_ne!(facts.bindings[id].pattern, Some(row.declaration));
        let row = facts
            .binding_sources
            .iter()
            .find(|row| row.binding == rest)
            .unwrap();
        assert_eq!(facts.bindings[rest].pattern, Some(row.declaration));
        assert!(
            matches!(row.path.as_deref(), Some([TypeProjection::RecordRemainder(fields)]) if fields.iter().map(String::as_str).collect::<Vec<_>>() == ["id"])
        );
        let source = facts.source_types.binding_type(rest).unwrap();
        let key = facts.source_types.key(source).unwrap();
        let ArgumentKey::Record { fields, .. } = key else {
            panic!("rest must retain a record view")
        };
        assert!(!fields.iter().any(|field| field.0 == "id"));
        assert!(fields.iter().any(|field| field.0 == "items" && matches!(&field.2,
            ArgumentKey::Array { length: Some(outer), element }
            if outer == "const(int:0)" && matches!(&**element, ArgumentKey::Array {length:Some(inner),..} if inner=="const(int:2)"))));
        ril_compiler::lower::lower_core(&program).unwrap();
    }
}

#[test]
fn hir_projection_work_exhaustion_never_returns_a_partial_binding_plan() {
    let program = fixture("pointer64");
    let facts = program.facts();
    let rest = facts
        .bindings
        .iter()
        .position(|binding| binding.name == "rest")
        .unwrap();
    let row = facts
        .binding_sources
        .iter()
        .find(|row| row.binding == rest)
        .unwrap();
    let hir = facts.semantic_hir.as_ref().unwrap();
    let complete = hir.pattern_bindings(row.declaration, &mut 4096).unwrap();
    assert_eq!(complete.len(), 2);
    assert!(hir.pattern_bindings(row.declaration, &mut 0).is_err());
    assert_eq!(
        hir.pattern_bindings(row.declaration, &mut 4096)
            .unwrap()
            .len(),
        complete.len()
    );
}

#[test]
fn nested_projections_and_aliases_keep_their_original_frozen_interpretation() {
    let source = ril_test::case_source(
        "tests/conformance/rest-patterns.ril::nested-record-rest-view-pointer64",
    );
    for target in ["pointer32", "pointer64"] {
        let program = Session::with_options(
            source.as_bytes().to_vec(),
            CheckOptions {
                target: target.into(),
                ..Default::default()
            },
        )
        .verify()
        .unwrap_or_else(|error| panic!("{target}: {error:?}"));
        let facts = program.facts();
        let rest = facts
            .bindings
            .iter()
            .position(|binding| binding.name == "rest")
            .unwrap();
        let alias = facts
            .bindings
            .iter()
            .position(|binding| binding.name == "alias")
            .unwrap();
        assert_eq!(
            facts.bindings[rest].typing_environment.id(),
            facts.bindings[alias].typing_environment.id()
        );
        let row = facts
            .binding_sources
            .iter()
            .find(|row| row.binding == rest)
            .unwrap();
        assert!(
            matches!(row.path.as_deref(), Some([TypeProjection::Tuple(0), TypeProjection::RecordRemainder(fields)]) if fields.contains("id"))
        );
        let original = facts
            .source_types
            .key(facts.source_types.binding_type(rest).unwrap())
            .unwrap();
        let received = facts
            .source_types
            .key(facts.source_types.binding_type(alias).unwrap())
            .unwrap();
        assert_eq!(original, received);
        ril_compiler::lower::lower_core(&program).unwrap();
    }
}

fn optional_fixture(target: &str) -> VerifiedProgram {
    let source = ril_test::case_source(
        "tests/regressions/source-observations.ril::optional-projection-paths-pointer64",
    );
    Session::with_options(
        source.as_bytes().to_vec(),
        CheckOptions {
            target: target.into(),
            ..Default::default()
        },
    )
    .verify()
    .unwrap_or_else(|error| panic!("{target}: {error:?}"))
}

#[test]
fn original_optional_reads_project_at_each_real_base_and_only_once_at_the_receiver() {
    use ril_compiler::sema::effect_identity::ArgumentKey;
    for target in ["pointer32", "pointer64"] {
        let program = optional_fixture(target);
        let facts = program.facts();
        for name in [
            "named", "field", "computed", "member", "selected", "indexed", "twice", "once",
        ] {
            let receivers: Vec<_> = facts
                .bindings
                .iter()
                .enumerate()
                .filter(|(_, binding)| binding.name == name)
                .collect();
            assert!(!receivers.is_empty(), "{name}");
            for (id, _) in receivers {
                let key = facts
                    .source_types
                    .key(facts.source_types.binding_type(id).unwrap())
                    .unwrap();
                if name == "once" {
                    assert!(
                        matches!(&key, ArgumentKey::Name { name, arguments }
                        if name == "Option" && matches!(arguments.as_slice(), [ArgumentKey::Array {length:Some(length),..}] if length=="const(int:2)")),
                        "{key:?}"
                    );
                } else {
                    assert!(
                        matches!(&key, ArgumentKey::Array { length:Some(length),.. } if length=="const(int:2)"),
                        "{name}: {key:?}"
                    );
                }
            }
        }
        ril_compiler::lower::lower_core(&program).unwrap();
    }
}
