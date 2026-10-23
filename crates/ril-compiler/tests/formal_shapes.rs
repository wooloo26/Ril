//! Symbolic constructor payloads keep their declaration views and shape bounds.
use ril_compiler::{CheckOptions, Session, hir::VerifiedProgram, sema::validate::solved_facts};

fn fixture(case: &str, target: &str) -> VerifiedProgram {
    let source = ril_test::case_bytes(case);
    let snapshot = Session::with_options(
        source.to_vec(),
        CheckOptions {
            target: target.into(),
            ..Default::default()
        },
    )
    .analyze();
    let diagnostics = format!("{:?}; {:?}", snapshot.diagnostics(), snapshot.unresolved());
    snapshot
        .into_verified()
        .unwrap_or_else(|error| panic!("{target} {case}: {error:?}; {diagnostics}"))
}

#[test]
fn symbolic_constructor_payload_shapes_reach_core_on_both_layouts() {
    for target in ["pointer32", "pointer64"] {
        let program = fixture(
            "tests/regressions/formal-shapes.ril::optional-array-shapes-pointer64",
            target,
        );
        ril_compiler::lower::lower_core(&program).unwrap();
    }
}

#[test]
fn handler_record_remainders_keep_their_original_nonempty_source_projection() {
    use ril_compiler::sema::{effect_identity::ArgumentKey, scopes::ScopeOrigin};
    for target in ["pointer32", "pointer64"] {
        let program = fixture(
            "tests/conformance/parameter-patterns.ril::parameter-record-option-sources-pointer64",
            target,
        );
        let facts = program.facts();
        let (index, binding) = facts
            .bindings
            .iter()
            .enumerate()
            .find(|(_, binding)| {
                binding.parameter
                    && binding.name == "rest"
                    && facts
                        .scopes
                        .get(&binding.owner)
                        .is_some_and(|scope| matches!(scope.origin, ScopeOrigin::Operation(_)))
            })
            .unwrap();
        let key = facts
            .source_types
            .key(facts.source_types.binding_type(index).unwrap())
            .unwrap();
        let ArgumentKey::Record { fields, .. } = key else {
            panic!("remainder must retain its record view")
        };
        assert!(!fields.iter().any(|field| field.0 == "id"));
        assert!(fields.iter().any(|field| field.0 == "items" && matches!(&field.2, ArgumentKey::Array { length: Some(outer), element } if outer == "const(int:0)" && matches!(&**element, ArgumentKey::Array { length: Some(inner), .. } if inner == "const(int:2)"))));
        let sibling = facts
            .bindings
            .iter()
            .find(|other| other.owner == binding.owner && other.name == "id")
            .unwrap()
            .pattern;
        for mutation in 0..4 {
            let mut changed = facts.clone();
            match mutation {
                0 => changed.bindings[index].pattern = None,
                1 => changed.bindings[index].pattern = sibling,
                2 => changed.bindings[index].typing_environment = Default::default(),
                _ => changed.source_types = Default::default(),
            }
            assert!(
                solved_facts(&changed).is_err(),
                "{target} handler projection mutation {mutation}"
            );
        }
        ril_compiler::lower::lower_core(&program).unwrap();
    }
}
