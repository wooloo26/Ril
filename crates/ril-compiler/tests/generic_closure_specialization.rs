use ril_compiler::Session;
use ril_compiler_core::ids::CallableOwner;

#[test]
fn abstract_live_captures_cannot_be_published_by_an_immutable_binding() {
    let source =
        include_str!("../../ril-cli/tests/fixtures/generic_closures/invalid_immutable_capture.ril");
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&outcome,ril_compiler::CompilationOutcome::Rejected {diagnostics} if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0535")),
        "{outcome:?}"
    );
}

#[test]
fn escaping_instances_map_closures_and_recipes_to_their_actual_static_owner() {
    let source =
        include_str!("../../ril-cli/tests/fixtures/generic_closures/retained_instances.ril");
    let verified = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    let program = ril_compiler::lower::lower_core(&verified).unwrap();
    assert_eq!(program.provenance.specializations.len(), 2);
    let mut sources = std::collections::BTreeSet::new();
    let mut targets = std::collections::BTreeSet::new();
    for instance in &program.provenance.specializations {
        let mut closures = instance
            .owners
            .iter()
            .filter(|mapping| matches!(mapping.source, CallableOwner::Lambda(_)));
        let closure = closures.next().unwrap();
        assert!(closures.next().is_none());
        assert_ne!(closure.source, closure.target);
        sources.insert(closure.source);
        assert!(targets.insert(closure.target));
        let CallableOwner::Lambda(target) = closure.target else {
            panic!()
        };
        assert!(
            program
                .provenance
                .closure_sites
                .iter()
                .any(|site| site.id == target
                    && site.owner == CallableOwner::Function(instance.definition))
        );
        let proof = program
            .provenance
            .retained_handlers
            .iter()
            .find(|proof| proof.callable == Some(closure.target))
            .unwrap();
        let definitions = proof.definitions.as_ref().unwrap();
        assert_eq!(definitions.len(), 1);
        assert!(
            instance
                .handlers
                .iter()
                .any(|mapping| mapping.target == definitions[0])
        );
        assert!(matches!(
            &program.provenance.types[proof.answer.0 as usize],
            ril_ir::provenance::Type::Integer(_) | ril_ir::provenance::Type::String
        ));
    }
    assert_eq!(
        sources.len(),
        1,
        "same source closure site, different concrete owners"
    );
}

#[test]
fn nested_sites_follow_their_specialized_parent_closure() {
    let source =
        include_str!("../../ril-cli/tests/fixtures/generic_closures/immediate_instances.ril");
    let verified = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    let program = ril_compiler::lower::lower_core(&verified).unwrap();
    for instance in &program.provenance.specializations {
        let closures: Vec<_> = instance
            .owners
            .iter()
            .filter(|mapping| matches!(mapping.source, CallableOwner::Lambda(_)))
            .collect();
        assert_eq!(closures.len(), 2);
        let targets: std::collections::BTreeSet<_> =
            closures.iter().map(|mapping| mapping.target).collect();
        assert!(
            program
                .provenance
                .closure_sites
                .iter()
                .any(|site| targets.contains(&CallableOwner::Lambda(site.id))
                    && targets.contains(&site.owner))
        );
    }
}
