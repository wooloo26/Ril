use ril_compiler::{CheckOptions, Session, sema::validate::solved_facts};

fn record_root(
    graph: &ril_ir::provenance::SourceTypeGraph,
    mut root: ril_ir::provenance::SourceTypeId,
) -> ril_ir::provenance::SourceTypeId {
    let mut seen = std::collections::BTreeSet::new();
    loop {
        assert!(seen.len() < 256 && seen.insert(root));
        match graph.get(root).unwrap() {
            ril_ir::provenance::SourceTypeNode::Alias { target, .. } => root = *target,
            ril_ir::provenance::SourceTypeNode::Container {
                kind: ril_ir::provenance::SourceContainer::Immutable,
                arguments,
            } => {
                assert_eq!(arguments.len(), 1);
                root = arguments[0];
            }
            ril_ir::provenance::SourceTypeNode::Record { .. } => return root,
            node => panic!("recursive record view became {node:?}"),
        }
    }
}

#[test]
fn recursive_copies_and_abrupt_optional_fallbacks_keep_original_source_views() {
    let source = ril_test::case_source("tests/regressions/copy.ril::binary-recursive-copy");
    for target in ["pointer32", "pointer64"] {
        let program = Session::with_options(
            source.as_bytes().to_vec(),
            CheckOptions {
                target: target.into(),
                ..Default::default()
            },
        )
        .verify()
        .unwrap();
        let facts = program.facts();
        solved_facts(facts).unwrap();
        let core = ril_compiler::lower::lower_core(&program).unwrap();
        for name in ["child", "shared"] {
            let binding = facts
                .bindings
                .iter()
                .position(|binding| binding.name == name)
                .unwrap();
            let view = facts.source_types.binding_view(binding).unwrap();
            assert!(matches!(
                facts.source_types.key(view.ty),
                Err(ril_compiler::sema::source_types::SourceTypesError::RecursiveLegacyKey)
            ));
            let source = core
                .provenance
                .binding_sources
                .iter()
                .find(|source| source.binding as usize == binding)
                .unwrap();
            let graph = &core.provenance.source_types;
            let root = record_root(graph, source.root.unwrap());
            let ril_ir::provenance::SourceTypeNode::Record { fields, row: None } =
                graph.get(root).unwrap()
            else {
                panic!("closed Node record")
            };
            assert_eq!(fields.len(), 3);
            for name in ["left", "right"] {
                let field = fields.iter().find(|field| field.label == name).unwrap();
                assert!(field.mutable);
                let ril_ir::provenance::SourceTypeNode::Container {
                    kind: ril_ir::provenance::SourceContainer::Option,
                    arguments,
                } = graph.get(field.value).unwrap()
                else {
                    panic!("recursive optional child")
                };
                assert_eq!(arguments.len(), 1);
                assert_eq!(
                    record_root(graph, arguments[0]),
                    root,
                    "the declaration backedge must survive transport"
                );
            }
        }
        let mut damaged = facts.clone();
        damaged.source_types = Default::default();
        assert!(solved_facts(&damaged).is_err());
        let call = facts
            .copy_call_events
            .iter()
            .find(|event| event.copy_operation.is_some())
            .unwrap();
        let mut damaged = facts.clone();
        damaged
            .call_arguments
            .iter_mut()
            .find(|row| row.source_event == call.id)
            .unwrap()
            .supplied
            .get_mut(&0)
            .unwrap()
            .expression = call.result_expression.unwrap();
        assert!(solved_facts(&damaged).is_err());
        let mut damaged = facts.clone();
        damaged.copy_call_events[call.id.0 as usize].copy_operation = None;
        assert!(solved_facts(&damaged).is_err());
    }
}
