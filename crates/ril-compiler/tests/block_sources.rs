use ril_compiler::{CheckOptions, Session};

#[test]
fn empty_blocks_keep_their_actual_expression_owners() {
    for target in ["pointer32", "pointer64"] {
        let program = Session::with_options(
            ril_test::case_bytes("tests/regressions/block-sources.ril::empty-block-contexts")
                .to_vec(),
            CheckOptions {
                target: target.into(),
                ..Default::default()
            },
        )
        .verify()
        .unwrap_or_else(|outcome| panic!("{target}: {outcome:?}"));
        ril_compiler::lower::lower_core(&program).unwrap();
    }
}

#[test]
fn an_empty_block_cannot_borrow_another_owner_or_drop_its_actual_completion() {
    let program = Session::new(
        ril_test::case_bytes("tests/regressions/block-sources.ril::empty-block-contexts").to_vec(),
    )
    .verify()
    .unwrap();
    let facts = program.facts();
    let hir = facts.semantic_hir.as_deref().unwrap();
    let roots: Vec<_> = facts
        .evaluations
        .iter()
        .filter_map(|record| {
            let identity = record.identity?;
            matches!(&hir.expression(identity.source)?.kind,
            ril_compiler::hir::nodes::ExprKind::Block(block) if block.statements.is_empty())
            .then_some(record.id.0 as usize)
        })
        .collect();
    assert!(roots.len() >= 2);
    let (first, other) = (roots[0], roots[1]);
    let identity = facts.evaluations[first].identity.unwrap();
    let replacement = facts.evaluations[other].identity.unwrap();
    for mutation in 0..4 {
        let mut changed = facts.clone();
        match mutation {
            0 => changed.evaluations[first].identity.as_mut().unwrap().source = replacement.source,
            1 => {
                changed.evaluations[first]
                    .identity
                    .as_mut()
                    .unwrap()
                    .activation = replacement.activation
            }
            2 => changed.expressions[first].source_id = Some(replacement.source),
            3 => changed.activations[identity.activation.0 as usize].result = None,
            _ => unreachable!(),
        }
        assert!(
            ril_compiler::sema::validate::solved_facts(&changed).is_err(),
            "block mutation {mutation}"
        );
    }
}
