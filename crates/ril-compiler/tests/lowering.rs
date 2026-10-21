use ril_compiler::Session;
use ril_ir::provenance::Type;

#[test]
fn core_retains_tag_specific_payload_origins_after_a_sum_branch_join() {
    let source = b"type Cell={mut value:int}\ntype Choice{Empty,Value(Cell)}\nfn choose(flag:bool)->Choice{if flag{Choice::Empty}else{Choice::Value(Cell.{value:1})}}";
    let verified = Session::new(source.to_vec()).verify().unwrap();
    let core = ril_compiler::lower::lower_core(&verified).unwrap();
    let mut joined = false;
    for (source, lowered) in verified
        .facts()
        .expressions
        .iter()
        .zip(&core.provenance.values)
    {
        assert_eq!(
            source.value.variant_witnesses.keys().collect::<Vec<_>>(),
            lowered.variant_witnesses.keys().collect::<Vec<_>>()
        );
        if source.value.variant_tag.is_none() && source.value.variant_witnesses.len() > 1 {
            joined = true;
            assert!(
                lowered.variant_payload.is_none(),
                "an unknown tag cannot substitute one variant's payload"
            );
        }
        for (tag, payload) in &source.value.variant_witnesses {
            let lowered = &lowered.variant_witnesses[tag];
            assert_eq!(lowered.cause, payload.cause);
            assert_eq!(
                lowered
                    .origins
                    .iter()
                    .map(|origin| origin.0)
                    .collect::<Vec<_>>(),
                payload
                    .origins
                    .nodes
                    .iter()
                    .map(|origin| origin.0)
                    .collect::<Vec<_>>()
            );
        }
    }
    assert!(
        joined,
        "the source join must retain both actual tag witnesses"
    );
}

#[test]
fn core_keeps_iterator_step_types_and_its_actual_capturing_environment() {
    let source = b"use ril/iter\nfn example(){let source=Iter::indexed([1,2]);let mut cursor=Iter::cursor(0);assert(Iter::pull(mut cursor,source)==Some(1))}";
    let verified = Session::new(source.to_vec()).verify().unwrap();
    let core = ril_compiler::lower::lower_core(&verified).unwrap();
    assert!(!verified.facts().iter_steps.is_empty());
    assert_eq!(
        core.provenance.iter_steps.len(),
        verified.facts().iter_steps.len()
    );
    for (source, lowered) in verified
        .facts()
        .iter_steps
        .iter()
        .zip(&core.provenance.iter_steps)
    {
        assert_eq!(source.identity, lowered.identity);
        assert_eq!(source.closure as u32, lowered.closure);
        assert_eq!(source.span, lowered.span);
        assert_eq!(source.cause, lowered.cause);
        let closure = &verified.facts().closures[source.closure];
        assert!(
            !closure.captures.is_empty(),
            "indexed must retain its real source"
        );
        assert!(matches!(
            core.provenance.types[lowered.state.0 as usize],
            Type::Integer(_)
        ));
        assert!(matches!(
            core.provenance.types[lowered.item.0 as usize],
            Type::Integer(_)
        ));
        assert!(core.provenance.callables.iter().any(|environment| matches!(environment.callable, ril_ir::provenance::Callable::Closure(id) if id == lowered.closure)));
    }
}

#[test]
fn core_retains_budget_termination_without_erasing_divergent_action_evidence() {
    let source = b"fn spin()->int{loop{}}\nhalt fn bounded()->?int{with Div::exhausted()->None;Some(Div::budget(20,spin))}";
    let verified = Session::new(source.to_vec()).verify().unwrap();
    let core = ril_compiler::lower::lower_core(&verified).unwrap();
    let source_witnesses = &verified.facts().budget_termination;
    assert!(!source_witnesses.is_empty());
    assert_eq!(
        core.provenance.budget_termination.len(),
        source_witnesses.len()
    );
    for (source, lowered) in source_witnesses
        .iter()
        .zip(&core.provenance.budget_termination)
    {
        assert_eq!(lowered.span, source.span);
        assert_eq!(lowered.cause, source.cause);
        assert_eq!(lowered.exhaustion_operation, source.exhaustion_operation);
        assert_eq!(lowered.callee_coverage, source.callee_coverage);
        assert_eq!(lowered.cleanup_coverage, source.cleanup_coverage);
        for (source, lowered) in [
            (&source.explicit_evaluation, &lowered.explicit_evaluation),
            (&source.action_invocation, &lowered.action_invocation),
            (&source.recovery, &lowered.recovery),
        ] {
            assert_eq!(lowered.may_diverge, source.may_diverge);
            assert_eq!(lowered.unresolved, source.unresolved);
            assert_eq!(
                lowered.callable_parameters,
                source
                    .callable_parameters
                    .iter()
                    .map(|&id| id as u32)
                    .collect::<Vec<_>>()
            );
        }
        assert!(lowered.action_invocation.may_diverge);
        assert!(!lowered.explicit_evaluation.may_diverge && !lowered.recovery.may_diverge);
    }
}

#[test]
fn core_retains_generic_identity_and_all_traceable_semantic_evidence() {
    let session = Session::new(b"fn identity<T>(value:T)->T { value }".to_vec());
    let verified = session.verify().unwrap();
    let core = ril_compiler::lower::lower_core(&verified).unwrap();
    assert_eq!(core.functions[0].generic_parameters.len(), 1);
    let parameter = core.functions[0].generic_parameters[0];
    assert!(matches!(
        core.provenance.types[parameter.0 as usize],
        Type::Generic(_)
    ));
    assert_eq!(
        core.provenance.origins.len(),
        verified.facts().heap.nodes.len()
    );
    assert_eq!(
        core.provenance.values.len(),
        verified.facts().expressions.len()
    );
    assert_eq!(
        core.provenance.bindings.len(),
        verified.facts().bindings.len()
    );
    assert_eq!(core.provenance.causes, verified.facts().explanations.causes);
    assert_eq!(core.provenance.generic_binders[0].name, "T");
    assert_eq!(
        core.provenance.contextual_types.len(),
        verified.facts().contextual_types.len()
    );
}
#[test]
fn verification_keeps_the_full_resolved_source_when_meta_definitions_are_materialized() {
    let session = Session::new(b"meta fn answer()->int{42}\nfn example(){}".to_vec());
    let program = session.verify().unwrap();
    assert_eq!(program.resolved_source().statements.len(), 2);
    assert_eq!(program.syntax().statements.len(), 1);
    assert_eq!(program.static_definitions().len(), 1);
    let core = ril_compiler::lower::lower_core(&program).unwrap();
    assert_eq!(
        core.provenance.static_termination.len(),
        program.static_termination().len()
    );
    assert!(!core.provenance.static_termination.is_empty());
}
#[test]
fn a_formal_callback_is_not_specialized_to_one_observed_effect_operation() {
    let program = Session::new(
        br#"
eff Left{read()->int}
eff Right{read()->int}
fn apply(action:fn()->int)->int{action()}
fn example(){
    with Left::read()->resume 1
    with Right::read()->resume 2
    assert(apply(Left::read)==1)
    assert(apply(Right::read)==2)
}

"#
        .to_vec(),
    )
    .verify()
    .unwrap();
    let core = ril_compiler::lower::lower_core(&program).unwrap();
    let body = &core
        .functions
        .iter()
        .find(|function| function.name == "apply")
        .unwrap()
        .body;
    assert!(matches!(
        &body.statements[0],
        ril_ir::core::Statement::Expr {
            expression: ril_ir::core::Expr {
                kind: ril_ir::core::ExprKind::Call { .. },
                ..
            },
            ..
        }
    ));
}

#[test]
fn call_metadata_keeps_the_visible_labels_of_an_ascribed_alias() {
    let source = br#"fn identity(original:int=1)->int{original}
fn example(){let alias:fn(renamed:int)->int=identity;let _=alias(renamed:7)}"#;
    let program = Session::new(source.to_vec()).verify().unwrap();
    let core = ril_compiler::lower::lower_core(&program).unwrap();
    let call = std::str::from_utf8(source)
        .unwrap()
        .find("alias(renamed:7)")
        .unwrap() as u32;
    let signature = core
        .call_signatures
        .iter()
        .find(|signature| signature.span.start == call)
        .unwrap();
    assert_eq!(
        signature.parameters,
        vec![ril_ir::core::CallParameter {
            label: Some("renamed".into()),
            has_default: false
        }]
    );
}

#[test]
fn core_retains_the_opaque_return_contract_of_an_aliased_exported_closure() {
    use ril_compiler::ProjectSource;

    fn check_bound(
        source: &std::sync::Arc<ril_compiler::sema::model::CallableReturnBound>,
        id: ril_ir::provenance::ReturnContractId,
        graph: &ril_ir::provenance::Graph,
        shared: &mut std::collections::BTreeMap<usize, ril_ir::provenance::ReturnContractId>,
    ) {
        let pointer = std::sync::Arc::as_ptr(source) as usize;
        if let Some(previous) = shared.insert(pointer, id) {
            assert_eq!(
                previous, id,
                "a shared semantic stage retains one Core node"
            );
            return;
        }
        let lowered = &graph.callable_return_contracts[id.0 as usize];
        assert_eq!(lowered.raw, source.raw);
        assert_eq!(lowered.span, source.span);
        assert_eq!(lowered.syntax.text, source.syntax.text);
        let environment = &graph.frozen_environments[lowered.environment.0 as usize];
        assert_eq!(
            environment.lexical,
            source
                .typing_environment
                .contract_bindings
                .iter()
                .map(|(name, &binding)| (name.clone(), binding as u32))
                .collect::<Vec<_>>()
        );
        assert_eq!(lowered.callables.len(), source.callables.len());
        for (source, lowered) in source.callables.iter().zip(&lowered.callables) {
            assert!(matches!(
                (source, lowered),
                (
                    ril_compiler::sema::model::Callable::Closure(source),
                    ril_ir::provenance::Callable::Closure(lowered)
                ) if *source as u32 == *lowered
            ));
        }
        assert!(!lowered.callables.is_empty());
        assert!(matches!(
            &graph.types[lowered.target.0 as usize],
            Type::Named(name) if name.ends_with("Value")
        ));
        assert_eq!(lowered.predecessors.len(), source.predecessors.len());
        for (source, id) in source.predecessors.iter().zip(&lowered.predecessors) {
            check_bound(source, *id, graph, shared);
        }
    }

    let directory = std::env::temp_dir().join("ril-core-callable-return-contract");
    let verified = Session::with_project(
        directory.join("root.ril"),
        vec![
            ProjectSource {
                path: directory.join("root.ril"),
                bytes: b"use token\nfn example(){let action=Token::make();let alias:fn()->Token::Value=action;assert(Token::reveal(alias())==7)}".to_vec(),
            },
            ProjectSource {
                path: directory.join("token.ril"),
                bytes: b"pub opaque type Value=int\npub type Action=fn()->Value\npub fn make()->Action{\\->7}\npub fn reveal(value:Value)->int{value}".to_vec(),
            },
        ],
        Default::default(),
    )
    .unwrap()
    .verify()
    .unwrap();
    let core = ril_compiler::lower::lower_core(&verified).unwrap();
    let mut shared = std::collections::BTreeMap::new();
    for (source, lowered) in verified
        .facts()
        .expressions
        .iter()
        .zip(&core.provenance.values)
    {
        assert_eq!(
            source.value.callable_returns.len(),
            lowered.callable_returns.len()
        );
        for (source, id) in source
            .value
            .callable_returns
            .iter()
            .zip(&lowered.callable_returns)
        {
            check_bound(source, *id, &core.provenance, &mut shared);
        }
    }
    assert!(
        shared.len() > 1,
        "the returned closure must retain an actual opaque result contract"
    );
}
