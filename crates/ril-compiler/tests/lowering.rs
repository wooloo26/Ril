use ril_compiler::Session;

#[test]
fn core_compiles_sum_branches_with_heap_payloads() {
    let source = b"type Cell={mut value:int}\ntype Choice{Empty,Value(Cell)}\nfn choose(flag:bool)->Choice{if flag{Choice::Empty}else{Choice::Value(Cell.{value:1})}}";
    let verified = Session::new(source.to_vec()).verify().unwrap();
    let core = ril_compiler::lower::lower_core(&verified).unwrap();
    assert!(
        core.functions
            .iter()
            .any(|function| function.name == "choose")
    );
}

#[test]
fn core_compiles_iterators_after_frontend_inference() {
    let source = b"use ril/iter\nfn example(){let source=Iter::indexed([1,2]);let mut cursor=Iter::cursor(0);assert(Iter::pull(mut cursor,source)==Some(1))}";
    let verified = Session::new(source.to_vec()).verify().unwrap();
    let core = ril_compiler::lower::lower_core(&verified).unwrap();
    assert!(
        core.functions
            .iter()
            .any(|function| function.name == "example")
    );
    let library = verified
        .facts()
        .functions
        .iter()
        .filter(|function| function.syntax.span.file.0 != 0)
        .collect::<Vec<_>>();
    assert_eq!(library.len(), 8);
    for function in library {
        assert!(
            core.functions
                .iter()
                .any(|lowered| lowered.definition == function.definition
                    && lowered.role == ril_ir::core::FunctionRole::Ordinary)
        );
    }
}

#[test]
fn core_compiles_bounded_divergence_with_an_exhaustion_handler() {
    let source = b"fn spin()->int{loop{}}\nhalt fn bounded()->?int{with Div::exhausted()->None;Some(Div::budget(20,spin))}";
    let verified = Session::new(source.to_vec()).verify().unwrap();
    let core = ril_compiler::lower::lower_core(&verified).unwrap();
    assert!(
        core.functions
            .iter()
            .any(|function| function.name == "bounded")
    );
    let source_witnesses = &verified.facts().budget_termination;
    assert!(!source_witnesses.is_empty());
}

#[test]
fn core_generic_parameters_use_owning_declarations() {
    let session =
        Session::new(b"fn identity<T>(value:T)->T { value }\nfn encoded()->f32{16777217}".to_vec());
    let verified = session.verify().unwrap();
    let core = ril_compiler::lower::lower_core(&verified).unwrap();
    assert_eq!(core.functions[0].generic_parameters.len(), 1);
    let parameter = core.functions[0].generic_parameters[0];
    assert_eq!(parameter.declaration, core.functions[0].definition);
    assert_eq!(parameter.index, 0);
    assert!(!verified.facts().numeric_uses.is_empty());
}
#[test]
fn verification_keeps_the_full_resolved_source_when_meta_definitions_are_materialized() {
    let session = Session::new(b"meta fn answer()->int{42}\nfn example(){}".to_vec());
    let program = session.verify().unwrap();
    assert_eq!(program.resolved_source().statements.len(), 2);
    assert_eq!(program.syntax().statements.len(), 1);
    assert_eq!(program.static_definitions().len(), 1);
    let _core = ril_compiler::lower::lower_core(&program).unwrap();
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
    ril_codegen::lower::lower_native_with_entry(&core, "example").unwrap();
}
