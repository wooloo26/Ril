use ril_compiler::Session;

fn core(source: &str) -> ril_ir::core::Program {
    let program = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    ril_compiler::lower::lower_core(&program).unwrap()
}

#[test]
fn closed_effect_calls_get_distinct_owners_and_transitive_callee_instances() {
    let program = core(
        r#"
eff Read<T>{get()->T}
fn read<U>(witness:U)->U @Read<U>{Read<U>::get()}
fn forward<T>(value:T)->T @Read<T>{read(value)}
fn main(){
    with {Read<int>::get()->resume 7,Read<str>::get()->resume "seven"}
    assert(forward(0)==7 && forward("")=="seven")
    assert(forward(1)==7)
}
"#,
    );
    assert_eq!(program.provenance.specializations.len(), 4);
    let ids: std::collections::BTreeSet<_> = program
        .functions
        .iter()
        .map(|function| function.definition)
        .collect();
    assert_eq!(ids.len(), program.functions.len());
    for instance in &program.provenance.specializations {
        assert_ne!(instance.template, instance.definition);
        assert!(!instance.invocations.is_empty());
        assert!(
            program
                .functions
                .iter()
                .any(|function| function.definition == instance.definition
                    && function.name == instance.name
                    && function.generic_parameters.is_empty())
        );
    }
    let native = ril_codegen::lower::lower_native(&program).unwrap();
    assert_eq!(native.specializations.len(), 4);
}

#[test]
fn extracted_or_uninstantiated_symbolic_callables_do_not_borrow_a_nearby_instance() {
    for source in [
        "eff Read<T>{get()->T}\nfn read<T>(value:T)->T @Read<T>{Read<T>::get()}\nfn main(){}",
        "eff Read<T>{get()->T}\nfn read<T>(value:T)->T @Read<T>{Read<T>::get()}\nfn main(){with Read<int>::get()->resume 7;assert(read(0)==7);let stored=read;assert(stored(0)==7)}",
    ] {
        let verified = Session::new(source.as_bytes().to_vec()).verify().unwrap();
        let result = ril_compiler::lower::lower_core(&verified);
        assert!(result.is_err(), "{source}: {result:?}");
    }
}

#[test]
fn previewed_branches_have_closed_operation_coverage_for_both_runtime_paths() {
    let source = "eff Read<T>{get()->T}\nfn read<T>(value:T,enabled:bool)->T @Read<T>{if enabled{Read<T>::get()}else{value}}\nfn main(){with Read<int>::get()->resume 7;assert(read(0,false)==0 && read(0,true)==7)}";
    let verified = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    let closed = *verified
        .facts()
        .effect_instances
        .iter()
        .find(|instance| instance.key.is_closed())
        .unwrap()
        .operations
        .first()
        .unwrap();
    let program = ril_compiler::lower::lower_core(&verified).unwrap();
    assert_eq!(program.provenance.specializations.len(), 1);
    let specialized = &program
        .functions
        .iter()
        .find(|function| function.definition == program.provenance.specializations[0].definition)
        .unwrap()
        .body;
    let ril_ir::core::Statement::Expr { expression, .. } = &specialized.statements[0] else {
        panic!()
    };
    let ril_ir::core::ExprKind::If { then_branch, .. } = &expression.kind else {
        panic!()
    };
    let ril_ir::core::ExprKind::Block(block) = &then_branch.kind else {
        panic!()
    };
    assert!(
        matches!(&block.statements[0],ril_ir::core::Statement::Expr {expression:ril_ir::core::Expr {kind:ril_ir::core::ExprKind::Perform {operation,..},..},..} if *operation==closed)
    );
}

#[test]
fn local_handler_sites_are_remapped_for_each_static_instance() {
    let program = core(
        r#"
eff Read<T>{get()->T}
fn local<T>(value:T)->T{with Read<T>::get()->resume value;Read<T>::get()}
fn main(){assert(local(7)==7 && local("seven")=="seven" && local(9)==9)}
"#,
    );
    assert_eq!(program.provenance.specializations.len(), 2);
    let mapped: Vec<_> = program
        .provenance
        .specializations
        .iter()
        .flat_map(|instance| &instance.handlers)
        .collect();
    assert_eq!(mapped.len(), 2);
    assert_eq!(mapped[0].source, mapped[1].source);
    assert_ne!(mapped[0].target, mapped[1].target);
    assert_ne!(mapped[0].source, mapped[0].target);
    ril_codegen::lower::lower_native(&program).unwrap();
}
