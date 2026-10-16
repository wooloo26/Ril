use ril_compiler::{CompilationOutcome, Session};

fn accepts(source: &str) {
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(outcome, CompilationOutcome::Accepted { .. }),
        "{source}: {outcome:?}"
    );
}
fn rejects_family(source: &str) {
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(&outcome,CompilationOutcome::Rejected{diagnostics} if diagnostics.iter().any(|d|d.code=="E0810")),
        "{source}: {outcome:?}"
    );
}

#[test]
fn static_local_data_shadows_an_ordinary_global_callable() {
    accepts(
        "meta let ROOT={let child=[7];(child,child)}\nfn child()->[]int &{ROOT}{ROOT.0}\nfn example() &{ROOT}{assert(child()==[7])}",
    );
    accepts(
        "fn child()->int{9}\nmeta fn pick(child:int)->int{child}\nmeta let _=assert(pick(3)==3)",
    );
    accepts(
        "fn child()->int{9}\nmeta let VALUES=Array::map([1,2],\\child->child+1)\nmeta let _=assert(VALUES==[2,3])",
    );
}

#[test]
fn match_and_branch_locals_have_only_their_lexical_scope() {
    accepts(
        "fn child()->int{9}\nmeta let VALUE=match Some(2){Some(child)->child,None->0}\nmeta let _=assert(VALUE==2)",
    );
    accepts(
        "fn child()->int{9}\nmeta fn pick()->int{if Some(2) is Some(2) {let child=2;child}else{0}}\nmeta let _=assert(pick()==2)",
    );
    rejects_family("fn child()->int{9}\nmeta fn bad()->int{let saved={let child=1;child};child()}");
    rejects_family(
        "fn child()->int{9}\nmeta fn bad(flag:bool)->int{if flag{let child=1;child}else{child()}}",
    );
}

#[test]
fn initializers_defaults_generic_values_and_unused_bodies_keep_family_checks() {
    for source in [
        "fn child()->int{9}\nmeta fn bad()->int{let child=child;child()}",
        "fn child()->int{9}\nmeta fn bad()->int{let first=child();let child=1;first}",
        "fn child()->int{9}\nmeta fn bad()->int{let unused=\\->child();1}",
        "fn child()->int{9}\nmeta fn bad(value:int=child())->int{value}",
        "meta fn child()->int{9}\nfn bad(callback:fn()->int=child)->int{callback()}",
        "meta fn identity<T>(value:T)->T{value}\nfn bad(){let callback=identity<int>}",
    ] {
        rejects_family(source);
    }
}

#[test]
fn unevaluated_typeof_does_not_invoke_the_ordinary_callable() {
    accepts(
        "fn child()->int{panic(\"must not execute\")}\ntype Of=\\T->type<typeof child()>\ntype Number=Of<bool>\nmeta let _=assert(type<Number>==type<int>)",
    );
}

#[test]
fn nominal_constructor_values_reach_their_actual_static_implementation_boundary() {
    for source in [
        "type Token(int)\nmeta let ROOT=Token(1)",
        "type Token(int)\nmeta let FACTORY=Token",
    ] {
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        assert!(
            matches!(&outcome,CompilationOutcome::NotImplemented{reason} if reason.detail.contains("constructor")),
            "{source}: {outcome:?}"
        );
    }
    let outcome = Session::new(b"type Row={count:int}\nmeta let VALUE=Row".to_vec()).check();
    assert!(
        matches!(&outcome,CompilationOutcome::Rejected{diagnostics} if diagnostics.iter().any(|d|d.code=="E0319")),
        "{outcome:?}"
    );
}

#[test]
fn owned_ast_names_cannot_collide_with_static_declaration_identities() {
    use ril_syntax::ast::{ExprKind, StmtKind};
    let mut parsed = ril_syntax::parse(
        "fn runtime_answer()->int{2}\nmeta fn answer()->int{1}\nmeta let VALUE=runtime_answer()",
    );
    let collision = "ril__static_scope_0_answer";
    let StmtKind::Function(function) = &mut parsed.program.statements[0].kind else {
        panic!()
    };
    function.name = collision.into();
    let StmtKind::Binding(binding) = &mut parsed.program.statements[2].kind else {
        panic!()
    };
    let ExprKind::Call { callee, .. } = &mut binding.value.kind else {
        panic!()
    };
    callee.kind = ExprKind::Name(collision.into());
    let outcome = Session::new(vec![]).verify_program(&parsed.program);
    assert!(
        matches!(outcome, Err(CompilationOutcome::Rejected { .. })),
        "{outcome:?}"
    );
}
