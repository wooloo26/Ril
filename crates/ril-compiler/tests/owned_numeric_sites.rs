use ril_compiler::{CompilationOutcome, Session};
use ril_ir::core::{ExprKind as CoreExpr, Literal as CoreLiteral, Statement as CoreStatement};
use ril_syntax::ast::StmtKind;

const SOURCE: &str = r#"pub fn test_native(){
    let narrow:f32=16777217.0
    let ordinary=16777217.0
    assert("{ordinary}"=="16777217.0")
}"#;

#[test]
fn an_unannotated_neighbor_keeps_its_default_f64_literal_encoding() {
    let verified = Session::new(SOURCE.as_bytes().to_vec()).verify().unwrap();
    let ordinary = verified
        .facts()
        .bindings
        .iter()
        .find(|binding| binding.name == "ordinary")
        .unwrap();
    assert_eq!(
        ordinary.value.ty,
        ril_compiler::sema::model::Ty::Float("f64".into())
    );
    let core = ril_compiler::lower::lower_core(&verified).unwrap();
    let CoreStatement::Bind { value, .. } = &core.functions[0].body.statements[1] else {
        panic!()
    };
    assert!(matches!(
        value.kind,
        CoreExpr::Literal(CoreLiteral::Float {
            value: 16_777_217.0,
            bits: 64
        })
    ));
}

#[test]
fn an_explicit_numeric_context_cannot_retype_another_owned_ast_literal() {
    let mut parsed = ril_syntax::parse(SOURCE);
    let StmtKind::Function(function) = &mut parsed.program.statements[0].kind else {
        panic!()
    };
    let statements = &mut function.body.as_mut().unwrap().statements;
    let StmtKind::Binding(narrow) = &statements[0].kind else {
        panic!()
    };
    let shared = narrow.value.span;
    let StmtKind::Binding(ordinary) = &mut statements[1].kind else {
        panic!()
    };
    ordinary.value.span = shared;
    let result = Session::new(SOURCE.as_bytes().to_vec()).verify_program(&parsed.program);
    assert!(
        matches!(result, Err(CompilationOutcome::NotImplemented { .. })),
        "a numeric collision received a semantic certificate"
    );
}

#[test]
fn numeric_context_collisions_are_not_confined_to_one_callable_owner() {
    let source = "fn first(){let narrow:f32=16777217.0}\nfn second(){let ordinary=16777217.0}";
    assert!(Session::new(source.as_bytes().to_vec()).verify().is_ok());
    let mut parsed = ril_syntax::parse(source);
    let mut shared = None;
    for statement in &mut parsed.program.statements {
        let StmtKind::Function(function) = &mut statement.kind else {
            panic!()
        };
        let StmtKind::Binding(binding) = &mut function.body.as_mut().unwrap().statements[0].kind
        else {
            panic!()
        };
        binding.value.span = *shared.get_or_insert(binding.value.span);
    }
    let result = Session::new(source.as_bytes().to_vec()).verify_program(&parsed.program);
    assert!(
        matches!(result, Err(CompilationOutcome::NotImplemented { .. })),
        "a cross-owner numeric collision received a semantic certificate"
    );
}

#[test]
fn a_composite_expression_context_cannot_select_an_unrelated_literal_type() {
    let source = "fn example(){let narrow:f32=1.0+16777216.0;let ordinary=16777217.0}";
    assert!(Session::new(source.as_bytes().to_vec()).verify().is_ok());
    let mut parsed = ril_syntax::parse(source);
    let StmtKind::Function(function) = &mut parsed.program.statements[0].kind else {
        panic!()
    };
    let statements = &mut function.body.as_mut().unwrap().statements;
    let StmtKind::Binding(narrow) = &statements[0].kind else {
        panic!()
    };
    let shared = narrow.value.span;
    let StmtKind::Binding(ordinary) = &mut statements[1].kind else {
        panic!()
    };
    ordinary.value.span = shared;
    let result = Session::new(source.as_bytes().to_vec()).verify_program(&parsed.program);
    assert!(
        matches!(result, Err(CompilationOutcome::NotImplemented { .. })),
        "a composite-expression collision received a semantic certificate"
    );
}
