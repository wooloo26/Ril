//! Shared original-corpus AST for recursive summary and descent controls.
use ril_syntax::ast::*;

pub(crate) fn program() -> Program {
    let source = ril_test::case_source(
        "tests/regressions/source-transport.ril::recursive-static-input-receipts",
    );
    let parsed = ril_syntax::parse(source);
    assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
    let mut program = parsed.program;
    identify(&mut program);
    program
}

pub(crate) fn identify(program: &mut Program) {
    crate::hir::HirProgram::lower_identified(program, crate::hir::nodes::InputOrigin::Source)
        .unwrap();
}

pub(crate) fn function_mut<'a>(program: &'a mut Program, name: &str) -> &'a mut Function {
    program
        .statements
        .iter_mut()
        .find_map(|statement| match &mut statement.kind {
            StmtKind::Function(function) if function.name == name => Some(function),
            _ => None,
        })
        .unwrap()
}

pub(crate) fn body_expression_mut(function: &mut Function) -> &mut Expr {
    let StmtKind::Expr { expression, .. } = &mut function.body.as_mut().unwrap().statements[0].kind
    else {
        panic!("corpus function has one branch expression");
    };
    expression
}

pub(crate) fn call_mut(function: &mut Function) -> &mut Expr {
    let ExprKind::If { then_branch, .. } = &mut body_expression_mut(function).kind else {
        panic!("corpus recursion is guarded");
    };
    let ExprKind::Block(block) = &mut then_branch.kind else {
        panic!("corpus recursive branch is a block");
    };
    let StmtKind::Expr { expression, .. } = &mut block.statements[0].kind else {
        panic!("corpus branch contains its original call");
    };
    assert!(matches!(expression.kind, ExprKind::Call { .. }));
    expression
}

pub(crate) fn base_case_mut(function: &mut Function) -> &mut Expr {
    let ExprKind::If { else_branch, .. } = &mut body_expression_mut(function).kind else {
        panic!("corpus recursion is guarded");
    };
    let ExprKind::Block(block) = &mut else_branch.as_mut().unwrap().kind else {
        panic!("corpus base case is a block");
    };
    let StmtKind::Expr { expression, .. } = &mut block.statements[0].kind else {
        panic!("corpus base case contains its original value");
    };
    expression
}

/// Add a default-forwarding helper to the same original recursive source. Its
/// first formal receives the caller's third port, despite the caller also
/// having a second port named `first`.
pub(crate) fn default_forwarding_program() -> Program {
    let mut program = program();
    let mut helper = program
        .statements
        .iter()
        .find(|statement| matches!(&statement.kind, StmtKind::Function(function) if function.name == "recur"))
        .unwrap()
        .clone();
    let StmtKind::Function(pick) = &mut helper.kind else {
        unreachable!();
    };
    pick.name = "pick".into();
    let mut first = pick.parameters[1].clone();
    first.pattern.kind = PatternKind::Name("first".into());
    let mut answer = first.clone();
    answer.pattern.kind = PatternKind::Name("answer".into());
    let mut default = base_case_mut(pick).clone();
    default.kind = ExprKind::Name("first".into());
    answer.default = Some(default);
    pick.parameters = vec![first.clone(), answer];
    let mut returned = base_case_mut(pick).clone();
    returned.kind = ExprKind::Name("answer".into());
    let body = pick.body.as_mut().unwrap();
    let StmtKind::Expr { expression, .. } = &mut body.statements[0].kind else {
        unreachable!();
    };
    *expression = returned;

    let recur = function_mut(&mut program, "recur");
    recur.parameters.insert(1, first);
    let call = call_mut(recur);
    let ExprKind::Call { arguments, .. } = &mut call.kind else {
        unreachable!();
    };
    let mut first_argument = arguments[1].clone();
    first_argument.value.kind = ExprKind::Name("first".into());
    arguments.insert(1, first_argument);
    let mut picked = call.clone();
    let ExprKind::Call { callee, arguments } = &mut picked.kind else {
        unreachable!();
    };
    let ExprKind::Generic { base, .. } = &mut callee.kind else {
        panic!("corpus call retains its explicit static arguments");
    };
    base.kind = ExprKind::Name("pick".into());
    let mut value = arguments[2].clone();
    value.label = Some("first".into());
    *arguments = vec![value];
    *base_case_mut(recur) = picked;
    program.statements.push(helper);
    identify(&mut program);
    program
}
