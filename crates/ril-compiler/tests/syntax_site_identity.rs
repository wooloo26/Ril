use ril_compiler::{CompilationOutcome, Session};
use ril_syntax::ast::{ExprKind, StmtKind};

const HANDLERS: &str = r#"
eff Read{get()->int}
type Reader=fn()->int &closure
fn make(value:int)->Reader &capture{
    with Read::get()->resume value
    with Read::get()->resume (Read::get())
    \->Read::get()
}
fn example(){let seven=make(7);let nine=make(9);assert(seven()==7 && nine()==9)}
"#;

#[test]
fn distinct_handlers_at_one_diagnostic_span_cannot_receive_a_certificate() {
    let mut parsed = ril_syntax::parse(HANDLERS);
    assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
    assert!(Session::new(HANDLERS.as_bytes().to_vec()).verify().is_ok());
    let function = parsed
        .program
        .statements
        .iter_mut()
        .find_map(|statement| match &mut statement.kind {
            StmtKind::Function(function) if function.name == "make" => Some(function),
            _ => None,
        })
        .unwrap();
    let handlers: Vec<_> = function
        .body
        .as_mut()
        .unwrap()
        .statements
        .iter_mut()
        .filter(|statement| matches!(statement.kind, StmtKind::Handler(_)))
        .collect();
    let shared = handlers[0].span;
    for handler in handlers {
        handler.span = shared;
    }
    let result = Session::new(vec![]).verify_program(&parsed.program);
    assert!(
        matches!(&result,Err(CompilationOutcome::NotImplemented{reason}) if reason.detail.contains("distinct lexical handler")),
        "{result:?}"
    );
}

#[test]
fn different_lambda_occurrences_at_one_span_cannot_share_a_site() {
    let source = "fn example(){let first=\\->1;let second=\\->2;assert(first()==1 && second()==2)}";
    let mut parsed = ril_syntax::parse(source);
    assert!(Session::new(source.as_bytes().to_vec()).verify().is_ok());
    let StmtKind::Function(function) = &mut parsed.program.statements[0].kind else {
        panic!()
    };
    let lambdas: Vec<_> = function
        .body
        .as_mut()
        .unwrap()
        .statements
        .iter_mut()
        .filter_map(|statement| match &mut statement.kind {
            StmtKind::Binding(binding) if matches!(binding.value.kind, ExprKind::Lambda { .. }) => {
                Some(&mut binding.value)
            }
            _ => None,
        })
        .collect();
    let shared = lambdas[0].span;
    for lambda in lambdas {
        lambda.span = shared;
    }
    let result = Session::new(vec![]).verify_program(&parsed.program);
    assert!(
        matches!(&result,Err(CompilationOutcome::NotImplemented{reason}) if reason.detail.contains("distinct lexical closure")),
        "{result:?}"
    );
}

#[test]
fn equal_spans_under_different_function_owners_remain_distinct() {
    let source = "eff Read{get()->int}\nfn first()->int{with Read::get()->resume 1;Read::get()}\nfn second()->int{with Read::get()->resume 2;Read::get()}\nfn example(){assert(first()==1 && second()==2)}";
    let mut parsed = ril_syntax::parse(source);
    let mut shared = None;
    for statement in &mut parsed.program.statements {
        if let StmtKind::Function(function) = &mut statement.kind {
            for statement in &mut function.body.as_mut().unwrap().statements {
                if matches!(statement.kind, StmtKind::Handler(_)) {
                    statement.span = *shared.get_or_insert(statement.span);
                }
            }
        }
    }
    let verified = Session::new(vec![])
        .verify_program(&parsed.program)
        .unwrap();
    let core = ril_compiler::lower::lower_core(&verified).unwrap();
    let sites: std::collections::BTreeSet<_> = core
        .provenance
        .handlers
        .iter()
        .filter_map(|handler| handler.definition)
        .collect();
    assert_eq!(sites.len(), 2);
}
