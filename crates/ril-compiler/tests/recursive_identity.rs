use ril_compiler::{CompilationOutcome, Session};
use ril_syntax::ast::{Program, StmtKind};

fn collide_function_spans(source: &str) -> Program {
    let mut parsed = ril_syntax::parse(source);
    assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
    let mut shared = None;
    for statement in &mut parsed.program.statements {
        if let StmtKind::Function(function) = &mut statement.kind
            && matches!(function.name.as_str(), "recur" | "fresh")
        {
            function.span = *shared.get_or_insert(function.span);
        }
    }
    parsed.program
}

#[test]
fn recursive_readonly_return_cannot_borrow_another_declarations_clone_authority() {
    let source = r#"
type Cell={mut value:int}
fn recur(depth:int,value:Cell)->Cell{if depth==0{value}else{recur(depth-1,value)}}
fn fresh(depth:int,value:Cell)->Cell{clone(value)}
fn example(){let original=Cell.{value:1};let mut copied=recur(1,original);copied.value=9;assert(original.value==1)}
"#;
    for program in [
        ril_syntax::parse(source).program,
        collide_function_spans(source),
    ] {
        let result = Session::new(source.as_bytes().to_vec()).verify_program(&program);
        assert!(
            matches!(&result, Err(CompilationOutcome::Rejected { diagnostics })
                if diagnostics.iter().any(|diagnostic| matches!(diagnostic.code.as_str(), "E0520" | "E0528"))),
            "{result:?}"
        );
    }
}

#[test]
fn unproductive_recursive_cycle_cannot_borrow_another_declarations_scalar_return() {
    let source = "fn recur()->int{recur()}\nfn fresh()->int{7}\nfn example(){assert(recur()==7)}";
    for program in [
        ril_syntax::parse(source).program,
        collide_function_spans(source),
    ] {
        let result = Session::new(source.as_bytes().to_vec()).verify_program(&program);
        assert!(
            matches!(&result, Err(CompilationOutcome::NotImplemented { reason })
                if reason.detail.contains("recursive dependency has no established normal-return")),
            "{result:?}"
        );
    }
}

#[test]
fn recursive_local_callable_alias_cannot_borrow_a_shadowed_clone_contract() {
    let source = r#"
type Cell={mut value:int}
fn fresh(depth:int,value:Cell)->Cell{clone(value)}
fn recur(depth:int,value:Cell)->Cell{let fresh=recur;if depth==0{value}else{fresh(depth-1,value)}}
fn example(){let original=Cell.{value:1};let mut copied=recur(1,original);copied.value=9}
"#;
    let result = Session::new(source.as_bytes().to_vec()).verify();
    assert!(
        matches!(&result, Err(CompilationOutcome::NotImplemented { reason })
            if reason.detail.contains("shadowing local callable")),
        "{result:?}"
    );
}

#[test]
fn same_span_declarations_keep_independent_proven_recursive_and_clone_returns() {
    let source = r#"
type Cell={mut value:int}
fn recur(depth:int,value:Cell)->Cell{if depth==0{value}else{recur(depth-1,value)}}
fn fresh(depth:int,value:Cell)->Cell{clone(value)}
fn example(){let original=Cell.{value:1};let value=recur(1,original);assert(value.value==1);let mut copied=fresh(1,original);copied.value=9;assert(original.value==1)}
"#;
    let verified = Session::new(source.as_bytes().to_vec())
        .verify_program(&collide_function_spans(source))
        .unwrap();
    let functions = &verified.facts().functions;
    let recur = functions
        .iter()
        .find(|function| function.syntax.name == "recur")
        .unwrap();
    let fresh = functions
        .iter()
        .find(|function| function.syntax.name == "fresh")
        .unwrap();
    assert_ne!(recur.definition, fresh.definition);
    let summaries = &verified.facts().recursive_summaries.summaries;
    assert!(summaries[&recur.definition].complete);
    assert!(summaries[&fresh.definition].complete);
    assert_ne!(
        summaries[&recur.definition].return_value,
        summaries[&fresh.definition].return_value
    );
}
