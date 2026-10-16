use ril_compiler::{CompilationOutcome, Session};

fn check(source: &str) -> CompilationOutcome {
    Session::new(source.as_bytes().to_vec()).check()
}

#[test]
fn returned_callable_generics_remain_local_to_each_factory_invocation() {
    let factory = "fn make<T>(value:T)->(fn()->T &closure) &capture{\\->value}\n";
    let source = format!(
        "{factory}fn example(){{let number=make(7);let text=make(\"seven\");assert(number()==7);assert(text()==\"seven\")}}"
    );
    let outcome = check(&source);
    assert!(
        matches!(outcome, CompilationOutcome::Accepted { .. }),
        "{outcome:?}"
    );
    for body in [
        "let action=make(7);let wrong:str=action()",
        "let action=make(\"seven\");let wrong:int=action()",
    ] {
        let outcome = check(&format!("{factory}fn example(){{{body}}}"));
        assert!(
            matches!(outcome, CompilationOutcome::Rejected { ref diagnostics } if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0301")),
            "{body}: {outcome:?}"
        );
    }
}

#[test]
fn returned_callable_aliases_preserve_the_permission_of_the_actual_result() {
    let factory = "type Cell={mut count:int}\ntype Read=fn()->Cell &closure\nfn make(value:Cell)->Read &capture{\\->value}\n";
    let source = format!(
        "{factory}fn example(){{let mut cell=Cell.{{count:7}};cell.count+=1;let view action=make(cell);assert(action().count==8)}}"
    );
    let outcome = check(&source);
    assert!(
        matches!(outcome, CompilationOutcome::Accepted { .. }),
        "{outcome:?}"
    );
    let outcome = check(&format!(
        "{factory}fn example(){{let mut cell=Cell.{{count:7}};cell.count+=1;let view action=make(cell);let mut alias=action();alias.count+=1}}"
    ));
    assert!(
        matches!(outcome, CompilationOutcome::Rejected { ref diagnostics } if diagnostics.iter().any(|diagnostic| matches!(diagnostic.code.as_str(), "E0520" | "E0522"))),
        "{outcome:?}"
    );
}

#[test]
fn a_callable_result_context_instantiates_every_return_contract_stage() {
    for (factory, body) in [
        (
            "fn make<T>()->fn()->?T{\\->None}\n",
            "let action:fn()->?int=make();assert(action()==None)",
        ),
        (
            "fn make<T>()->fn()->fn()->?T{\\->\\->None}\n",
            "let action:fn()->fn()->?int=make();assert(action()()==None)",
        ),
    ] {
        let outcome = check(&format!("{factory}fn example(){{{body}}}"));
        assert!(
            matches!(outcome, CompilationOutcome::Accepted { .. }),
            "{body}: {outcome:?}"
        );
    }
    let outcome = check(
        "fn make<T>()->fn()->?T{\\->None}\nfn example(){let action:fn()->?int=make();let wrong:?str=action()}",
    );
    assert!(
        matches!(outcome, CompilationOutcome::Rejected { ref diagnostics } if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0301")),
        "{outcome:?}"
    );
}
