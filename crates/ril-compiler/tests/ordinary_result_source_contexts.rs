//! Result contexts choose only producing Type leaves, never source dimensions.
use ril_compiler::sema::{SemanticFacts, validate::solved_facts};
use ril_compiler::{CheckOptions, CompilationOutcome, Session};

fn checked(source: &str) -> SemanticFacts {
    let mut facts = None;
    for target in ["pointer32", "pointer64"] {
        let program = Session::with_options(
            source.as_bytes().to_vec(),
            CheckOptions {
                target: target.into(),
                ..Default::default()
            },
        )
        .verify()
        .unwrap_or_else(|outcome| panic!("{source}\n{outcome:?}"));
        solved_facts(program.facts()).unwrap();
        ril_compiler::lower::lower_core(&program).unwrap();
        facts = Some(program.facts().clone());
    }
    facts.unwrap()
}

#[test]
fn independent_result_contexts_preserve_the_declared_array_shell() {
    for source in [
        "fn empty<T>()->[]T{[]}\nfn example(){let first:[]int=empty();let second:[]str=empty()}",
        "fn empty<T>()->[]T{[]}\nfn example<T,U>(){let first:[]T=empty();let second:[]U=empty()}",
        "fn empty_pair<T>()->([]T,[]T){([],[])}\nfn example(){let pair:([]int,[]int)=empty_pair()}",
        "fn empty<T>()->[]T{[]}\nfn example(){let pair:([]int,[]str)=(empty(),empty())}",
        "fn empty<T>()->[]T{[]}\nfn example(){let optional:?[]int=Some(empty());let result:Result<[]str,str>=Ok(empty());assert(result is Ok(_))}",
        "fn empty<T>()->[]T{[]}\nfn take(values:[]int){}\nfn example(){take(empty())}",
    ] {
        checked(source);
    }
}

#[test]
fn contextual_type_selection_does_not_upgrade_a_returned_dynamic_shell() {
    for source in [
        "fn empty<T>()->[]T{[]}\nfn example(){let fixed:[0]int=empty()}",
        "fn pair<T>()->([]T,[]T){([],[])}\nfn example(){let fixed:([0]int,[]int)=pair()}",
        "fn empty<T>()->[]T{[]}\nfn example(){let fixed:?[0]int=Some(empty())}",
        "fn empty<T>()->[]T{[]}\nfn example(){let fixed:Result<[0]int,str>=Ok(empty());assert(fixed is Ok(_))}",
    ] {
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        assert!(
            matches!(&outcome,CompilationOutcome::Rejected {diagnostics}
            if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0301")),
            "{source}\n{outcome:?}"
        );
    }
}

#[test]
fn lambda_input_coordinates_do_not_require_an_unwritten_return_annotation() {
    for source in [
        "fn example(){let step=\\n:int->n+1;assert(step(1)==2)}",
        "fn example(value:?(fn()->int))->int{(value ?? (\\->{return 1}))()}",
        "fn example(){let outer=\\n:int->{let inner=\\value:int->value+1;inner(n)};assert(outer(1)==2)}",
        "type Cell={mut value:int}\nfn example(){let mut cell=Cell.{value:0};let retain=\\^mut value:Cell->value;let mut result=retain(^mut cell);result.value+=1;cell.value+=1}",
        "var count=0\nfn advance()&{mut count}{count+=1}\nfn invoke(action:fn()->()){action()}\nfn example()&{mut count}{invoke(advance)}",
    ] {
        checked(source);
    }
}

#[test]
fn deleting_a_producing_meta_resolution_cannot_erase_its_source_obligation() {
    let facts = checked(
        "fn empty<T>()->[]T{[]}\nfn example(){let first:[]int=empty();let second:[]str=empty()}",
    );
    let mut changed = facts.clone();
    let index = changed
        .inference_resolutions
        .iter()
        .position(|row| {
            row.binder.contains(":invocation:")
                && matches!(row.selected, ril_compiler::sema::model::Ty::Int(_))
        })
        .unwrap();
    changed.inference_resolutions.remove(index);
    assert!(solved_facts(&changed).is_err());
}

#[test]
fn an_unrecorded_pipeline_cannot_authorize_sensitive_public_inputs() {
    let source =
        "fn run(callback:fn([2]int)->int,values:[]int)->int{values |> callback}\nfn example(){}";
    let outcome = Session::new(source.as_bytes().to_vec()).check();
    assert!(
        matches!(outcome, CompilationOutcome::NotImplemented { .. }),
        "{source}\n{outcome:?}"
    );
}

#[test]
fn result_carriers_keep_the_actual_open_payload_and_context_only_the_absent_branch() {
    checked("fn wrapped<R>(item:{..R})->Result<{..R},str>{Ok(item)}\nfn example(){let result=wrapped(.{item:1});assert(result is Ok(_))}");
    checked("fn wrapped<R>(item:{..R})->Result<str,{..R}>{Err(item)}\nfn example(){let result=wrapped(.{item:1});assert(result is Err(_))}");
    for source in [
        "fn wrapped(item:[0][3]int)->Result<[0][2]int,str>{Ok(item)}",
        "fn wrapped(item:[0][3]int)->Result<str,[0][2]int>{Err(item)}",
    ] {
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        assert!(matches!(&outcome, CompilationOutcome::Rejected { diagnostics }
            if diagnostics.iter().any(|diagnostic| diagnostic.code == "E0301")), "{source}\n{outcome:?}");
    }
}
