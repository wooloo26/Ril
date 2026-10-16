use ril_compiler::sema::{copy_contract::CopyInvocationStatus, model::Callable};
use ril_compiler::{CompilationOutcome, Session};
use std::collections::{BTreeMap, BTreeSet};

fn accepted(source: &str) -> ril_compiler::hir::VerifiedProgram {
    Session::new(source.as_bytes().to_vec())
        .verify()
        .unwrap_or_else(|outcome| panic!("{source}: {outcome:?}"))
}

#[test]
fn escaped_closure_objects_keep_the_creation_and_each_actual_call_identity() {
    let program = accepted(
        "type Reader=fn()->int &closure\nfn make(value:int)->Reader &capture{\\->value}\nfn example(){let seven=make(7);let nine=make(9);assert(seven()==7&&seven()==7&&nine()==9)}",
    );
    let facts = program.facts();
    let mut objects = BTreeMap::new();
    for call in &facts.closure_invocations {
        if call.probe {
            continue;
        }
        assert_eq!(call.status, CopyInvocationStatus::Completed);
        let closure = &facts.closures[call.closure];
        assert!(closure.creation_invocation.is_some());
        assert_ne!(closure.creation_invocation, call.parent_named);
        objects
            .entry(call.closure)
            .or_insert_with(Vec::new)
            .push(call.id);
        assert!(facts.invocation_expressions.iter().any(|observation| {
            observation.context.closure_invocation == Some(call.id)
                && observation.context.closure == Some(call.closure)
        }));
    }
    assert_eq!(objects.len(), 2);
    assert_eq!(objects.values().map(Vec::len).sum::<usize>(), 3);
    let sites: BTreeSet<_> = objects.keys().map(|id| facts.closures[*id].site).collect();
    assert_eq!(sites.len(), 1);
    let creation: BTreeSet<_> = objects
        .keys()
        .map(|id| facts.closures[*id].creation_invocation)
        .collect();
    assert_eq!(creation.len(), 2);
}

#[test]
fn a_closure_created_after_its_factory_return_keeps_its_dynamic_closure_parent() {
    let program = accepted(
        "type Reader=fn()->int &closure\ntype Maker=fn()->Reader &capture &closure\nfn make(value:int)->Maker &capture{\\->(\\->value)}\nfn example(){let factory=make(7);let first=factory();let second=factory();assert(first()==7&&second()==7)}",
    );
    let facts = program.facts();
    let children: Vec<_> = facts
        .closure_invocations
        .iter()
        .filter(|call| !call.probe && facts.closures[call.closure].creation_closure.is_some())
        .collect();
    assert_eq!(children.len(), 2);
    let parents: BTreeSet<_> = children
        .iter()
        .map(|call| facts.closures[call.closure].creation_closure.unwrap())
        .collect();
    assert_eq!(parents.len(), 2);
    let parent_objects: BTreeSet<_> = parents
        .iter()
        .map(|parent| facts.closure_invocations[parent.0 as usize].closure)
        .collect();
    assert_eq!(parent_objects.len(), 1);
}

#[test]
fn generic_reader_alias_keeps_qualified_results_and_actual_creation_instances() {
    let source =
        include_str!("../../ril-cli/tests/fixtures/generic_closures/retained_instances.ril");
    let program = accepted(source);
    let facts = program.facts();
    let mut created = BTreeSet::new();
    for call in facts.closure_invocations.iter().filter(|call| !call.probe) {
        assert_eq!(call.status, CopyInvocationStatus::Completed);
        let closure = &facts.closures[call.closure];
        created.insert(closure.creation_invocation.unwrap());
        assert!(facts.invocation_expressions.iter().filter(|fact|fact.context.closure_invocation==Some(call.id)).any(|observation|facts.expressions[observation.expression].value.callables.iter().any(|target|matches!(target,Callable::Builtin(name) if facts.operations.contains_key(name)))));
    }
    assert_eq!(created.len(), 3);
}

#[test]
fn generic_callable_qualifications_cannot_erase_mode_or_environment_requirements() {
    for (source, code) in [
        (
            "type Edit<T>=fn(mut T)->() &mut\ntype Cell={mut value:int}\nfn bad()->Edit<Cell>{\\cell:Cell->()}",
            "E0407",
        ),
        (
            "eff Read<T>{get()->T}\ntype Reader<T>=fn()->T &closure\nfn make<T>(value:T)->Reader<T> &capture{with Read<T>::get()->resume value;\\->Read<T>::get()}\nfn consume(action:Reader<int>)->int &{}{action()}\nfn example(){let action=make(7);let answer=consume(action)}",
            "E0534",
        ),
        (
            "eff Read<T>{get()->T}\ntype Reader<T>=fn()->T &closure\nfn make<T>(value:T)->Reader<T> &capture{with Read<T>::get()->resume value;\\->Read<T>::get()}\ntype Cell={mut value:int}\nfn example(){let mut cell=Cell.{value:1};let reader=make(cell);cell.value=2}",
            "E0535",
        ),
    ] {
        let outcome = Session::new(source.as_bytes().to_vec()).check();
        assert!(
            matches!(outcome,CompilationOutcome::Rejected{ref diagnostics} if diagnostics.iter().any(|diagnostic|diagnostic.code==code)),
            "{source}: {outcome:?}"
        );
    }
    accepted(
        "eff Read<T>{get()->T}\ntype Reader<T>=fn()->T &closure\nfn make<T>(value:T)->Reader<T> &capture{with Read<T>::get()->resume value;\\->Read<T>::get()}\ntype Cell={mut value:int}\nfn example(){let mut cell=Cell.{value:1};let view reader=make(cell);let view observed=reader();cell.value=2;assert(observed.value==2)}",
    );
}

#[test]
fn latent_handler_and_helper_captures_preserve_scalar_storage_cells() {
    for helper in [false, true] {
        let read = if helper { "fetch()" } else { "count" };
        let declarations = if helper {
            " where fn fetch()->int &{closure, count}{count}"
        } else {
            ""
        };
        let source = |reception: &str, copy: &str| {
            format!(
                "eff Read{{get()->int}}\nfn example(){{var count=1;with Read::get()->resume {read};{reception} first=\\->Read::get();let view second=\\->Read::get();count=2;assert(first()==2&&second()==2);{copy}{declarations}}}"
            )
        };
        let program = accepted(&source("let view", ""));
        let facts = program.facts();
        let cell = facts
            .bindings
            .iter()
            .find(|binding| binding.name == "count")
            .and_then(|binding| binding.cell)
            .unwrap();
        let retained: Vec<_> = facts
            .retained_handlers
            .iter()
            .filter_map(|proof| {
                if let Callable::Closure(id) = proof.callable {
                    Some(id)
                } else {
                    None
                }
            })
            .collect();
        assert_eq!(retained.len(), 2);
        for id in retained {
            assert!(
                facts
                    .heap
                    .reachable([facts.closures[id].node])
                    .contains(&cell),
                "retained capture graph lost the scalar cell"
            );
        }
        for (source, code) in [
            (source("let", ""), "E0535"),
            (source("let view", "let copied=clone(first);"), "E0530"),
            (
                source("let view", "let copied=clone_immut(first);"),
                "E0530",
            ),
        ] {
            let outcome = Session::new(source.as_bytes().to_vec()).check();
            assert!(
                matches!(outcome,CompilationOutcome::Rejected{ref diagnostics} if diagnostics.iter().any(|diagnostic|diagnostic.code==code)),
                "{source}: {outcome:?}"
            );
        }
    }
}

#[test]
fn a_nonpositive_budget_marks_action_coverage_without_claiming_runtime_entry() {
    let program = accepted(include_str!(
        "../../ril-cli/tests/fixtures/generic_closures/nested_and_budget.ril"
    ));
    let facts = program.facts();
    let validations: Vec<_> = facts
        .closure_invocations
        .iter()
        .filter(|call| call.budget_validation)
        .collect();
    assert!(!validations.is_empty());
    for call in validations {
        assert_eq!(call.status, CopyInvocationStatus::Completed);
        assert!(
            facts
                .invocation_expressions
                .iter()
                .filter(|observation| observation.context.closure_invocation == Some(call.id))
                .all(|observation| observation.context.budget_validation)
        );
        assert!(
            facts
                .closure_invocations
                .iter()
                .any(|ordinary| ordinary.closure == call.closure && !ordinary.budget_validation)
        );
    }
}

#[test]
fn latent_handler_writes_need_a_writable_callable_handle_and_results_still_need_inspection() {
    let mutable = "eff Read{get()->int}\nfn example(){var count=0;with Read::get()->{count+=1;resume count};let view action=\\->Read::get();assert(action()==1)}";
    let outcome = Session::new(mutable.as_bytes().to_vec()).check();
    assert!(
        matches!(outcome,CompilationOutcome::Rejected{ref diagnostics} if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0520")),
        "{outcome:?}"
    );
    accepted(&mutable.replace("let view action", "let mut action"));
    let prefix = "eff Read<T>{get()->T}\ntype Reader<T>=fn()->T &closure\nfn make()->Reader<Result<int,str>> &capture{with Read<int>::get()->resume 7;\\->Ok(Read<int>::get())}\n";
    let outcome = Session::new(
        format!("{prefix}fn example(){{let action=make();let ignored=action()}}").into_bytes(),
    )
    .check();
    assert!(
        matches!(outcome,CompilationOutcome::Rejected{ref diagnostics} if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0720")),
        "{outcome:?}"
    );
    accepted(&format!(
        "{prefix}fn example(){{let action=make();assert(action() is Ok(7))}}"
    ));
}
