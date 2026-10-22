//! Nominal payloads cannot replace the original operand's array coordinates.
use ril_compiler::sema::{SemanticFacts, model::Callable, validate::solved_facts};
use ril_compiler::{CheckOptions, CompilationOutcome, Session};

fn verified(source: &str, target: &str) -> SemanticFacts {
    let program = Session::with_options(
        source.as_bytes().to_vec(),
        CheckOptions {
            target: target.into(),
            ..Default::default()
        },
    )
    .verify()
    .unwrap_or_else(|outcome| panic!("{target}\n{source}\n{outcome:?}"));
    ril_compiler::lower::lower_core(&program).unwrap();
    program.facts().clone()
}

#[test]
fn stored_dynamic_and_empty_outer_dimensions_are_rejected_at_constructor_input() {
    for source in [
        "type Fixed([2]int)\nfn example(){let xs:[]int=[1,2];let wrapped=Fixed(xs)}",
        "type Fixed([0][2]int)\nfn example(){let xs:[0][3]int=[];let wrapped=Fixed(xs)}",
        "type Envelope{Item([0][2]int)}\nfn example(){let xs:[0][3]int=[];let wrapped=Envelope::Item(xs)}",
    ] {
        for layout in ["pointer32", "pointer64"] {
            let outcome = Session::with_options(
                source.as_bytes().to_vec(),
                CheckOptions {
                    target: layout.into(),
                    ..Default::default()
                },
            )
            .check();
            assert!(
                matches!(&outcome,CompilationOutcome::Rejected{diagnostics}
                if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0301")),
                "{layout}\n{source}\n{outcome:?}"
            );
        }
    }
}

#[test]
fn written_literals_fixed_values_and_both_tuple_boundaries_keep_source_coordinates() {
    for source in [
        "type Fixed([2]int)\nfn example(){let wrapped=Fixed([1,2]);let xs:[2]int=inner(wrapped)}",
        "type Fixed([2]int)\nfn example(){let xs:[2]int=[1,2];let wrapped=Fixed(xs);let returned:[2]int=inner(wrapped)}",
        "type Fixed([0][2]int)\nfn example(){let wrapped=Fixed([]);let xs:[0][2]int=inner(wrapped)}",
        "type Envelope{Item([2]int,str)}\nfn example(){let first=Envelope::Item(([1,2],\"a\"));let second=Envelope::Item([3,4],\"b\")}",
    ] {
        for layout in ["pointer32", "pointer64"] {
            verified(source, layout);
        }
    }
}

fn events(facts: &SemanticFacts) -> Vec<usize> {
    facts
        .copy_call_events
        .iter()
        .enumerate()
        .filter_map(|(index, event)| {
            let callee = facts.expressions.get(event.callee_expression?)?;
            callee
                .value
                .callables
                .iter()
                .any(|callable| matches!(callable, Callable::Constructor(_)))
                .then_some(index)
        })
        .collect()
}

#[test]
fn constructor_preparation_or_payload_metadata_deletion_does_not_remove_source_duties() {
    let facts = verified(
        "type Fixed([2]int)\nfn example(){let wrapped=Fixed([1,2])}",
        "pointer64",
    );
    assert_eq!(events(&facts).len(), 1);
    for mutation in 0..3 {
        let mut changed = facts.clone();
        match mutation {
            0 => changed.call_arguments.clear(),
            1 => changed.call_arguments[0].supplied.clear(),
            2 => {
                for constructor in changed.constructors.values_mut() {
                    constructor.payload_syntax = None;
                }
            }
            _ => unreachable!(),
        }
        assert!(
            solved_facts(&changed).is_err(),
            "mutation {mutation} was authorized"
        );
    }
}

#[test]
fn another_constructor_operand_cannot_replace_the_physical_supplied_root() {
    let mut facts = verified(
        "type Fixed([2]int)\nfn example(){let first=Fixed([1,2]);let second=Fixed([3,4])}",
        "pointer64",
    );
    let events = events(&facts);
    assert_eq!(events.len(), 2);
    let first = facts.copy_call_events[events[0]].id;
    let second = facts.copy_call_events[events[1]].id;
    let replacement = facts
        .call_arguments
        .iter()
        .find(|row| row.source_event == second)
        .unwrap()
        .supplied[&0];
    facts
        .call_arguments
        .iter_mut()
        .find(|row| row.source_event == first)
        .unwrap()
        .supplied
        .insert(0, replacement);
    assert!(solved_facts(&facts).is_err());
}

#[test]
fn repeated_literal_source_still_requires_its_own_actual_call_interval() {
    let mut facts = verified(
        "type Fixed([2]int)\nfn example(){var count=0;for [1,2] as n{let wrapped=Fixed([n,n]);count+=1};assert(count>=0)}",
        "pointer64",
    );
    let events = events(&facts);
    assert!(events.len() >= 2, "loop must provide a later actual event");
    let first = facts.copy_call_events[events[0]].id;
    let second = facts.copy_call_events[events[1]].id;
    assert_eq!(
        facts.copy_call_events[events[0]].span,
        facts.copy_call_events[events[1]].span
    );
    let replacement = facts
        .call_arguments
        .iter()
        .find(|row| row.source_event == second)
        .unwrap()
        .supplied[&0];
    facts
        .call_arguments
        .iter_mut()
        .find(|row| row.source_event == first)
        .unwrap()
        .supplied
        .insert(0, replacement);
    let row = facts
        .invocation_expressions
        .iter_mut()
        .find(|row| row.expression == replacement.expression)
        .unwrap();
    row.argument_of = Some((first, 0));
    assert!(
        solved_facts(&facts).is_err(),
        "joint root/slot retag crossed an actual call interval"
    );
}

#[test]
fn canonical_iteration_header_retains_array_coordinates_and_cannot_be_replaced() {
    let source = "fn step_value()->Iter::Step<[2]int,[0][3]int>{Iter::Step::Yielded([],[1,2])}";
    for layout in ["pointer32", "pointer64"] {
        verified(source, layout);
    }
    let mut facts = verified(source, "pointer64");
    facts
        .external_type_declarations
        .get_mut("Iter::Step")
        .unwrap()
        .variants[1]
        .payload = None;
    assert!(
        solved_facts(&facts).is_err(),
        "the canonical Step declaration was replaced"
    );
    let source = "fn step_value()->Iter::Step<int,[0][2]int>{let rows:[0][3]int=[];Iter::Step::Yielded(rows,0)}";
    for layout in ["pointer32", "pointer64"] {
        let outcome = Session::with_options(
            source.as_bytes().to_vec(),
            CheckOptions {
                target: layout.into(),
                ..Default::default()
            },
        )
        .check();
        assert!(
            matches!(&outcome,CompilationOutcome::Rejected{diagnostics}
            if diagnostics.iter().any(|diagnostic|diagnostic.code=="E0301")),
            "{layout}\n{source}\n{outcome:?}"
        );
    }
}

#[test]
fn constructor_instance_source_and_its_original_environment_cannot_be_replaced() {
    let source = "fn step_value()->Iter::Step<[2]int,[0][3]int>{Iter::Step::Yielded([],[1,2])}";
    let facts = verified(source, "pointer64");
    let event = &facts.copy_call_events[events(&facts)[0]];
    let callee = &facts.expressions[event.callee_expression.unwrap()].value;
    let [Callable::Constructor(identity)] = callee.callables.as_slice() else {
        panic!("expected one actual constructor instance")
    };
    let original = &facts.constructors[identity];
    assert!(original.source.is_some());
    assert_eq!(
        original.source.unwrap().environment,
        original.typing_environment.id()
    );
    for mutation in 0..5 {
        let mut changed = facts.clone();
        let constructor = changed.constructors.get_mut(identity).unwrap();
        match mutation {
            0 => constructor.source = None,
            1 => {
                constructor.typing_environment = constructor.typing_environment.thaw().freeze();
                assert_ne!(
                    constructor.typing_environment.id(),
                    original.typing_environment.id()
                );
            }
            2 => constructor.source_syntax = None,
            3 => {
                let written = std::sync::Arc::make_mut(constructor.source_syntax.as_mut().unwrap());
                let ril_syntax::ast::TypeKind::Name { arguments, .. } = &mut written.kind else {
                    panic!("expected a nominal instance header")
                };
                arguments.swap(0, 1);
            }
            4 => {
                constructor.source = None;
                constructor.source_syntax = None;
                constructor.source_type_witness = None;
            }
            _ => unreachable!(),
        }
        assert!(
            solved_facts(&changed).is_err(),
            "constructor source mutation {mutation} was authorized"
        );
    }
}
