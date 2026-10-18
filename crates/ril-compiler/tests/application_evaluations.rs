//! Real Source applications calibrate prefix replay before adversarial edits.
//! These structural tests do not replace the bundle's native trace assertions.
use ril_compiler::hir::application::ApplicationKind;
use ril_compiler::sema::{
    SemanticFacts,
    copy_contract::{CopyCallEvent, CopyCallEventId},
    default_uses::{
        ApplicationEvaluation, ArgumentSource, CallArguments, DefaultOrigin, EvaluationRole,
    },
    model::Ty,
    validate::solved_facts,
};
use ril_compiler::{CheckOptions, CompilationOutcome, Session};
use ril_compiler_core::ids::CallableOwner;
use std::collections::BTreeMap;

fn source(name: &str) -> &'static str {
    ril_test::case_source(&format!(
        "tests/regressions/evaluation-identity.ril::{name}"
    ))
}

fn verified(name: &str, layout: &str) -> SemanticFacts {
    let program = Session::with_options(
        source(name).as_bytes().to_vec(),
        CheckOptions {
            target: layout.into(),
            ..Default::default()
        },
    )
    .verify()
    .unwrap_or_else(|outcome| panic!("{name} {layout}: {outcome:?}"));
    solved_facts(program.facts()).unwrap();
    ril_compiler::lower::lower_core(&program).unwrap();
    program.facts().clone()
}

fn preparation(facts: &SemanticFacts, event: CopyCallEventId) -> &CallArguments {
    let rows: Vec<_> = facts
        .call_arguments
        .iter()
        .filter(|row| row.source_event == event)
        .collect();
    assert_eq!(rows.len(), 1, "{event:?} has no unique real preparation");
    rows[0]
}

fn preparation_mut(facts: &mut SemanticFacts, event: CopyCallEventId) -> &mut CallArguments {
    facts
        .call_arguments
        .iter_mut()
        .find(|row| row.source_event == event)
        .unwrap()
}

fn outer_events<'a>(facts: &'a SemanticFacts, owner: &str) -> Vec<&'a CopyCallEvent> {
    let owners: Vec<_> = facts
        .functions
        .iter()
        .filter(|function| function.syntax.name == owner)
        .map(|function| CallableOwner::Function(function.definition))
        .collect();
    assert!(!owners.is_empty(), "missing actual function {owner}");
    let hir = facts.semantic_hir.as_ref().unwrap();
    let events: Vec<_> = facts
        .copy_call_events
        .iter()
        .filter(|event| {
            if !event.owner.is_some_and(|owner| owners.contains(&owner)) {
                return false;
            }
            let Some(id) = event.source_id else {
                return false;
            };
            let Some(application) = hir.application(id).unwrap() else {
                return false;
            };
            application.kind == ApplicationKind::Pipeline
                || matches!(
                    &hir.expression(application.callee).unwrap().kind,
                    ril_compiler::hir::nodes::ExprKind::Block(_)
                )
        })
        .collect();
    assert!(!events.is_empty(), "no actual outer application in {owner}");
    events
}

fn rejects(facts: &SemanticFacts, change: &str) {
    assert!(
        solved_facts(facts).is_err(),
        "independent replay authorized {change}"
    );
}

#[test]
fn historical_operands_keep_their_allocation_epoch_and_require_explicit_transport() {
    let facts = verified("application-loop-computed-callee-fixed-empty", "pointer64");
    let mut saw_later_transport = false;
    for invocation in &facts.copy_invocations {
        let Some(event) = invocation.source_event else {
            continue;
        };
        let row = preparation(&facts, event);
        for (&slot, token) in &row.supplied {
            let Some((_, argument)) = invocation.arguments.get(slot as usize) else {
                continue;
            };
            let observation = &facts.expressions[token.expression];
            assert_eq!(observation.allocation_epoch, token.allocation_epoch);
            let original = observation.value.clone();
            let entry = observation
                .value_at(invocation.entry_allocation_epoch, &facts.allocation_history)
                .unwrap();
            assert_eq!(entry.origins, argument.value.origins);
            let current = observation
                .value_at(facts.allocation_history.len(), &facts.allocation_history)
                .unwrap();
            saw_later_transport |= current.origins != original.origins;
            assert_eq!(
                observation.value, original,
                "querying a later view rewrote the original observation"
            );
        }
    }
    assert!(
        saw_later_transport,
        "the real loop must allocate a newer instance of an earlier site"
    );
    let event = facts
        .copy_invocations
        .iter()
        .find_map(|invocation| {
            invocation
                .source_event
                .filter(|event| !preparation(&facts, *event).supplied.is_empty())
        })
        .unwrap();
    let index = preparation(&facts, event)
        .supplied
        .values()
        .next()
        .unwrap()
        .expression;
    let mut changed = facts.clone();
    changed.expressions[index].allocation_epoch = facts.allocation_history.len() + 1;
    rejects(
        &changed,
        "historical observation claimed an allocation epoch outside its history",
    );
}

#[test]
fn ordinary_and_pipeline_prefixes_follow_their_real_hir_children() {
    for layout in ["pointer32", "pointer64"] {
        let facts = verified("application-ordinary-complete-order", layout);
        for (owner, expected) in [
            (
                "test_ordinary_order",
                vec![
                    EvaluationRole::Callee,
                    EvaluationRole::Written(0),
                    EvaluationRole::Written(1),
                ],
            ),
            (
                "test_pipeline_order",
                vec![
                    EvaluationRole::Piped,
                    EvaluationRole::Written(0),
                    EvaluationRole::Callee,
                ],
            ),
        ] {
            for event in outer_events(&facts, owner) {
                let row = preparation(&facts, event.id);
                assert!(row.slots_bound && row.evaluation_complete);
                assert_eq!(
                    row.evaluated
                        .iter()
                        .map(|step| step.role)
                        .collect::<Vec<_>>(),
                    expected
                );
                let app = facts
                    .semantic_hir
                    .as_ref()
                    .unwrap()
                    .application(event.source_id.unwrap())
                    .unwrap()
                    .unwrap();
                assert_eq!(
                    row.evaluated
                        .iter()
                        .map(|step| step.role)
                        .collect::<Vec<_>>(),
                    app.evaluation_order().collect::<Vec<_>>()
                );
                let mut previous = None;
                for step in &row.evaluated {
                    assert_eq!(
                        facts.expressions[step.observation.expression].source_id,
                        app.expression(step.role)
                    );
                    if let Some(previous) = previous {
                        assert!(previous < step.observation.expression);
                    }
                    previous = Some(step.observation.expression);
                }
                let callee = row
                    .evaluated
                    .iter()
                    .find(|step| step.role == EvaluationRole::Callee)
                    .unwrap();
                assert_eq!(event.callee_expression, Some(callee.observation.expression));
            }
        }
    }
}

#[test]
fn never_stops_at_the_actual_prefix_without_binding_or_emitting_later_operands() {
    let facts = verified("application-pipeline-left-never", "pointer64");
    for (owner, roles, has_callee) in [
        ("ordinary_callee_stop", vec![EvaluationRole::Callee], true),
        (
            "ordinary_first_stop",
            vec![EvaluationRole::Callee, EvaluationRole::Written(0)],
            true,
        ),
        (
            "ordinary_last_stop",
            vec![
                EvaluationRole::Callee,
                EvaluationRole::Written(0),
                EvaluationRole::Written(1),
            ],
            true,
        ),
        ("pipeline_left_stop", vec![EvaluationRole::Piped], false),
        (
            "pipeline_written_stop",
            vec![EvaluationRole::Piped, EvaluationRole::Written(0)],
            false,
        ),
        (
            "pipeline_callee_stop",
            vec![
                EvaluationRole::Piped,
                EvaluationRole::Written(0),
                EvaluationRole::Callee,
            ],
            true,
        ),
    ] {
        for event in outer_events(&facts, owner) {
            let row = preparation(&facts, event.id);
            assert!(!row.evaluation_complete, "{owner} forged normal completion");
            assert_eq!(
                row.evaluated
                    .iter()
                    .map(|step| step.role)
                    .collect::<Vec<_>>(),
                roles,
                "{owner}"
            );
            assert_eq!(event.callee_expression.is_some(), has_callee, "{owner}");
            let last = row.evaluated.last().unwrap();
            assert_eq!(
                facts.expressions[last.observation.expression].value.ty,
                Ty::Never,
                "{owner}"
            );
            assert_eq!(
                facts.expressions[event.result_expression.unwrap()].value.ty,
                Ty::Never,
                "{owner}"
            );
            if !has_callee || last.role == EvaluationRole::Callee {
                assert!(
                    !row.slots_bound,
                    "{owner} bound slots without a normal callee"
                );
                assert!(row.slots.is_empty() && row.supplied.is_empty(), "{owner}");
            }
        }
    }
}

#[test]
fn deleting_or_reordering_prefixes_cannot_reuse_another_physical_operand() {
    let facts = verified("application-ordinary-complete-order", "pointer64");
    for owner in ["test_ordinary_order", "test_pipeline_order"] {
        let event = outer_events(&facts, owner)[0].id;
        assert_eq!(preparation(&facts, event).evaluated.len(), 3);
        for mutation in 0..5 {
            let mut changed = facts.clone();
            let row = preparation_mut(&mut changed, event);
            match mutation {
                0 => row.evaluated.clear(),
                1 => row.evaluated.swap(0, 1),
                2 => {
                    let first = row.evaluated[0].observation;
                    row.evaluated[0].observation = row.evaluated[1].observation;
                    row.evaluated[1].observation = first;
                }
                3 => {
                    row.evaluated.remove(1);
                }
                4 => row.evaluated[0].observation.allocation_epoch = usize::MAX,
                _ => unreachable!(),
            }
            rejects(&changed, &format!("{owner} prefix mutation {mutation}"));
        }
    }
    let mut changed = facts.clone();
    changed.call_arguments.clear();
    for observation in &mut changed.invocation_expressions {
        observation.argument_of = None;
    }
    rejects(&changed, "joint argument/prefix receipt deletion");
    changed.copy_call_events.clear();
    rejects(&changed, "joint application event and prefix deletion");
}

#[test]
fn a_missing_or_abrupt_callee_cannot_gain_bound_slots_from_a_neighbor() {
    let facts = verified("application-pipeline-left-never", "pointer64");
    let abrupt = outer_events(&facts, "pipeline_left_stop")[0].id;
    let completed = outer_events(&facts, "test_pipeline_order")[0].id;
    let borrowed = preparation(&facts, completed)
        .evaluated
        .iter()
        .find(|step| step.role == EvaluationRole::Callee)
        .unwrap()
        .observation;
    assert!(
        facts.copy_call_events[abrupt.0 as usize]
            .callee_expression
            .is_none()
    );
    let mut changed = facts.clone();
    let row = preparation_mut(&mut changed, abrupt);
    row.slots_bound = true;
    row.slots = vec![ArgumentSource::Supplied];
    row.supplied = BTreeMap::from([(0, row.evaluated[0].observation)]);
    rejects(&changed, "bound slots before any normal callee evaluation");
    let mut changed = facts.clone();
    changed.copy_call_events[abrupt.0 as usize].callee_expression = Some(borrowed.expression);
    preparation_mut(&mut changed, abrupt)
        .evaluated
        .push(ApplicationEvaluation {
            role: EvaluationRole::Callee,
            observation: borrowed,
        });
    rejects(
        &changed,
        "neighbor callee restored after a Never piped input",
    );
    let mut changed = facts.clone();
    changed.copy_call_events[completed.0 as usize].callee_expression = None;
    rejects(&changed, "normal application erased its callee root");
    let mut changed = facts;
    let row = preparation_mut(&mut changed, completed);
    row.slots_bound = false;
    row.slots.clear();
    row.supplied.clear();
    rejects(
        &changed,
        "normal application erased bound slots while retaining complete inputs",
    );
}

#[test]
fn repeated_static_applications_keep_distinct_dynamic_prefixes_and_bound_slots() {
    let facts = verified("application-repeated-ordinary-and-pipeline", "pointer64");
    for name in ["ordinary", "piped"] {
        let definition = facts
            .functions
            .iter()
            .find(|function| function.syntax.name == name)
            .unwrap()
            .definition;
        let mut by_source = BTreeMap::new();
        for event in facts
            .copy_call_events
            .iter()
            .filter(|event| event.owner == Some(CallableOwner::Function(definition)))
        {
            if event
                .parent
                .is_some_and(|id| facts.copy_invocations[id.0 as usize].source_event.is_some())
            {
                by_source
                    .entry(event.source_id.unwrap())
                    .or_insert_with(Vec::new)
                    .push(event.id);
            }
        }
        let events = by_source
            .values()
            .find(|events| events.len() >= 2)
            .expect("two real calls must reach the same lexical application");
        let (first, second) = (events[0], events[1]);
        assert_ne!(
            facts.copy_call_events[first.0 as usize].parent,
            facts.copy_call_events[second.0 as usize].parent
        );
        let foreign = preparation(&facts, second).clone();
        let original = preparation(&facts, first);
        assert_ne!(
            original.evaluated[0].observation.expression,
            foreign.evaluated[0].observation.expression
        );
        let mut changed = facts.clone();
        let row = preparation_mut(&mut changed, first);
        row.evaluated = foreign.evaluated.clone();
        row.supplied = foreign.supplied;
        rejects(
            &changed,
            &format!("{name} reused another event's complete physical prefix and slot map"),
        );
        let mut changed = facts.clone();
        changed.copy_call_events[first.0 as usize].callee_expression =
            facts.copy_call_events[second.0 as usize].callee_expression;
        rejects(
            &changed,
            &format!("{name} borrowed another instance's callee"),
        );
    }
}

#[test]
fn written_order_and_parameter_slot_order_remain_separate_with_defaults() {
    for layout in ["pointer32", "pointer64"] {
        let facts = verified("application-pipeline-named-default", layout);
        let hir = facts.semantic_hir.as_ref().unwrap();
        let mut saw_ordinary = false;
        let mut saw_pipeline = false;
        for event in &facts.copy_call_events {
            let Some(app) = event.source_id.and_then(|id| hir.application(id).unwrap()) else {
                continue;
            };
            if !app
                .operands
                .iter()
                .any(|operand| operand.label == Some("third"))
            {
                continue;
            }
            let row = preparation(&facts, event.id);
            assert!(row.slots_bound && row.evaluation_complete);
            assert!(matches!(
                row.slots.as_slice(),
                [
                    ArgumentSource::Supplied,
                    ArgumentSource::Default(_),
                    ArgumentSource::Supplied
                ]
            ));
            let slot_zero = row.supplied[&0].expression;
            let slot_two = row.supplied[&2].expression;
            match app.kind {
                ApplicationKind::Call => {
                    saw_ordinary = true;
                    assert!(slot_two < slot_zero);
                }
                ApplicationKind::Pipeline => {
                    saw_pipeline = true;
                    assert!(slot_zero < slot_two);
                }
            }
            let ArgumentSource::Default(default) = row.slots[1] else {
                unreachable!()
            };
            let default = &facts.default_uses[default.0 as usize];
            assert!(
                default
                    .result_expression
                    .is_some_and(|root| root > slot_zero && root > slot_two)
            );
            let mut changed = facts.clone();
            let row = preparation_mut(&mut changed, event.id);
            let first = row.supplied[&0];
            let last = row.supplied[&2];
            row.supplied.insert(0, last);
            row.supplied.insert(2, first);
            rejects(
                &changed,
                "parameter slots exchanged without changing written source order",
            );
        }
        assert!(saw_ordinary && saw_pipeline);
    }
}

#[test]
fn pipeline_receiving_never_upgrades_stored_sources_or_argument_modes() {
    for (case, code) in [
        ("application-ordinary-stored-dynamic", "E0301"),
        ("application-pipeline-stored-dynamic", "E0301"),
        ("application-ordinary-stored-inner-dimension", "E0301"),
        ("application-pipeline-stored-inner-dimension", "E0301"),
        (
            "application-ordinary-callee-cannot-strengthen-source",
            "E0301",
        ),
        (
            "application-pipeline-callee-cannot-strengthen-source",
            "E0301",
        ),
        ("application-ordinary-mut-is-not-retention", "E0406"),
        ("application-pipeline-mut-is-not-retention", "E0406"),
        ("application-ordinary-mut-requires-place", "E0410"),
        ("application-pipeline-mut-requires-place", "E0410"),
        ("application-fixed-storage-rejects-opaque-resizer", "E0301"),
    ] {
        for target in ["pointer32", "pointer64"] {
            let outcome = Session::with_options(
                source(case).as_bytes().to_vec(),
                CheckOptions {
                    target: target.into(),
                    ..Default::default()
                },
            )
            .check();
            assert!(
                matches!(&outcome,CompilationOutcome::Rejected{diagnostics}
                if diagnostics.iter().any(|diagnostic|diagnostic.code==code)),
                "{case} {target}: {outcome:?}"
            );
        }
    }
}

#[test]
fn genuine_construction_and_mutable_call_boundaries_still_reach_core() {
    for case in [
        "application-ordinary-fresh-fixed",
        "application-pipeline-fresh-fixed",
        "application-ordinary-callee-reassignment",
        "application-pipeline-callee-reassignment",
        "application-pipeline-temporary-mut",
        "application-ordinary-explicit-retention",
        "application-fixed-storage-keeps-mutable-elements",
    ] {
        for layout in ["pointer32", "pointer64"] {
            verified(case, layout);
        }
    }
}

#[test]
fn invalid_argument_binding_never_runs_defaults_or_enters_the_body() {
    for layout in ["pointer32", "pointer64"] {
        let control = verified("application-default-binding-control", layout);
        let selected = control
            .functions
            .iter()
            .find(|function| function.syntax.name == "selected")
            .unwrap()
            .definition;
        assert!(control.default_uses.iter().any(|usage| {
            usage.target == Some(selected) && matches!(usage.origin, DefaultOrigin::Call(_))
        }));
        assert!(control.copy_invocations.iter().any(|invocation| {
            invocation.target == selected && invocation.source_event.is_some()
        }));

        for (case, code) in [
            ("application-ordinary-unknown-label-before-default", "E0339"),
            ("application-pipeline-unknown-label-before-default", "E0339"),
            (
                "application-ordinary-duplicate-label-before-default",
                "E0325",
            ),
            (
                "application-pipeline-duplicate-label-before-default",
                "E0325",
            ),
            ("application-ordinary-excess-before-default", "E0314"),
            ("application-pipeline-excess-before-default", "E0314"),
        ] {
            let options = CheckOptions {
                target: layout.into(),
                ..Default::default()
            };
            let session = Session::with_options(source(case).as_bytes().to_vec(), options);
            let outcome = session.check();
            assert!(
                matches!(&outcome, CompilationOutcome::Rejected { diagnostics }
                    if diagnostics.iter().any(|diagnostic| diagnostic.code == code)),
                "{case} {layout}: {outcome:?}"
            );
            let snapshot = session.analyze();
            let facts = snapshot
                .facts()
                .expect("rejected binding retains actual work");
            let selected = facts
                .functions
                .iter()
                .find(|function| function.syntax.name == "selected")
                .unwrap()
                .definition;
            let events: Vec<_> = facts
                .copy_call_events
                .iter()
                .filter(|event| event.target == Some(selected))
                .collect();
            assert!(
                !events.is_empty(),
                "{case}: no real application was observed"
            );
            for event in events {
                let arguments = preparation(facts, event.id);
                assert!(
                    !arguments.slots_bound,
                    "{case}: invalid binding was accepted"
                );
                assert!(arguments.slots.is_empty() && arguments.supplied.is_empty());
                assert!(!arguments.evaluation_complete);
                assert!(
                    !facts
                        .default_uses
                        .iter()
                        .any(|usage| { usage.origin == DefaultOrigin::Call(event.id) }),
                    "{case}: an invalid binding evaluated its default"
                );
                assert!(
                    !facts
                        .copy_invocations
                        .iter()
                        .any(|invocation| { invocation.source_event == Some(event.id) }),
                    "{case}: an invalid binding entered its body"
                );
            }
        }
    }
}

#[test]
fn same_context_loop_iterations_cannot_exchange_their_physical_application_roots() {
    for layout in ["pointer32", "pointer64"] {
        let facts = verified("application-loop-computed-callee-fixed-empty", layout);
        let context = |expression| {
            let rows: Vec<_> = facts
                .invocation_expressions
                .iter()
                .filter(|row| row.expression == expression)
                .collect();
            assert_eq!(rows.len(), 1, "an actual root needs one full context");
            rows[0].context
        };
        let mut by_source = BTreeMap::new();
        for event in outer_events(&facts, "test_native") {
            by_source
                .entry(event.source_id.unwrap())
                .or_insert_with(Vec::new)
                .push(event);
        }
        assert_eq!(by_source.len(), 2, "ordinary and pipeline lexical sites");
        for events in by_source.values() {
            let (first, second) = events
                .iter()
                .enumerate()
                .find_map(|(index, first)| {
                    events[index + 1..].iter().find_map(|second| {
                        (first.parent == second.parent
                            && context(first.result_expression.unwrap())
                                == context(second.result_expression.unwrap()))
                        .then_some((*first, *second))
                    })
                })
                .expect("a real loop must repeat within the same complete invocation context");
            assert_eq!(first.source_id, second.source_id);
            assert_eq!(first.parent, second.parent);
            let shared_context = context(first.result_expression.unwrap());
            assert_eq!(shared_context, context(second.result_expression.unwrap()));
            assert_ne!(first.result_expression, second.result_expression);
            let original = preparation(&facts, first.id);
            let foreign = preparation(&facts, second.id);
            assert!(original.slots_bound && original.evaluation_complete);
            assert!(foreign.slots_bound && foreign.evaluation_complete);
            assert_eq!(original.evaluated.len(), 2);
            assert_eq!(foreign.evaluated.len(), 2);
            for (left, right) in original.evaluated.iter().zip(&foreign.evaluated) {
                assert_eq!(left.role, right.role);
                assert_ne!(left.observation.expression, right.observation.expression);
                assert_eq!(context(left.observation.expression), shared_context);
                assert_eq!(context(right.observation.expression), shared_context);
            }
            assert_eq!(original.supplied.len(), 1);
            assert_eq!(foreign.supplied.len(), 1);
            assert_ne!(
                original.supplied[&0].expression,
                foreign.supplied[&0].expression
            );

            let mut changed = facts.clone();
            changed.copy_call_events[first.id.0 as usize].callee_expression =
                second.callee_expression;
            rejects(&changed, "same-context neighbor loop callee root");

            let mut changed = facts.clone();
            changed.copy_call_events[first.id.0 as usize].result_expression =
                second.result_expression;
            rejects(
                &changed,
                "same-context neighbor loop application result root",
            );

            let mut changed = facts.clone();
            let row = preparation_mut(&mut changed, first.id);
            let argument = row
                .evaluated
                .iter_mut()
                .find(|step| step.role != EvaluationRole::Callee)
                .unwrap();
            argument.observation = foreign.supplied[&0];
            row.supplied.insert(0, foreign.supplied[&0]);
            rejects(
                &changed,
                "same-context neighbor loop argument root and slot",
            );

            let mut changed = facts.clone();
            let row = preparation_mut(&mut changed, first.id);
            row.evaluated = foreign.evaluated.clone();
            row.supplied = foreign.supplied.clone();
            changed.copy_call_events[first.id.0 as usize].callee_expression =
                second.callee_expression;
            rejects(
                &changed,
                "same-context neighbor loop complete physical prefix",
            );
        }
    }
}
