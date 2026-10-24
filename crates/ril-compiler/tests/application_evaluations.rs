//! Real Source applications calibrate prefix replay before adversarial edits.
//! These structural tests do not replace the bundle's native trace assertions.
use ril_compiler::hir::application::ApplicationKind;
use ril_compiler::sema::{
    SemanticFacts,
    copy_contract::{CopyCallEvent, CopyCallEventId},
    default_uses::{CallArguments, DefaultOrigin, EvaluationRole},
    model::Ty,
};
use ril_compiler::{CheckOptions, CompilationOutcome, Session};
use ril_compiler_core::ids::CallableOwner;

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
                    EvaluationRole::Callee,
                    EvaluationRole::Written(0),
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
            vec![
                EvaluationRole::Piped,
                EvaluationRole::Callee,
                EvaluationRole::Written(0),
            ],
            true,
        ),
        (
            "pipeline_callee_stop",
            vec![EvaluationRole::Piped, EvaluationRole::Callee],
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
