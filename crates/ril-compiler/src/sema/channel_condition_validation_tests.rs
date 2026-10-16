//! Real Source/physical observations and adversarial receipt cross-links.
use super::*;

const SOME: &str = "fn example(value:Option<Result<int,str>>)->Result<(),Concurrent::TaskFault> @Async{Concurrent::scope \\mut _->{match value{Some(inner)->assert(inner is Ok(_)|Err(_)),None->()};Ok()}}";

fn verified(source: &str) -> SemanticFacts {
    let program = crate::Session::new(source.as_bytes().to_vec())
        .verify()
        .unwrap_or_else(|error| panic!("{error:?}\n{source}"));
    crate::lower::lower_core(&program).unwrap();
    program.facts().clone()
}

fn proven(facts: &SemanticFacts) -> ChannelMessageFact {
    facts
        .channel_messages
        .iter()
        .find(|event| Analysis::new(facts).truth(event).unwrap() == Some(true))
        .unwrap_or_else(|| {
            panic!(
                "no complete Source-grounded receipt: {:#?}",
                facts.channel_messages
            )
        })
        .clone()
}

#[test]
fn a_real_scalar_formal_capture_and_single_some_path_prove_complete_evaluation() {
    let facts = verified(SOME);
    let event = proven(&facts);
    assert!(
        event
            .guard
            .terms
            .iter()
            .flatten()
            .any(|literal| matches!(literal, GuardLiteral::Optional { present: true, .. }))
    );
    assert_eq!(Analysis::new(&facts).truth(&event).unwrap(), Some(true));
}

#[test]
fn actual_operand_context_program_graph_epoch_and_authority_cannot_be_substituted() {
    let facts = verified(SOME);
    let event = proven(&facts);
    let mut missing = facts.clone();
    missing.source_program = None;
    assert_eq!(Analysis::new(&missing).truth(&event).unwrap(), None);

    let mut changed = event.clone();
    let ChannelAction::ConditionEvaluated {
        subject_expression, ..
    } = &mut changed.action
    else {
        panic!()
    };
    *subject_expression = facts.expressions.len();
    assert_eq!(Analysis::new(&facts).truth(&changed).unwrap(), None);

    let mut changed = event.clone();
    changed.context.closure_invocation = None;
    assert_eq!(Analysis::new(&facts).truth(&changed).unwrap(), None);

    let mut changed = event.clone();
    changed.allocation_epoch = facts.allocation_history.len() + 1;
    assert_eq!(Analysis::new(&facts).truth(&changed).unwrap(), None);

    let mut changed = event.clone();
    let ChannelAction::ConditionEvaluated { subject, .. } = &mut changed.action else {
        panic!()
    };
    subject.value.construction = !subject.value.construction;
    assert_eq!(Analysis::new(&facts).truth(&changed).unwrap(), None);

    let mut changed = event.clone();
    let ChannelAction::ConditionEvaluated { subject, .. } = &mut changed.action else {
        panic!()
    };
    subject.nodes.push(crate::sema::copy_contract::CopyNode {
        origin: NodeId(0),
        fact: facts.heap.nodes[0].clone(),
        fields: vec![],
        length: None,
        fixed: false,
    });
    assert_eq!(Analysis::new(&facts).truth(&changed).unwrap(), None);
}

#[test]
fn widening_both_receipt_and_first_head_cannot_erase_source_some_definedness() {
    let mut facts = verified(SOME);
    let mut event = proven(&facts);
    for prior in &mut facts.channel_messages {
        if prior.context == event.context && matches!(prior.action, ChannelAction::TagTest { .. }) {
            prior.guard = ChannelGuard::always();
        }
    }
    event.guard = ChannelGuard::always();
    assert_eq!(Analysis::new(&facts).truth(&event).unwrap(), None);
}

#[test]
fn unknown_prefix_and_nonfirst_operand_cannot_supply_truth_after_guards_are_widened() {
    for body in [
        "may_abort(flag);assert(value is Ok(_)|Err(_));Ok()",
        "let ignored=may_abort(flag);assert(value is Ok(_)|Err(_));Ok()",
        "let ignored=(may_abort(flag),value is Ok(_)|Err(_));Ok()",
    ] {
        let source = format!(
            "fn may_abort(flag:bool){{if flag{{panic(\"aborted\")}}}}\nfn example(flag:bool,value:Result<int,str>)->Result<(),Concurrent::TaskFault> @Async{{Concurrent::scope \\mut _->{{{body}}}}}"
        );
        let mut facts = verified(&source);
        let mut receipts = vec![];
        for event in &mut facts.channel_messages {
            if matches!(
                event.action,
                ChannelAction::TagTest { .. } | ChannelAction::ConditionEvaluated { .. }
            ) {
                event.guard = ChannelGuard::always();
            }
            if matches!(event.action, ChannelAction::ConditionEvaluated { .. }) {
                receipts.push(event.clone());
            }
        }
        assert!(!receipts.is_empty());
        for event in receipts {
            assert_eq!(Analysis::new(&facts).truth(&event).unwrap(), None);
        }
    }
}

#[test]
fn active_receipt_refines_only_its_executed_case_and_pays_no_debt() {
    use crate::sema::result_conditions::ConditionEvaluationId;
    let facts = SemanticFacts::default();
    let mut before = Case::default();
    before.custody.insert(70, Custody::Caller(ScopeId(1)));
    before.owners.insert(70, ScopeId(1));
    before.inspected.insert(71);
    before.returned.insert(72, ScopeId(1));
    before.closed.insert(ChannelAnchor::Known {
        channel: NodeId(1),
        scope: NodeId(2),
    });
    let queued = ChannelAnchor::Known {
        channel: NodeId(1),
        scope: NodeId(2),
    };
    before.custody.insert(73, Custody::Channel(queued.clone()));
    before.owners.insert(73, ScopeId(1));
    before.queues.insert(
        queued,
        vec![Packet {
            send: ChannelMessageId(5),
            producers: [73].into(),
            clock: [(None, 3)].into(),
        }],
    );
    before.clocks.insert(None, [(None, 3)].into());
    before.tasks.insert(NodeId(4), None);
    before.executed.insert(ChannelMessageId(5));
    let event = ChannelMessageFact {
        id: ChannelMessageId(0),
        source_event: None,
        repetition: None,
        sequence: 0,
        context: InvocationContext {
            invocation: None,
            owner: None,
            closure: None,
            closure_invocation: None,
            budget_validation: false,
            default_use: None,
        },
        task: None,
        activation: ScopeId(1),
        span: Span {
            file: ril_compiler_core::source::FileId(0),
            start: 0,
            end: 0,
        },
        cause: CauseId(0),
        allocation_epoch: 0,
        guard: ChannelGuard::literal(GuardLiteral::Optional {
            identity: ril_compiler_core::ids::OptionalTagId(0),
            present: true,
        }),
        action: ChannelAction::ConditionEvaluated {
            evaluation: ConditionEvaluationId(1),
            subject_expression: 0,
            subject: CopyValueSnapshot {
                value: Value::scalar(Ty::Int("int".into()), None, CauseId(0)),
                nodes: vec![],
                relations: vec![],
            },
        },
    };
    // The Source/physical premise is deliberately supplied here, after its
    // separate real-Source tests above. This is a replay state-machine model.
    let mut replay = Replay {
        cases: vec![before.clone()],
        ..Default::default()
    };
    replay
        .record(&facts, Record::Event(&event), Some(true))
        .unwrap();
    assert_eq!(replay.cases.len(), 1); // Equal full states join their guards.
    let mut after = replay.cases[0].clone();
    let guard = std::mem::take(&mut after.guard);
    assert!(after == before);
    let active_false = ChannelGuard {
        incomplete: false,
        terms: [[
            GuardLiteral::Optional {
                identity: ril_compiler_core::ids::OptionalTagId(0),
                present: true,
            },
            GuardLiteral::Boolean {
                evaluation: ConditionEvaluationId(1),
                truth: false,
            },
        ]
        .into()]
        .into(),
    }
    .normalized()
    .unwrap();
    assert!(guard.and(&active_false).unwrap().is_never());
    let inactive_false = ChannelGuard {
        incomplete: false,
        terms: [[
            GuardLiteral::Optional {
                identity: ril_compiler_core::ids::OptionalTagId(0),
                present: false,
            },
            GuardLiteral::Boolean {
                evaluation: ConditionEvaluationId(1),
                truth: false,
            },
        ]
        .into()]
        .into(),
    }
    .normalized()
    .unwrap();
    assert!(!guard.and(&inactive_false).unwrap().is_never());
}
