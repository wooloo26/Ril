use ril_compiler::{Session, sema::channel_messages::ChannelAction};

#[test]
fn representative_callbacks_and_loop_bodies_do_not_prove_message_cardinality() {
    let repeated = ril_test::case_source(
        "tests/regressions/channels.ril::channel-message-repeated-cardinality-gap",
    );
    let ordinary = ril_test::case_source(
        "tests/regressions/channels.ril::channel-message-loop-cardinality-gap",
    );
    for source in [repeated.to_owned(), ordinary.to_owned()] {
        match Session::new(source.as_bytes().to_vec()).check() {
            ril_compiler::CompilationOutcome::NotImplemented { reason } => assert!(
                format!("{reason:?}").contains("iteration-indexed"),
                "{reason:?}"
            ),
            other => panic!("{other:?}\n{source}"),
        }
    }
    for source in [
        repeated.replace("[1,2]", "[1]"),
        ordinary.replace("0..2", "0..1"),
    ] {
        let verified = Session::new(source.as_bytes().to_vec())
            .verify()
            .unwrap_or_else(|error| panic!("{error:?}\n{source}"));
        ril_compiler::lower::lower_core(&verified).unwrap();
    }
}

#[test]
fn scalar_only_and_empty_message_repetitions_keep_their_own_execution_regions() {
    let source = format!(
        "{}\nfn checked(number:int)->int{{number+1}}\nlet MAPPED=Array::map([1,2],checked)\nfn unrelated()->Result<(),Concurrent::TaskFault> @Async {{Concurrent::scope \\mut s -> {{let child=s.fork(\\->());let (mut tx,mut rx)=Channel::bounded<int>(2);for [1,2] as value {{assert((tx !> Channel::send(value)) is Ok());assert((rx !> Channel::recv()) is Ok(_));let local=clone(tx);Channel::close(local)}};Channel::close(tx);Channel::close(rx);child.join()}}}}",
        ril_test::case_source("tests/regressions/channels.ril::channel-formal-result")
    );
    let verified = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    assert!(!verified.facts().channel_repetitions.is_empty());
    assert!(
        verified
            .facts()
            .channel_repetitions
            .iter()
            .all(|entry| entry.end_sequence.is_some() && entry.call.is_some())
    );
    let _core = ril_compiler::lower::lower_core(&verified).unwrap();
}

#[test]
fn inline_nested_and_captured_publishers_use_the_same_actual_summary_contract() {
    for source in [
        ril_test::case_source("tests/regressions/channels.ril::channel-message-inline-control"),
        ril_test::case_source("tests/regressions/channels.ril::channel-message-nested-formal"),
        ril_test::case_source("tests/regressions/channels.ril::channel-message-captured-formal"),
        ril_test::case_source("tests/regressions/channels.ril::channel-message-same-sender"),
    ] {
        let verified = Session::new(source.as_bytes().to_vec())
            .verify()
            .unwrap_or_else(|error| panic!("{error:?}\n{source}"));
        ril_compiler::lower::lower_core(&verified).unwrap();
    }
}

#[test]
fn different_sender_tasks_do_not_borrow_the_analysis_walks_global_order() {
    let original =
        ril_test::case_source("tests/regressions/channels.ril::channel-message-two-senders");
    for source in [
        original.to_owned(),
        original.replacen(
            "Ok(value)->assert(value is Ok(_)|Err(_))",
            "Ok(value)->{let alias=value;let _=alias;}",
            1,
        ),
    ] {
        match Session::new(source.as_bytes().to_vec()).check() {
            ril_compiler::CompilationOutcome::NotImplemented { reason } => {
                assert!(format!("{reason:?}").contains("senders"), "{reason:?}")
            }
            other => panic!("{other:?}"),
        }
    }
}

#[test]
fn outer_transport_checks_and_normal_close_cannot_discard_business_debt() {
    for source in [
        ril_test::case_source(
            "tests/regressions/channels.ril::channel-message-formal-failed-send-loses-original",
        ),
        ril_test::case_source(
            "tests/regressions/channels.ril::channel-message-inline-closed-send-loses-original",
        ),
        ril_test::case_source("tests/regressions/channels.ril::channel-message-inline-outer-only"),
        ril_test::case_source(
            "tests/regressions/channels.ril::channel-message-inline-unread-close",
        ),
    ] {
        match Session::new(source.as_bytes().to_vec()).check() {
            ril_compiler::CompilationOutcome::Rejected { diagnostics, .. } => assert!(
                diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.code == "E0720"),
                "{diagnostics:?}"
            ),
            other => panic!("{other:?}\n{source}"),
        }
    }
}

#[test]
fn fallback_and_propagation_keep_success_and_failure_message_responsibilities_disjoint() {
    let fallback =
        ril_test::case_source("tests/regressions/channels.ril::channel-message-fallback");
    let question =
        ril_test::case_source("tests/regressions/channels.ril::channel-message-question-checked");
    for source in [fallback, question] {
        let verified = Session::new(source.as_bytes().to_vec())
            .verify()
            .unwrap_or_else(|error| panic!("{error:?}\n{source}"));
        ril_compiler::lower::lower_core(&verified).unwrap();
    }
    for source in [
        fallback.replace("Ok(value)->assert(value is Ok(7)|Err(_))", "Ok(_)->()"),
        fallback.replace(
            "\\error->{assert(payload is Ok(7)|Err(_));()}",
            "\\error->()",
        ),
        question
            .replace("assert(value is Ok(_)|Err(_))", "()")
            .replace("Err(_)->assert(payload is Ok(7)|Err(_))", "Err(_)->()"),
    ] {
        match Session::new(source.as_bytes().to_vec()).check() {
            ril_compiler::CompilationOutcome::Rejected { diagnostics, .. } => assert!(
                diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.code == "E0720"),
                "{diagnostics:?}"
            ),
            other => panic!("{other:?}\n{source}"),
        }
    }
}

#[test]
fn a_returned_family_tag_is_selected_by_its_actual_member_receipt() {
    let source = ril_test::case_source(
        "tests/regressions/channels.ril::channel-message-conditional-returns",
    );
    let verified = Session::new(source.as_bytes().to_vec())
        .verify()
        .unwrap_or_else(|error| panic!("{error:?}\n{source}"));
    ril_compiler::lower::lower_core(&verified).unwrap();
    let negative = source.replace("Err(_)->assert(payload is Ok(7)|Err(_))", "Err(_)->()");
    match Session::new(negative.into_bytes()).check() {
        ril_compiler::CompilationOutcome::Rejected { diagnostics, .. } => assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0720"),
            "{diagnostics:?}"
        ),
        other => panic!("{other:?}"),
    }
    let implicit = source.replace(
        "if choice {return sent}else{return Err(Channel::ChannelError::Closed)}",
        "if choice {sent}else{Err(Channel::ChannelError::Closed)}",
    );
    match Session::new(implicit.into_bytes()).check() {
        ril_compiler::CompilationOutcome::NotImplemented { reason } => {
            assert!(format!("{reason:?}").contains("one-of"), "{reason:?}")
        }
        other => panic!("{other:?}"),
    }
}

#[test]
fn a_business_error_from_scope_does_not_supply_cancellation_proof() {
    let source = ril_test::case_source(
        "tests/regressions/channels.ril::channel-message-inline-unread-close",
    )
    .replace("(mut tx,mut rx)", "(mut tx,rx)")
    .replace("Channel::close(rx)", "let _=rx")
    .replace(
        "        Ok()",
        "        Err(Concurrent::TaskFault::Panicked(\"domain\"))",
    );
    match Session::new(source.into_bytes()).check() {
        ril_compiler::CompilationOutcome::Rejected { diagnostics, .. } => assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0720"),
            "{diagnostics:?}"
        ),
        other => panic!("{other:?}"),
    }
}

#[test]
fn result_free_optional_inputs_do_not_need_business_presence_choices() {
    let source =
        ril_test::case_source("tests/regressions/channels.ril::channel-message-optional-scalar");
    let verified = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    ril_compiler::lower::lower_core(&verified).unwrap();
}

#[test]
fn formal_optional_presence_does_not_inspect_its_inner_result() {
    let source = ril_test::case_source(
        "tests/regressions/channels.ril::channel-message-formal-optional-checked",
    );
    let verified = Session::new(source.as_bytes().to_vec())
        .verify()
        .unwrap_or_else(|error| panic!("{error:?}\n{source}"));
    ril_compiler::lower::lower_core(&verified).unwrap();
    let unchecked = source.replace("Some(inner)->assert(inner is Ok(_)|Err(_))", "Some(_)->()");
    match Session::new(unchecked.as_bytes().to_vec()).check() {
        ril_compiler::CompilationOutcome::Rejected { diagnostics, .. } => assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0720"),
            "{diagnostics:?}"
        ),
        other => panic!("{other:?}\n{unchecked}"),
    }
}

#[test]
fn an_optional_clone_keeps_the_tag_bit_but_has_a_new_result_producer() {
    let source = ril_test::case_source(
        "tests/regressions/channels.ril::channel-message-formal-optional-clone-checked",
    );
    let verified = Session::new(source.as_bytes().to_vec())
        .verify()
        .unwrap_or_else(|error| panic!("{error:?}\n{source}"));
    ril_compiler::lower::lower_core(&verified).unwrap();
    let unchecked = source.replace(
        "Some(inner)->assert(inner is Ok(_)|Err(_)),\n                None->()",
        "Some(_)->(),\n                None->()",
    );
    assert_ne!(source, unchecked);
    match Session::new(unchecked.as_bytes().to_vec()).check() {
        ril_compiler::CompilationOutcome::Rejected { diagnostics, .. } => assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0720"),
            "{diagnostics:?}"
        ),
        other => panic!("{other:?}\n{unchecked}"),
    }
}

#[test]
fn formal_sender_results_keep_actual_message_events_and_lower_complete_evidence() {
    let source = ril_test::case_source("tests/regressions/channels.ril::channel-formal-result");
    let verified = Session::new(source.as_bytes().to_vec())
        .verify()
        .unwrap_or_else(|error| panic!("{error:?}"));
    if std::env::var_os("RIL_CHANNEL_TRACE").is_some() {
        for event in &verified.facts().channel_messages {
            let (kind, detail) = match &event.action {
                ChannelAction::Send {
                    anchor,
                    payload,
                    original_owners,
                    transport,
                    ..
                } => (
                    "send",
                    format!(
                        "{anchor:?} payload={:?} outer={:?} owners={original_owners:?}",
                        payload.value.results, transport.value.outer_results
                    ),
                ),
                ChannelAction::Receive {
                    anchor,
                    payload,
                    transport,
                    sources,
                    ..
                } => (
                    "recv",
                    format!(
                        "{anchor:?} payload={:?} outer={:?} sources={sources:?}",
                        payload.value.results, transport.value.outer_results
                    ),
                ),
                ChannelAction::Inspect { value, .. } => {
                    ("inspect", format!("{:?}", value.value.must_outer_results))
                }
                ChannelAction::TagTest {
                    subject, success, ..
                } => (
                    "tag",
                    format!("{:?} {success}", subject.value.outer_results),
                ),
                ChannelAction::Select { evaluation, truth } => {
                    ("select", format!("{evaluation:?} {truth}"))
                }
                ChannelAction::ConditionEvaluated {
                    evaluation,
                    subject_expression,
                    ..
                } => (
                    "condition-evaluated",
                    format!("{evaluation:?} operand={subject_expression}"),
                ),
                ChannelAction::TaskFork { child } => ("fork", format!("{child:?}")),
                ChannelAction::TaskJoin { child } => ("join", format!("{child:?}")),
                ChannelAction::ResultAliases { map } => ("aliases", format!("{map:?}")),
                ChannelAction::ResultTransfer {
                    from,
                    to,
                    producers,
                    ..
                } => ("transfer", format!("{from:?}->{to:?} {producers:?}")),
            };
            println!(
                "{} {kind} activation={:?} context={:?} task={:?} guard={:?} {detail}",
                event.sequence, event.activation, event.context, event.task, event.guard
            );
        }
        for exit in &verified.facts().channel_exits {
            println!(
                "{} exit {:?} activation={:?} context={:?} anchor={:?} returned={:?} guard={:?}",
                exit.sequence,
                exit.kind,
                exit.activation,
                exit.context,
                exit.anchor,
                exit.returned.value.results,
                exit.guard
            );
        }
        for boundary in &verified.facts().concurrent_boundaries {
            println!("boundary {boundary:?}");
        }
        for duty in &verified.facts().result_duties {
            println!("duty {duty:?}");
        }
    }
    assert!(
        verified
            .facts()
            .channel_messages
            .iter()
            .any(|fact| matches!(fact.action, ChannelAction::Send { .. }))
    );
    assert!(
        verified
            .facts()
            .channel_messages
            .iter()
            .any(|fact| matches!(fact.action, ChannelAction::Receive { .. }))
    );
    assert!(!verified.facts().channel_exits.is_empty());
    let _core = ril_compiler::lower::lower_core(&verified).unwrap();
}

#[test]
fn complete_outer_evaluation_cannot_pay_nested_or_cloned_message_debt() {
    for source in [
        ril_test::case_bytes(
            "tests/regressions/channels.ril::channel-condition-receipts-clone-unpaid",
        ),
        ril_test::case_bytes(
            "tests/regressions/channels.ril::channel-condition-receipts-nested-unpaid",
        ),
    ] {
        match Session::new(source.to_vec()).check() {
            ril_compiler::CompilationOutcome::Rejected { diagnostics, .. } => assert!(
                diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.code == "E0720"),
                "{diagnostics:?}"
            ),
            other => panic!("unpaid business message is not a semantic pass: {other:?}"),
        }
    }
}
