use ril_compiler::{Session, sema::channel_messages::ChannelAction};

fn facts() -> ril_compiler::sema::SemanticFacts {
    Session::new(
        ril_test::case_bytes("tests/regressions/channels.ril::channel-formal-result").to_vec(),
    )
    .verify()
    .unwrap()
    .facts()
    .clone()
}

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
    let core = ril_compiler::lower::lower_core(&verified).unwrap();
    assert_eq!(
        core.provenance.channel_repetitions.len(),
        verified.facts().channel_repetitions.len()
    );
}

#[test]
fn erasing_repetition_tables_cannot_erase_callback_and_incoming_loop_call_bounds() {
    use ril_syntax::ast::{ExprKind, Literal, StmtKind};
    for (source, array) in [
        (
            ril_test::case_source(
                "tests/regressions/channels.ril::channel-message-repeated-cardinality-gap",
            )
            .replace("[1,2]", "[1]"),
            true,
        ),
        (
            ril_test::case_source(
                "tests/regressions/channels.ril::channel-message-loop-cardinality-gap",
            )
            .replace("0..2", "0..1"),
            false,
        ),
    ] {
        let verified = Session::new(source.as_bytes().to_vec()).verify().unwrap();
        let mut changed = verified.facts().clone();
        changed.channel_repetitions.clear();
        for event in &mut changed.channel_messages {
            event.repetition = None;
        }
        let mut edits = 0;
        for closure in &mut changed.closures {
            let ExprKind::Block(body) = &mut closure.body.kind else {
                continue;
            };
            for statement in &mut body.statements {
                let value = match &mut statement.kind {
                    StmtKind::Binding(binding) => &mut binding.value,
                    StmtKind::Expr { expression, .. } => expression,
                    _ => continue,
                };
                if array {
                    if let ExprKind::Call { callee, arguments } = &mut value.kind
                        && matches!(&callee.kind, ExprKind::Path(path) if path.join("::") == "Array::map")
                        && let ExprKind::Array(values) = &mut arguments[0].value.kind
                    {
                        values.push(values[0].clone());
                        edits += 1;
                    }
                } else if let ExprKind::For { iterable, .. } = &mut value.kind
                    && let ExprKind::Range { end: Some(end), .. } = &mut iterable.kind
                {
                    end.kind = ExprKind::Literal(Literal::Integer("2".into()));
                    edits += 1;
                }
            }
        }
        assert!(edits > 0);
        rejected(&changed);
    }
    let mut changed = facts();
    changed
        .closure_invocations
        .iter_mut()
        .filter(|invocation| !invocation.probe)
        .for_each(|invocation| invocation.source_event = None);
    rejected(&changed);
}

#[test]
fn zero_entry_inspection_cannot_pay_a_later_channel_message() {
    use ril_syntax::ast::{ExprKind, StmtKind};
    let original = ril_test::case_source("tests/regressions/channels.ril::channel-formal-result");
    let inspected = original.replace(
        "let sent=publish(mut tx,payload)",
        "let inspect=\\number:int->{assert(payload is Ok(_)|Err(_));number}\nlet _=Array::map([1],inspect)\nlet sent=publish(mut tx,payload)",
    ).replace("Ok(value)->assert(value is Ok(7)|Err(_))", "Ok(_)->()");
    let verified = Session::new(inspected.as_bytes().to_vec())
        .verify()
        .unwrap();
    ril_compiler::lower::lower_core(&verified).unwrap();
    let mut changed = verified.facts().clone();
    changed.channel_repetitions.clear();
    for event in &mut changed.channel_messages {
        event.repetition = None;
    }
    for duty in &mut changed.result_duties {
        duty.inspected = true;
        duty.covered = true;
    }
    let mut edits = 0;
    for closure in &mut changed.closures {
        let ExprKind::Block(body) = &mut closure.body.kind else {
            continue;
        };
        for statement in &mut body.statements {
            if let StmtKind::Binding(binding) = &mut statement.kind
                && let ExprKind::Call { callee, arguments } = &mut binding.value.kind
                && matches!(&callee.kind, ExprKind::Path(path) if path.join("::") == "Array::map")
                && let ExprKind::Array(values) = &mut arguments[0].value.kind
            {
                values.clear();
                edits += 1;
            }
        }
    }
    assert!(edits > 0);
    rejected(&changed);
    for source in [
        inspected.replace("[1],inspect", "[],inspect"),
        inspected.replace("[1],inspect", "[1,2],inspect").replace(
            "assert(payload is Ok(_)|Err(_));number",
            "if false {assert(payload is Ok(_)|Err(_))};number",
        ),
    ] {
        assert!(
            !matches!(
                Session::new(source.as_bytes().to_vec()).check(),
                ril_compiler::CompilationOutcome::Accepted { .. }
            ),
            "{source}"
        );
    }
}

fn rejected(facts: &ril_compiler::sema::SemanticFacts) {
    let issues = ril_compiler::sema::validate::solved_facts(facts).unwrap_err();
    assert!(
        issues.iter().any(|issue| matches!(
            issue.kind,
            ril_compiler::sema::validate::ValidationIssueKind::ChannelMessage(_)
        )),
        "{issues:?}"
    );
}

#[test]
fn deleting_transport_or_normal_exit_tables_cannot_erase_their_coverage() {
    let original = facts();
    for table in 0..3 {
        let mut changed = original.clone();
        if table != 1 {
            changed.channel_messages.clear();
        }
        if table != 0 {
            changed.channel_exits.clear();
        }
        changed.channel_message_sequence = 0;
        rejected(&changed);
    }
    let mut changed = original;
    changed.channel_exits.last_mut().unwrap().guard =
        ril_compiler::sema::channel_messages::ChannelGuard::never();
    rejected(&changed);
}

#[test]
fn producer_ownership_receive_sources_and_physical_generations_need_actual_evidence() {
    use ril_compiler::sema::{channel_messages::ChannelAnchor, facts::ScopeId};
    let original = facts();
    let mut changed = original.clone();
    let owners = changed
        .channel_messages
        .iter_mut()
        .find_map(|event| match &mut event.action {
            ChannelAction::Send {
                anchor: ChannelAnchor::Known { .. },
                original_owners,
                ..
            } => Some(original_owners),
            _ => None,
        })
        .unwrap();
    *owners.values_mut().next().unwrap() = ScopeId(0);
    rejected(&changed);
    let mut changed = original.clone();
    let sources = changed
        .channel_messages
        .iter_mut()
        .find_map(|event| match &mut event.action {
            ChannelAction::Receive { sources, .. } => Some(sources),
            _ => None,
        })
        .unwrap();
    sources[0].send = None;
    rejected(&changed);
    let mut changed = original;
    let versions = changed
        .channel_messages
        .iter_mut()
        .find_map(|event| match &mut event.action {
            ChannelAction::Send {
                anchor: ChannelAnchor::Known { .. },
                producer_versions,
                ..
            } => Some(producer_versions),
            _ => None,
        })
        .unwrap();
    for version in versions.values_mut() {
        *version += 1;
    }
    rejected(&changed);
}

#[test]
fn final_inspected_flags_cannot_replace_missing_business_inspection_events() {
    use ril_compiler::sema::channel_messages::ChannelAnchor;
    let mut changed = facts();
    let producers = changed
        .channel_messages
        .iter()
        .find_map(|event| match &event.action {
            ChannelAction::Send {
                anchor: ChannelAnchor::Known { .. },
                payload,
                ..
            } => Some(payload.value.results.clone()),
            _ => None,
        })
        .unwrap();
    for event in &mut changed.channel_messages {
        if let ChannelAction::Inspect { value, .. } = &mut event.action {
            value
                .value
                .must_outer_results
                .retain(|producer| !producers.contains(producer));
        }
    }
    for evaluation in &mut changed.condition_evaluations {
        evaluation
            .inspections
            .when_true
            .retain(|producer| !producers.contains(producer));
        evaluation
            .inspections
            .when_false
            .retain(|producer| !producers.contains(producer));
    }
    for duty in &mut changed.result_duties {
        duty.inspected = true;
        duty.covered = true;
    }
    rejected(&changed);
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
fn caller_summary_identity_and_complete_return_coverage_are_not_optional() {
    let original = facts();
    let mut changed = original.clone();
    for summary in &mut changed.invocations {
        summary.channel_messages.clear();
    }
    rejected(&changed);
    let mut changed = original;
    for summary in &mut changed.invocations {
        summary.activation = None;
        summary.context = None;
    }
    rejected(&changed);
    let mut changed = Session::new(
        ril_test::case_bytes("tests/regressions/channels.ril::channel-message-question-checked")
            .to_vec(),
    )
    .verify()
    .unwrap()
    .facts()
    .clone();
    let returned = changed
        .channel_exits
        .iter()
        .find(|exit| exit.kind == ril_compiler::sema::channel_messages::ChannelExitKind::Return)
        .unwrap()
        .clone();
    let completion = changed
        .channel_exits
        .iter_mut()
        .find(|exit| {
            exit.activation == returned.activation
                && exit.kind == ril_compiler::sema::channel_messages::ChannelExitKind::Complete
        })
        .unwrap();
    completion.guard = completion
        .guard
        .and(&returned.guard.not().unwrap())
        .unwrap();
    rejected(&changed);
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
fn unknown_nested_and_collection_producer_graphs_never_become_complete_from_one_tag() {
    for source in [
        ril_test::case_source(
            "tests/regressions/channels.ril::channel-message-formal-array-graph-gap",
        ),
        ril_test::case_source(
            "tests/regressions/channels.ril::channel-message-formal-map-graph-gap",
        ),
    ] {
        match Session::new(source.as_bytes().to_vec()).check() {
            ril_compiler::CompilationOutcome::NotImplemented { reason } => assert!(
                format!("{reason:?}").contains("complete ordinary graph"),
                "{reason:?}"
            ),
            other => panic!("{other:?}\n{source}"),
        }
    }
    let source =
        ril_test::case_source("tests/regressions/channels.ril::channel-message-finite-graphs");
    let verified = Session::new(source.as_bytes().to_vec())
        .verify()
        .unwrap_or_else(|error| panic!("{error:?}"));
    ril_compiler::lower::lower_core(&verified).unwrap();
    let mut changed = verified.facts().clone();
    for event in &mut changed.channel_messages {
        if let ChannelAction::Send { payload, .. } = &mut event.action
            && matches!(payload.value.ty, ril_compiler::sema::model::Ty::Result(..))
        {
            payload.value.result_success = None;
            payload.value.result_payload = None;
            payload.value.result_tag = None;
            break;
        }
    }
    rejected(&changed);
}

#[test]
fn finite_formal_nested_results_retain_branch_exclusive_borrowed_producers() {
    for source in [
        ril_test::case_source(
            "tests/regressions/channels.ril::channel-message-formal-nested-checked",
        ),
        ril_test::case_source(
            "tests/regressions/channels.ril::channel-message-formal-two-branches-checked",
        ),
    ] {
        let verified = Session::new(source.as_bytes().to_vec())
            .verify()
            .unwrap_or_else(|error| panic!("{error:?}\n{source}"));
        ril_compiler::lower::lower_core(&verified).unwrap();
        let mut changed = verified.facts().clone();
        for event in &mut changed.channel_messages {
            if let ChannelAction::Send { payload, .. } = &mut event.action
                && payload
                    .value
                    .result_success
                    .as_ref()
                    .is_some_and(|value| !value.outer_results.is_empty())
            {
                payload.value.result_success = None;
                break;
            }
        }
        rejected(&changed);
    }
    let source = ril_test::case_source(
        "tests/regressions/channels.ril::channel-message-formal-nested-graph-gap",
    );
    match Session::new(source.as_bytes().to_vec()).check() {
        ril_compiler::CompilationOutcome::Rejected { diagnostics, .. } => assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "E0720"),
            "{diagnostics:?}"
        ),
        other => panic!("{other:?}\n{source}"),
    }
    let source = ril_test::case_source(
        "tests/regressions/channels.ril::channel-message-formal-two-branches-checked",
    );
    for source in [
        source.replace("Err(inner)->assert(inner is Ok(_)|Err(_))", "Err(_)->()"),
        source.replace("Ok(inner)->assert(inner is Ok(_)|Err(_))", "Ok(_)->()"),
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
fn a_business_event_cannot_move_to_an_unrelated_declaration_region() {
    let source = ril_test::case_source(
        "tests/regressions/channels.ril::channel-message-formal-nested-checked",
    );
    let verified = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    let mut changed = verified.facts().clone();
    let other = changed
        .functions
        .iter()
        .find(|function| function.syntax.name == "test_native")
        .unwrap()
        .definition;
    let send = changed
        .channel_messages
        .iter_mut()
        .find(|event| matches!(event.action, ChannelAction::Send { .. }))
        .unwrap();
    send.context.invocation = None;
    send.context.closure_invocation = None;
    send.context.closure = None;
    send.context.owner = Some(ril_compiler_core::ids::CallableOwner::Function(other));
    rejected(&changed);
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
fn independent_formal_optional_paths_cannot_be_unified_even_with_one_valid_cause() {
    let source = ril_test::case_source(
        "tests/regressions/channels.ril::channel-message-formal-two-optionals-checked",
    );
    let verified = Session::new(source.as_bytes().to_vec())
        .verify()
        .unwrap_or_else(|error| panic!("{error:?}\n{source}"));
    let mut changed = verified.facts().clone();
    let invocation = changed
        .copy_invocations
        .iter_mut()
        .find(|invocation| {
            invocation.declaration_probe
                && invocation.caller_activation.is_none()
                && invocation.entry.arguments.len() == 2
                && invocation.entry.arguments[0]
                    .1
                    .value
                    .option_identity
                    .is_some()
                && invocation.entry.arguments[1]
                    .1
                    .value
                    .option_identity
                    .is_some()
        })
        .unwrap();
    let identity = invocation.entry.arguments[0]
        .1
        .value
        .option_identity
        .unwrap();
    assert_ne!(
        Some(identity),
        invocation.entry.arguments[1].1.value.option_identity
    );
    invocation.entry.arguments[1].1.value.option_identity = Some(identity);
    invocation.entry.arguments[1].1.value.cause = changed.optional_tags[identity.0 as usize].cause;
    // The arena entry, payload type, owner and ancestry are all individually
    // valid. The two actual symbolic input positions must still be independent.
    rejected(&changed);
}

#[test]
fn formal_optional_independence_cannot_be_disabled_by_a_registered_owner() {
    let source = ril_test::case_source(
        "tests/regressions/channels.ril::channel-message-formal-two-optionals-checked",
    );
    let verified = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    let mut changed = verified.facts().clone();
    let invocation = changed
        .copy_invocations
        .iter_mut()
        .find(|invocation| {
            invocation.declaration_probe
                && invocation.caller_activation.is_none()
                && invocation.entry.arguments.len() == 2
                && invocation.entry.arguments[0]
                    .1
                    .value
                    .option_identity
                    .is_some()
                && invocation.entry.arguments[1]
                    .1
                    .value
                    .option_identity
                    .is_some()
        })
        .unwrap();
    let identity = invocation.entry.arguments[0]
        .1
        .value
        .option_identity
        .unwrap();
    assert_ne!(
        Some(identity),
        invocation.entry.arguments[1].1.value.option_identity
    );
    invocation.entry.arguments[1].1.value.option_identity = Some(identity);
    invocation.entry.arguments[1].1.value.cause = changed.optional_tags[identity.0 as usize].cause;
    // Registry-valid owner metadata must not change which actual declaration
    // parameter paths are independent symbolic inputs.
    changed.optional_tags[identity.0 as usize].creation_owner =
        *changed.allocated_scopes.iter().next().unwrap();
    rejected(&changed);
}

#[test]
fn formal_optional_independence_survives_every_entry_selector_combination() {
    let source = ril_test::case_source(
        "tests/regressions/channels.ril::channel-message-formal-two-optionals-checked",
    );
    let actual_alias = format!(
        "{source}\nfn alias_unknown_optional(value:Option<Result<int,str>>)->Result<(),Concurrent::TaskFault> @Async{{consume(value,value)}}\nfn named_optional_callback(value:Option<Result<int,str>>) @Async{{assert(consume(value,value) is Ok()|Err(_))}}\nfn through_named_optional_callback(value:Option<Result<int,str>>) @Async{{named_optional_callback(value)}}\nfn through_single_optional_callback(value:Option<Result<int,str>>) @Async{{let mapped=Array::map([1],\\number:int->{{named_optional_callback(value);number}})}}\n"
    );
    let alias_verified = Session::new(actual_alias.as_bytes().to_vec())
        .verify()
        .unwrap_or_else(|error| panic!("lawful actual input alias: {error:?}"));
    ril_compiler::lower::lower_core(&alias_verified).unwrap();
    let verified = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    let original = verified.facts().clone();
    let entry = original
        .copy_invocations
        .iter()
        .find(|invocation| {
            invocation.declaration_probe
                && invocation.caller_activation.is_none()
                && invocation.entry.arguments.len() == 2
                && invocation.entry.arguments[0]
                    .1
                    .value
                    .option_identity
                    .is_some()
                && invocation.entry.arguments[1]
                    .1
                    .value
                    .option_identity
                    .is_some()
        })
        .unwrap();
    let header = original
        .functions
        .iter()
        .find(|function| function.definition == entry.target)
        .unwrap();
    assert_eq!(entry.span, header.syntax.span);
    let scope = *original.allocated_scopes.iter().next().unwrap();
    let actual_source = original
        .copy_call_events
        .iter()
        .find(|event| event.target == Some(entry.target))
        .unwrap()
        .id;
    let parent = original
        .copy_invocations
        .iter()
        .find(|candidate| candidate.id != entry.id && candidate.parent.is_none())
        .unwrap()
        .id;
    println!(
        "real declaration entry={:?}, target={:?}, header={:?}, parameters={}",
        entry.id,
        entry.target,
        header.syntax.span,
        header.syntax.parameters.len()
    );
    let mut accepted = Vec::new();
    let mut unrelated_rejections = Vec::new();
    for selectors in 0u8..16 {
        let mut changed = original.clone();
        let invocation = &mut changed.copy_invocations[entry.id.0 as usize];
        let identity = invocation.entry.arguments[0]
            .1
            .value
            .option_identity
            .unwrap();
        assert_ne!(
            Some(identity),
            invocation.entry.arguments[1].1.value.option_identity
        );
        invocation.entry.arguments[1].1.value.option_identity = Some(identity);
        invocation.entry.arguments[1].1.value.cause =
            changed.optional_tags[identity.0 as usize].cause;
        // All substituted identities are registered. The original real
        // declaration span and two frozen symbolic input paths stay intact.
        changed.optional_tags[identity.0 as usize].creation_owner = scope;
        if selectors & 1 != 0 {
            invocation.declaration_probe = false;
        }
        if selectors & 2 != 0 {
            invocation.caller_activation = Some(scope);
        }
        if selectors & 4 != 0 {
            invocation.source_event = Some(actual_source);
        }
        if selectors & 8 != 0 {
            invocation.parent = Some(parent);
        }
        match ril_compiler::sema::validate::solved_facts(&changed) {
            Ok(structure) => {
                println!("entry selectors={selectors:04b}: ACCEPTED {structure:?}");
                accepted.push(selectors);
            }
            Err(issues) => {
                println!("entry selectors={selectors:04b}: rejected {issues:?}");
                if !issues.iter().any(|issue| {
                    matches!(&issue.kind, ril_compiler::sema::validate::ValidationIssueKind::ChannelMessage(message)
                        if message.contains("independent symbolic formal parameter paths"))
                }) {
                    unrelated_rejections.push(selectors);
                }
            }
        }
    }
    assert!(
        accepted.is_empty(),
        "real independent formal paths were accepted after changing entry selectors: {accepted:?}"
    );
    assert!(
        unrelated_rejections.is_empty(),
        "entry selectors did not reconstruct the actual formal independence duty: {unrelated_rejections:?}"
    );
}

#[test]
fn deleting_the_entire_formal_input_table_cannot_skip_header_coverage() {
    let source = ril_test::case_source(
        "tests/regressions/channels.ril::channel-message-formal-two-optionals-checked",
    );
    let verified = Session::new(source.as_bytes().to_vec()).verify().unwrap();
    let mut changed = verified.facts().clone();
    let invocation = changed
        .copy_invocations
        .iter_mut()
        .find(|invocation| {
            invocation.declaration_probe
                && invocation.caller_activation.is_none()
                && invocation.entry.arguments.len() == 2
                && invocation.entry.arguments[0]
                    .1
                    .value
                    .option_identity
                    .is_some()
                && invocation.entry.arguments[1]
                    .1
                    .value
                    .option_identity
                    .is_some()
        })
        .unwrap();
    invocation.entry.arguments.clear();
    let result = ril_compiler::sema::validate::solved_facts(&changed);
    println!("deleted whole declaration input table: {result:?}");
    let issues = result.unwrap_err();
    assert!(
        issues.iter().any(|issue| {
            matches!(&issue.kind, ril_compiler::sema::validate::ValidationIssueKind::ChannelMessage(message)
                if message.contains("actual parameter header"))
        }),
        "{issues:?}"
    );
}

#[test]
fn unrelated_global_optional_inputs_do_not_require_business_message_source_proofs() {
    let scalar =
        ril_test::case_source("tests/regressions/channels.ril::channel-message-optional-scalar");
    Session::new(scalar.as_bytes().to_vec()).verify().unwrap();
    let source = format!(
        "{scalar}\nfn unrelated_global_optional(value:?int)->int{{value ?? 0}}\nlet STORED=unrelated_global_optional(Array::get([1],0))\n"
    );
    let outcome = Session::new(source.as_bytes().to_vec()).verify();
    match &outcome {
        Ok(_) => println!("unrelated global scalar Option input: verified"),
        Err(error) => println!("unrelated global scalar Option input: {error:?}"),
    }
    let verified = outcome.unwrap();
    ril_compiler::lower::lower_core(&verified).unwrap();

    // Ordinary Result receipts can depend on a scalar Option tag even when
    // every channel payload is Result-free. That tag still owes its source.
    let ordinary = format!(
        "{scalar}\nfn ordinary_tag_receipts(value:?int){{let result:Result<int,str>=Ok(1);if value is Some(_){{assert(result is Ok(_)|Err(_))}}else{{assert(result is Ok(_)|Err(_))}}}}\nfn ordinary_tag_forward(value:?int){{ordinary_tag_receipts(value)}}\n"
    );
    let verified = Session::new(ordinary.as_bytes().to_vec()).verify().unwrap();
    ril_compiler::lower::lower_core(&verified).unwrap();
    let mut changed = verified.facts().clone();
    let target = changed
        .functions
        .iter()
        .find(|function| function.syntax.name == "ordinary_tag_receipts")
        .unwrap()
        .definition;
    let call = changed
        .copy_invocations
        .iter_mut()
        .find(|invocation| {
            invocation.target == target
                && !invocation.declaration_probe
                && invocation.source_event.is_some()
                && invocation.entry.arguments[0]
                    .1
                    .value
                    .option_identity
                    .is_some()
        })
        .unwrap();
    call.source_event = None;
    let issues = ril_compiler::sema::validate::solved_facts(&changed).unwrap_err();
    assert!(
        issues.iter().any(|issue| {
            matches!(&issue.kind, ril_compiler::sema::validate::ValidationIssueKind::ChannelMessage(message)
                if message.contains("optional input call lacks its actual named source application"))
        }),
        "ordinary Result conditional source was erased: {issues:?}"
    );
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
    let core = ril_compiler::lower::lower_core(&verified).unwrap();
    assert_eq!(
        core.provenance.channel_messages.len(),
        verified.facts().channel_messages.len()
    );
    assert_eq!(
        core.provenance.channel_exits.len(),
        verified.facts().channel_exits.len()
    );
}
