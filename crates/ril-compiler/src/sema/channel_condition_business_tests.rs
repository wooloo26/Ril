//! Actual business regions must consume the new proven receipt.
use super::*;

fn source_fixture() -> &'static [u8] {
    ril_test::case_bytes("tests/regressions/channels.ril::channel-condition-receipts-checked")
}

#[test]
fn the_receipt_is_proved_inside_a_real_send_receive_region_and_reaches_core() {
    let program = crate::Session::new(source_fixture().to_vec())
        .verify()
        .unwrap();
    let facts = program.facts();
    let regions = facts
        .channel_messages
        .iter()
        .filter_map(|event| match &event.action {
            ChannelAction::Send { payload, .. } | ChannelAction::Receive { payload, .. }
                if !payload.value.results.is_empty() =>
            {
                Some(super::super::region(facts, event.context).unwrap())
            }
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    assert!(!regions.is_empty());
    let proven = facts
        .channel_messages
        .iter()
        .filter(|event| {
            regions.contains(&super::super::region(facts, event.context).unwrap())
                && Analysis::new(facts).truth(event).unwrap() == Some(true)
        })
        .collect::<Vec<_>>();
    assert!(
        !proven.is_empty(),
        "business replay has no Source-grounded complete receipt"
    );
    let _core = crate::lower::lower_core(&program).unwrap();
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
        match crate::Session::new(source.to_vec()).check() {
            crate::CompilationOutcome::Rejected { diagnostics, .. } => assert!(
                diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.code == "E0720"),
                "{diagnostics:?}"
            ),
            other => panic!("unpaid business message is not a semantic pass: {other:?}"),
        }
    }
}

#[test]
fn jointly_widened_business_receipt_and_tag_guards_cannot_erase_source_presence() {
    let program = crate::Session::new(source_fixture().to_vec())
        .verify()
        .unwrap();
    let mut facts = program.facts().clone();
    let event = facts
        .channel_messages
        .iter()
        .find(|event| Analysis::new(&facts).truth(event).unwrap() == Some(true))
        .unwrap()
        .clone();
    let region = super::super::region(&facts, event.context).unwrap();
    assert!(facts.channel_messages.iter().any(|candidate| matches!(
        candidate.action,
        ChannelAction::Send { .. }
    ) && super::super::region(
        &facts,
        candidate.context
    ) == Ok(region)));
    for candidate in &mut facts.channel_messages {
        if candidate.context == event.context
            && matches!(
                candidate.action,
                ChannelAction::TagTest { .. } | ChannelAction::ConditionEvaluated { .. }
            )
        {
            candidate.guard = ChannelGuard::always();
        }
    }
    assert_eq!(
        Analysis::new(&facts)
            .truth(&facts.channel_messages[event.id.0 as usize])
            .unwrap(),
        None
    );
}
