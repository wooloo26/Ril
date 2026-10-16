//! Independent replay of actual channel Result custody.
//!
//! This module deliberately does not consume the checker's private ledger or
//! final Result inspection/ownership bits. Each normal exit is checked against
//! prior guarded events and frozen carrier graphs.
use super::{
    ConcurrentBoundaryKind as Boundary, SemanticFacts,
    channel_messages::*,
    copy_contract::CopyValueSnapshot,
    effect_identity::InvocationContext,
    facts::{NodeId, ScopeId},
    model::Value,
};
use ril_compiler_core::{diagnostic::CauseId, source::Span};
use std::collections::{BTreeMap, BTreeSet};
#[path = "channel_condition_validation.rs"]
mod conditions;
#[path = "channel_optional_validation.rs"]
mod optional;
#[path = "channel_repetition_validation.rs"]
mod repetition;
#[cfg(test)]
#[path = "channel_state_observer.rs"]
mod state_observer;

type Failure = (Span, Option<CauseId>, String);
type Check<T = ()> = Result<T, String>;
type Clock = BTreeMap<Option<NodeId>, u64>;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
enum Custody {
    Caller(ScopeId),
    Channel(ChannelAnchor),
}
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
struct Packet {
    send: ChannelMessageId,
    producers: BTreeSet<u32>,
    clock: Clock,
}
#[derive(Clone, Default, PartialEq, Eq, PartialOrd, Ord)]
struct Case {
    guard: ChannelGuard,
    custody: BTreeMap<u32, Custody>,
    owners: BTreeMap<u32, ScopeId>,
    inspected: BTreeSet<u32>,
    returned: BTreeMap<u32, ScopeId>,
    queues: BTreeMap<ChannelAnchor, Vec<Packet>>,
    closed: BTreeSet<ChannelAnchor>,
    clocks: BTreeMap<Option<NodeId>, Clock>,
    tasks: BTreeMap<NodeId, Option<NodeId>>,
    executed: BTreeSet<ChannelMessageId>,
}
#[derive(Default)]
struct Replay {
    cases: Vec<Case>,
    aliases: BTreeMap<u32, BTreeSet<ChannelMessageId>>,
    versions: BTreeMap<u32, u32>,
    outcomes: BTreeMap<u32, [ChannelGuard; 2]>,
    epoch: usize,
    business: BTreeSet<u32>,
}
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Region {
    Named(u32),
    Closure(u32),
    Declaration(u32),
    Global,
}

pub(super) fn validate(facts: &SemanticFacts) -> Result<(), Failure> {
    // Ordinary programs do not owe transport evidence or spend its budget.
    if !facts
        .concurrent_boundaries
        .iter()
        .any(|boundary| matches!(boundary.kind, Boundary::Send | Boundary::Receive))
    {
        return Ok(());
    }
    let fallback = facts.concurrent_boundaries.first().unwrap().span;
    metadata(facts).map_err(|message| (fallback, None, message))?;
    let roots = facts
        .channel_messages
        .iter()
        .filter_map(|event| match &event.action {
            ChannelAction::Send { payload, .. } | ChannelAction::Receive { payload, .. } => {
                Some(&payload.value.results)
            }
            _ => None,
        })
        .flatten()
        .copied()
        .collect::<BTreeSet<_>>();
    if roots.is_empty() {
        return Ok(());
    }
    let mut execution_bounds = repetition::Analysis::new(facts);
    let mut condition_proofs = conditions::Analysis::new(facts);
    execution_bounds
        .metadata()
        .map_err(|message| (fallback, None, message))?;
    let mut business = family(facts, &roots).map_err(|message| (fallback, None, message))?;
    loop {
        let previous = business.len();
        for event in &facts.channel_messages {
            if let ChannelAction::ResultAliases { map } = &event.action {
                for (new, old) in map {
                    if business.contains(new) || !business.is_disjoint(old) {
                        business.insert(*new);
                        business.extend(old);
                    }
                }
            }
        }
        if business.len() == previous {
            break;
        }
        if business.len() > 4096 {
            return Err((
                fallback,
                None,
                "business producer dependency bound exceeded".into(),
            ));
        }
    }
    let mut records = facts
        .channel_messages
        .iter()
        .map(Record::Event)
        .chain(facts.channel_exits.iter().map(Record::Exit))
        .collect::<Vec<_>>();
    records.sort_by_key(|record| record.sequence());
    let mut regions = BTreeMap::<Region, Replay>::new();
    let business_regions = facts
        .channel_messages
        .iter()
        .filter(|event| match &event.action {
            ChannelAction::Send { payload, .. } | ChannelAction::Receive { payload, .. } => {
                !payload.value.results.is_empty()
            }
            _ => false,
        })
        .map(|event| region(facts, event.context))
        .collect::<Check<BTreeSet<_>>>()
        .map_err(|message| (fallback, None, message))?;
    for record in records {
        let region = region(facts, record.context())
            .map_err(|message| (record.span(), Some(record.cause()), message))?;
        if !business_regions.contains(&region) {
            continue;
        }
        if let Record::Event(event) = record
            && matches!(
                event.action,
                ChannelAction::Inspect { .. }
                    | ChannelAction::Select { .. }
                    | ChannelAction::ConditionEvaluated { .. }
            )
            && !execution_bounds
                .inspection_entered(event)
                .map_err(|message| (event.span, Some(event.cause), message))?
        {
            continue;
        }
        let condition_truth = if let Record::Event(event) = record
            && matches!(event.action, ChannelAction::ConditionEvaluated { .. })
        {
            let truth = condition_proofs
                .truth(event)
                .map_err(|message| (event.span, Some(event.cause), message))?;
            // An unproved receipt is not an event that can split/delete cases.
            // Epoch remapping is still performed at the next actual operation.
            if truth.is_none() {
                continue;
            }
            truth
        } else {
            None
        };
        let replay = regions.entry(region).or_insert_with(|| Replay {
            cases: vec![Case::default()],
            business: business.clone(),
            ..Default::default()
        });
        replay
            .advance(facts, record.epoch())
            .and_then(|()| replay.record(facts, record, condition_truth))
            .map_err(|message| {
                (
                    record.span(),
                    Some(record.cause()),
                    format!("channel event {}: {message}", record.sequence()),
                )
            })?;
    }
    Ok(())
}

#[derive(Clone, Copy)]
enum Record<'a> {
    Event(&'a ChannelMessageFact),
    Exit(&'a ChannelExitFact),
}
impl Record<'_> {
    fn sequence(self) -> u64 {
        match self {
            Self::Event(e) => e.sequence,
            Self::Exit(e) => e.sequence,
        }
    }
    fn epoch(self) -> usize {
        match self {
            Self::Event(e) => e.allocation_epoch,
            Self::Exit(e) => e.allocation_epoch,
        }
    }
    fn span(self) -> Span {
        match self {
            Self::Event(e) => e.span,
            Self::Exit(e) => e.span,
        }
    }
    fn cause(self) -> CauseId {
        match self {
            Self::Event(e) => e.cause,
            Self::Exit(e) => e.cause,
        }
    }
    fn context(self) -> InvocationContext {
        match self {
            Self::Event(e) => e.context,
            Self::Exit(e) => e.context,
        }
    }
}
fn record_guard<'a>(record: Record<'a>) -> &'a ChannelGuard {
    match record {
        Record::Event(e) => &e.guard,
        Record::Exit(e) => &e.guard,
    }
}

fn merge_cases(cases: Vec<Case>) -> Check<Vec<Case>> {
    #[cfg(test)]
    state_observer::merge_begin(cases.len());
    let mut states = BTreeMap::<Case, ChannelGuard>::new();
    for mut case in cases {
        #[cfg(test)]
        state_observer::input_processed();
        let guard = std::mem::take(&mut case.guard);
        if let Some(previous) = states.get_mut(&case) {
            *previous = previous
                .or(&guard)
                .ok_or("equivalent channel case guard join exceeds its bound")?;
        } else {
            states.insert(case, guard);
        }
        if states.len() > 256 {
            #[cfg(test)]
            state_observer::overflow(&states);
            return Err("independent channel replay exceeds its case bound".into());
        }
    }
    Ok(states
        .into_iter()
        .map(|(mut case, guard)| {
            case.guard = guard;
            case
        })
        .collect())
}

fn region(facts: &SemanticFacts, context: InvocationContext) -> Check<Region> {
    // A closure declaration probe is a separate hypothetical invocation. A
    // real closure nested under a named invocation shares its caller's state.
    let mut closure = context.closure_invocation;
    let mut declaration_owner = context.owner;
    let mut seen = BTreeSet::new();
    while let Some(id) = closure {
        if !seen.insert(id) {
            return Err("closure invocation cycle".into());
        }
        let entry = facts
            .closure_invocations
            .get(id.0 as usize)
            .filter(|entry| entry.id == id)
            .ok_or("missing actual closure invocation")?;
        if entry.probe {
            return Ok(Region::Closure(id.0));
        }
        declaration_owner = entry.caller_owner;
        closure = entry.parent_closure;
    }
    let mut invocation = context.invocation;
    let mut root = None;
    let mut seen = BTreeSet::new();
    while let Some(id) = invocation {
        if !seen.insert(id) {
            return Err("named invocation cycle".into());
        }
        let entry = facts
            .copy_invocations
            .get(id.0 as usize)
            .filter(|entry| entry.id == id)
            .ok_or("missing actual named invocation")?;
        root = Some(id.0);
        invocation = entry.parent;
    }
    Ok(root
        .map(Region::Named)
        .unwrap_or_else(|| match declaration_owner {
            Some(ril_compiler_core::ids::CallableOwner::Function(id)) => Region::Declaration(id.0),
            _ => Region::Global,
        }))
}

fn metadata(facts: &SemanticFacts) -> Check {
    optional::validate(facts)?;
    if facts
        .channel_messages
        .len()
        .saturating_add(facts.channel_exits.len())
        > 4096
    {
        return Err("independent channel history exceeds its work bound".into());
    }
    let mut sequence = BTreeSet::new();
    for (index, event) in facts.channel_messages.iter().enumerate() {
        if event.id.0 as usize != index || !sequence.insert(event.sequence) {
            return Err("event identities/sequence are incomplete".into());
        }
        validate_guard(facts, &event.guard, event.sequence)?;
        if matches!(
            event.action,
            ChannelAction::Send { .. } | ChannelAction::Receive { .. }
        ) {
            event
                .source_event
                .and_then(|id| {
                    facts
                        .copy_call_events
                        .get(id.0 as usize)
                        .filter(|call| call.id == id)
                })
                .ok_or("channel event lacks its incoming source application")?;
            let transport = match &event.action {
                ChannelAction::Send { transport, .. }
                | ChannelAction::Receive { transport, .. } => transport,
                _ => unreachable!(),
            };
            if !facts.invocation_expressions.iter().any(|observation| {
                observation.context == event.context
                    && facts
                        .expressions
                        .get(observation.expression)
                        .is_some_and(|expression| {
                            expression.span == event.span
                                && expression.value.outer_results == transport.value.outer_results
                        })
            }) {
                return Err("channel operation lacks its actual expression and physical transport producer observation".into());
            }
        }
        if event.allocation_epoch > facts.allocation_history.len() {
            return Err("event allocation epoch is not historical".into());
        }
    }
    for exit in &facts.channel_exits {
        if !sequence.insert(exit.sequence) {
            return Err("exit sequence collides with another actual event".into());
        }
        validate_guard(facts, &exit.guard, exit.sequence)?;
        if exit.allocation_epoch > facts.allocation_history.len() {
            return Err("exit allocation epoch is not historical".into());
        }
        if exit.kind == ChannelExitKind::Return && !exit.guard.is_never() {
            let completions = facts
                .channel_exits
                .iter()
                .filter(|completion| {
                    completion.activation == exit.activation
                        && completion.sequence > exit.sequence
                        && matches!(completion.kind, ChannelExitKind::Complete)
                })
                .try_fold(ChannelGuard::never(), |guard, completion| {
                    guard.or(&completion.guard)
                })
                .ok_or("actual returned continuation completion exceeds its bound")?;
            if !exit
                .guard
                .and(
                    &completions
                        .not()
                        .ok_or("completion complement is unavailable")?,
                )
                .ok_or("return completion implication is unavailable")?
                .is_never()
            {
                return Err(
                    "actual returned continuation is absent from callable completion coverage"
                        .into(),
                );
            }
        }
        if exit.kind == ChannelExitKind::Complete {
            if !exit.returned.value.results.is_empty() || exit.anchor.is_some() {
                return Err("completion coverage contains producer return authority".into());
            }
            let receipts = facts
                .channel_exits
                .iter()
                .filter(|receipt| {
                    receipt.activation == exit.activation
                        && receipt.sequence < exit.sequence
                        && receipt.anchor.is_none()
                        && matches!(
                            receipt.kind,
                            ChannelExitKind::Callable
                                | ChannelExitKind::Return
                                | ChannelExitKind::Abnormal
                        )
                })
                .try_fold(ChannelGuard::never(), |guard, receipt| {
                    guard.or(&receipt.guard)
                })
                .ok_or("actual completion receipt union exceeds its bound")?;
            if receipts != exit.guard {
                return Err(
                    "completion does not exactly cover its actual return/fallthrough receipts"
                        .into(),
                );
            }
        }
        if exit.kind == ChannelExitKind::Scope
            && exit.anchor.as_ref().is_some_and(|anchor| {
                let scope = final_node(facts, anchor_scope(anchor), exit.allocation_epoch);
                facts
                    .channel_messages
                    .iter()
                    .any(|event| match &event.action {
                        ChannelAction::Send {
                            payload,
                            anchor: ChannelAnchor::Known { scope: actual, .. },
                            ..
                        }
                        | ChannelAction::Receive {
                            payload,
                            anchor: ChannelAnchor::Known { scope: actual, .. },
                            ..
                        } => {
                            !payload.value.results.is_empty()
                                && final_node(facts, *actual, event.allocation_epoch) == scope
                        }
                        _ => false,
                    })
            })
        {
            let receipts = facts
                .channel_exits
                .iter()
                .filter(|completion| {
                    completion.kind == ChannelExitKind::Complete
                        && completion.sequence < exit.sequence
                        && facts.scope_parents.get(&completion.activation) == Some(&exit.activation)
                        && (completion
                            .context
                            .closure_invocation
                            .and_then(|id| facts.closure_invocations.get(id.0 as usize))
                            .is_some_and(|invocation| invocation.site == exit.span)
                            || completion
                                .context
                                .invocation
                                .and_then(|id| facts.copy_invocations.get(id.0 as usize))
                                .is_some_and(|invocation| invocation.span == exit.span))
                })
                .try_fold(ChannelGuard::never(), |guard, completion| {
                    guard.or(&completion.guard)
                })
                .ok_or("scope callback completion union exceeds its bound")?;
            if receipts != exit.guard {
                return Err(
                    "scope completion does not cover its actual callback completion".into(),
                );
            }
        }
    }
    if sequence.len() as u64 != facts.channel_message_sequence
        || sequence
            .iter()
            .copied()
            .ne(0..facts.channel_message_sequence)
    {
        return Err("event/exit coverage does not reach the actual frontier".into());
    }
    // Reconstruct primitive coverage independently. Erasing both the arena and
    // its frontier cannot erase the actual endpoint operations.
    let mut operations = BTreeMap::new();
    for event in &facts.channel_messages {
        let (kind, scope, task) = match &event.action {
            ChannelAction::Send { anchor, .. } => (0, Some(anchor_scope(anchor)), event.task),
            ChannelAction::Receive { anchor, .. } => (1, Some(anchor_scope(anchor)), event.task),
            ChannelAction::TaskFork { child } => (2, None, Some(*child)),
            ChannelAction::TaskJoin { child } => (3, None, Some(*child)),
            _ => continue,
        };
        let key = (
            kind,
            event.span.file.0,
            event.span.start,
            event.span.end,
            scope.map(|node| final_node(facts, node, event.allocation_epoch)),
            task.map(|node| final_node(facts, node, event.allocation_epoch)),
        );
        *operations.entry(key).or_insert(0_usize) += 1;
    }
    for boundary in &facts.concurrent_boundaries {
        let kind = match boundary.kind {
            Boundary::Send => 0,
            Boundary::Receive => 1,
            Boundary::Fork => 2,
            Boundary::Join => 3,
            _ => continue,
        };
        let scope = (kind < 2).then_some(boundary.scope);
        let key = (
            kind,
            boundary.span.file.0,
            boundary.span.start,
            boundary.span.end,
            scope,
            boundary.task,
        );
        let count = operations
            .get_mut(&key)
            .ok_or("actual concurrent operation lacks message/order evidence")?;
        *count = count
            .checked_sub(1)
            .ok_or("duplicate primitive coverage claim")?;
    }
    if operations.values().any(|count| *count != 0) {
        return Err("message/order evidence has no matching actual concurrent operation".into());
    }
    for summary in &facts.invocations {
        let (Some(owner), Some(context)) = (summary.activation, summary.context) else {
            if !summary.channel_messages.is_empty() {
                return Err("channel summary lacks its actual invocation identity".into());
            }
            continue;
        };
        let expected = facts
            .channel_messages
            .iter()
            .filter(|event| {
                matches!(
                    event.action,
                    ChannelAction::Send { .. } | ChannelAction::Receive { .. }
                ) && descendant(facts, event.activation, owner)
            })
            .map(|event| event.id)
            .collect::<BTreeSet<_>>();
        if expected != summary.channel_messages {
            return Err("actual invocation summary omits or borrows channel events".into());
        }
        if context.invocation.is_none() {
            return Err("named invocation summary lacks its actual completed call identity".into());
        }
    }
    for event in &facts.channel_messages {
        if let ChannelAction::Send { payload, .. } | ChannelAction::Receive { payload, .. } =
            &event.action
            && !super::channel_production::complete(
                payload,
                &facts.external_type_declarations,
                &facts.constructors,
            )
        {
            return Err("actual message has an incomplete Result production graph".into());
        }
        let payload = match &event.action {
            ChannelAction::Send { payload, .. } | ChannelAction::Receive { payload, .. }
                if !payload.value.results.is_empty() =>
            {
                payload
            }
            _ => continue,
        };
        snapshot(facts, payload)?;
        if let Some(invocation) = event.context.invocation
            && !matches!(region(facts, event.context)?, Region::Closure(_))
            && !facts.invocations.iter().any(|summary| {
                summary
                    .context
                    .is_some_and(|context| context.invocation == Some(invocation))
                    && summary
                        .activation
                        .is_some_and(|owner| descendant(facts, event.activation, owner))
                    && summary.channel_messages.contains(&event.id)
            })
        {
            return Err("actual message event has no corresponding caller summary".into());
        }
        let event_region = region(facts, event.context)?;
        if !facts.channel_exits.iter().any(|exit| {
            exit.activation == event.activation
                && exit.kind == ChannelExitKind::Complete
                && exit.sequence > event.sequence
                && region(facts, exit.context) == Ok(event_region)
        }) {
            return Err("business message invocation lacks its actual completion exit".into());
        }
        if let ChannelAction::Send {
            anchor: ChannelAnchor::Known { scope, .. },
            ..
        } = &event.action
            && !event.guard.is_never()
            && !matches!(event_region, Region::Closure(_))
        {
            let final_scope = final_node(facts, *scope, event.allocation_epoch);
            if !facts.channel_exits.iter().any(|exit| {
                matches!(
                    exit.kind,
                    ChannelExitKind::Scope | ChannelExitKind::Abnormal
                ) && exit.sequence > event.sequence
                    && exit.anchor.as_ref().is_some_and(|anchor| {
                        final_node(facts, anchor_scope(anchor), exit.allocation_epoch)
                            == final_scope
                    })
                    && region(facts, exit.context) == Ok(event_region)
            }) {
                return Err("submitted business message lacks its scope completion exit".into());
            }
        }
    }
    Ok(())
}
fn descendant(facts: &SemanticFacts, mut actual: ScopeId, owner: ScopeId) -> bool {
    let mut seen = BTreeSet::new();
    loop {
        if actual == owner {
            return true;
        }
        if !seen.insert(actual) {
            return false;
        }
        let Some(parent) = facts.scope_parents.get(&actual) else {
            return false;
        };
        actual = *parent;
    }
}
fn anchor_scope(anchor: &ChannelAnchor) -> NodeId {
    match anchor {
        ChannelAnchor::Known { scope, .. } | ChannelAnchor::Formal { scope, .. } => *scope,
    }
}
fn final_node(facts: &SemanticFacts, mut node: NodeId, epoch: usize) -> NodeId {
    for (recent, older) in &facts.allocation_history[epoch..] {
        if node == *recent {
            node = *older;
        }
    }
    node
}
fn validate_guard(facts: &SemanticFacts, guard: &ChannelGuard, sequence: u64) -> Check {
    if guard.normalized().as_ref() != Some(guard) {
        return Err("guard is unavailable, over budget or not canonical".into());
    }
    for literal in guard.terms.iter().flatten() {
        match literal {
            GuardLiteral::Optional { identity, .. } => {
                if facts
                    .optional_tags
                    .get(identity.0 as usize)
                    .is_none_or(|tag| tag.id != *identity)
                {
                    return Err("optional guard lacks its registered immutable tag".into());
                }
                let anchored = facts
                    .channel_messages
                    .iter()
                    .filter(|event| event.sequence < sequence)
                    .any(|event| {
                        let snapshot = match &event.action {
                            ChannelAction::Send { payload, .. }
                            | ChannelAction::Receive { payload, .. } => payload,
                            ChannelAction::TagTest { subject, .. } => subject,
                            _ => return false,
                        };
                        optional_snapshot_has(snapshot, *identity)
                    });
                if !anchored {
                    return Err(
                        "optional guard lacks its preceding physical value observation".into(),
                    );
                }
            }
            GuardLiteral::Transport {
                event,
                producer,
                version,
                ..
            } => {
                let entry = facts
                    .channel_messages
                    .get(event.0 as usize)
                    .filter(|entry| entry.id == *event && entry.sequence < sequence)
                    .ok_or("guard does not refer to a preceding actual transport")?;
                let (transport, versions) = match &entry.action {
                    ChannelAction::Send {
                        transport,
                        producer_versions,
                        ..
                    }
                    | ChannelAction::Receive {
                        transport,
                        producer_versions,
                        ..
                    } => (transport, producer_versions),
                    _ => return Err("guard event is not a transport".into()),
                };
                if !transport.value.outer_results.contains(producer) {
                    // Families/copies retain the same physical event, with an
                    // explicit prior alias edge rather than source matching.
                    if !alias_reaches(
                        facts,
                        *producer,
                        &transport.value.outer_results,
                        sequence,
                        &mut BTreeSet::new(),
                    ) {
                        return Err("guard producer has no actual transport alias".into());
                    }
                } else if versions.get(producer) != Some(version) {
                    return Err("transport guard uses another producer generation".into());
                }
            }
            GuardLiteral::Boolean { evaluation, truth } => {
                let evaluation = facts
                    .condition_evaluations
                    .get(evaluation.0 as usize)
                    .filter(|entry| entry.id == *evaluation)
                    .ok_or("guard boolean was not actually evaluated")?;
                if evaluation.constant.is_some_and(|known| known != *truth) {
                    return Err("guard chooses an impossible constant boolean outcome".into());
                }
            }
            GuardLiteral::Result {
                producer, version, ..
            } => {
                if facts
                    .result_duties
                    .get(*producer as usize)
                    .is_none_or(|duty| duty.id != *producer)
                {
                    return Err("constructor guard lacks its physical Result producer".into());
                }
                let anchored = facts
                    .channel_messages
                    .iter()
                    .filter(|event| event.sequence < sequence)
                    .any(|event| {
                        let (value, versions) = match &event.action {
                            ChannelAction::Send {
                                payload,
                                producer_versions,
                                ..
                            }
                            | ChannelAction::Receive {
                                payload,
                                producer_versions,
                                ..
                            } => (&payload.value, producer_versions),
                            ChannelAction::TagTest {
                                subject,
                                producer_versions,
                                ..
                            } => (&subject.value, producer_versions),
                            ChannelAction::Inspect {
                                value,
                                producer_versions,
                            } => (&value.value, producer_versions),
                            _ => return false,
                        };
                        value.results.contains(producer) && versions.get(producer) == Some(version)
                    });
                if !anchored {
                    return Err(
                        "constructor guard lacks a preceding physical producer/version receipt"
                            .into(),
                    );
                }
            }
        }
    }
    Ok(())
}

fn optional_snapshot_has(
    snapshot: &CopyValueSnapshot,
    identity: ril_compiler_core::ids::OptionalTagId,
) -> bool {
    let mut pending = vec![&snapshot.value];
    pending.extend(
        snapshot
            .nodes
            .iter()
            .flat_map(|node| node.fields.iter().map(|(_, value)| value)),
    );
    let mut work = 4096usize;
    while let Some(value) = pending.pop() {
        if work == 0 {
            return false;
        }
        work -= 1;
        if value.option_identity == Some(identity) {
            return true;
        }
        pending.extend(
            [
                &value.result_payload,
                &value.result_success,
                &value.result_error,
                &value.option_payload,
                &value.variant_payload,
            ]
            .into_iter()
            .flatten()
            .map(|child| child.as_ref()),
        );
    }
    false
}
fn alias_reaches(
    facts: &SemanticFacts,
    producer: u32,
    targets: &BTreeSet<u32>,
    sequence: u64,
    seen: &mut BTreeSet<u32>,
) -> bool {
    if targets.contains(&producer) {
        return true;
    }
    if !seen.insert(producer) || seen.len() > 4096 {
        return false;
    }
    facts
        .channel_messages
        .iter()
        .filter(|event| event.sequence < sequence)
        .any(|event| match &event.action {
            ChannelAction::ResultAliases { map } => map.get(&producer).is_some_and(|old| {
                old.iter()
                    .any(|old| alias_reaches(facts, *old, targets, event.sequence, seen))
            }),
            _ => false,
        })
}

fn snapshot(facts: &SemanticFacts, snapshot: &CopyValueSnapshot) -> Check {
    if !super::channel_production::complete(
        snapshot,
        &facts.external_type_declarations,
        &facts.constructors,
    ) {
        return Err(
            "message payload lacks complete conditional/quantified Result production witnesses"
                .into(),
        );
    }
    let mut pending = vec![&snapshot.value];
    pending.extend(
        snapshot
            .nodes
            .iter()
            .flat_map(|node| node.fields.iter().map(|(_, value)| value)),
    );
    let mut work = 4096_usize;
    while let Some(value) = pending.pop() {
        work = work
            .checked_sub(1)
            .ok_or("frozen message graph exceeds its bound")?;
        if !value.scoped.is_empty()
            || !value.callables.is_empty()
            || value.mutable_environment
            || value.observer_environment
        {
            return Err("message proof contains scoped/resource/callable state".into());
        }
        for producer in value
            .results
            .iter()
            .chain(&value.outer_results)
            .chain(&value.must_results)
            .chain(&value.must_outer_results)
        {
            if facts
                .result_duties
                .get(*producer as usize)
                .is_none_or(|duty| duty.id != *producer)
            {
                return Err("frozen message graph lacks its producer".into());
            }
        }
        if value
            .origins
            .nodes
            .iter()
            .any(|origin| !snapshot.nodes.iter().any(|node| node.origin == *origin))
        {
            return Err("message graph lacks a reachable frozen node".into());
        }
        pending.extend(
            [
                &value.result_payload,
                &value.result_success,
                &value.result_error,
                &value.option_payload,
                &value.variant_payload,
            ]
            .into_iter()
            .flatten()
            .map(|value| value.as_ref()),
        );
        pending.extend(value.variant_witnesses.values().map(|value| value.as_ref()));
    }
    Ok(())
}

impl Replay {
    fn advance(&mut self, facts: &SemanticFacts, epoch: usize) -> Check {
        if epoch < self.epoch {
            return Err("actual event epochs moved backwards".into());
        }
        for &(recent, older) in &facts.allocation_history[self.epoch..epoch] {
            for case in &mut self.cases {
                let remap = |anchor: &ChannelAnchor| match anchor {
                    ChannelAnchor::Known { channel, scope } => ChannelAnchor::Known {
                        channel: if *channel == recent { older } else { *channel },
                        scope: if *scope == recent { older } else { *scope },
                    },
                    ChannelAnchor::Formal { endpoint, scope } => ChannelAnchor::Formal {
                        endpoint: if *endpoint == recent {
                            older
                        } else {
                            *endpoint
                        },
                        scope: if *scope == recent { older } else { *scope },
                    },
                };
                let mut queues = BTreeMap::new();
                for (anchor, packets) in std::mem::take(&mut case.queues) {
                    if queues.insert(remap(&anchor), packets).is_some() {
                        return Err("recency merges distinct pending channel queues".into());
                    }
                }
                case.queues = queues;
                case.closed = case.closed.iter().map(remap).collect();
                for custody in case.custody.values_mut() {
                    if let Custody::Channel(anchor) = custody {
                        *anchor = remap(anchor);
                    }
                }
                // A repeated task identity needs a multiplicity-aware clock;
                // merging two actors must never invent happens-before.
                if case.clocks.contains_key(&Some(recent)) && case.clocks.contains_key(&Some(older))
                {
                    return Err("recency merges distinct task clock identities".into());
                }
                if let Some(clock) = case.clocks.remove(&Some(recent)) {
                    case.clocks.insert(Some(older), clock);
                }
                for clock in case.clocks.values_mut().chain(
                    case.queues
                        .values_mut()
                        .flatten()
                        .map(|packet| &mut packet.clock),
                ) {
                    if let Some(time) = clock.remove(&Some(recent))
                        && clock.insert(Some(older), time).is_some()
                    {
                        return Err("recency merges distinct causal clock coordinates".into());
                    }
                }
                if let Some(parent) = case.tasks.remove(&recent) {
                    case.tasks.insert(older, parent);
                }
                for parent in case.tasks.values_mut() {
                    if *parent == Some(recent) {
                        *parent = Some(older);
                    }
                }
            }
        }
        self.epoch = epoch;
        Ok(())
    }

    fn record(
        &mut self,
        facts: &SemanticFacts,
        record: Record<'_>,
        condition_truth: Option<bool>,
    ) -> Check {
        #[cfg(test)]
        let _state_observer = state_observer::Capture::begin(facts, record, self.cases.len());
        let guard = record_guard(record);
        if let Record::Event(event) = record {
            match &event.action {
                ChannelAction::Send {
                    transport,
                    producer_versions,
                    ..
                }
                | ChannelAction::Receive {
                    transport,
                    producer_versions,
                    ..
                } => {
                    for producer in &transport.value.outer_results {
                        self.aliases.entry(*producer).or_default().insert(event.id);
                    }
                    for (&producer, &version) in producer_versions {
                        if self
                            .versions
                            .insert(producer, version)
                            .is_some_and(|old| old != version)
                        {
                            return Err(
                                "actual transport reuses another business producer generation"
                                    .into(),
                            );
                        }
                    }
                }
                ChannelAction::ResultAliases { map } => {
                    for (new, old) in map {
                        if old.len() == 1
                            && let Some(outcomes) = self.outcomes.get(old.first().unwrap()).cloned()
                        {
                            self.outcomes.insert(*new, outcomes);
                        } else if old.len() == 1
                            && let Some(old) = old.first().filter(|old| self.business.contains(old))
                            && !self.aliases.contains_key(old)
                            && self.cases.iter().any(|case| case.guard.terms.iter().flatten().any(|literal| matches!(literal, GuardLiteral::Result { producer, .. } if producer == old)))
                        {
                            let outcomes = [false, true].map(|success| {
                                ChannelGuard::literal(GuardLiteral::Result {
                                    producer: *old,
                                    version: self.versions.get(old).copied().unwrap_or(0),
                                    success,
                                })
                            });
                            self.outcomes.insert(*new, outcomes);
                        } else if old.len() > 1
                            && old.iter().any(|member| self.aliases.contains_key(member))
                        {
                            let outcomes = self.family_outcomes(facts, event, old)?;
                            self.outcomes.insert(*new, outcomes);
                        }
                        let events = old
                            .iter()
                            .filter_map(|old| self.aliases.get(old))
                            .flatten()
                            .copied()
                            .collect::<BTreeSet<_>>();
                        if !events.is_empty() {
                            self.aliases.insert(*new, events);
                        }
                    }
                }
                _ => {}
            }
        }
        let mut next = Vec::new();
        for case in std::mem::take(&mut self.cases) {
            let mut active = case
                .guard
                .and(guard)
                .ok_or("bounded event intersection is unavailable")?;
            active.terms.retain(|term| {
                term.iter().all(|literal| match literal {
                    GuardLiteral::Transport { event, .. } => case.executed.contains(event),
                    GuardLiteral::Boolean { .. }
                    | GuardLiteral::Result { .. }
                    | GuardLiteral::Optional { .. } => true,
                })
            });
            #[cfg(test)]
            let _guard_metrics = metrics::Capture::begin(
                record.sequence(),
                match record {
                    Record::Event(event) => Some(event.id),
                    Record::Exit(_) => None,
                },
                &case.guard,
                guard,
                &case.executed,
            );
            let inactive = case
                .guard
                .and(
                    &guard
                        .not()
                        .ok_or("bounded event complement is unavailable")?,
                )
                .ok_or("bounded inactive event intersection is unavailable")?;
            #[cfg(test)]
            drop(_guard_metrics);
            if !inactive.is_never() {
                let mut preserved = case.clone();
                preserved.guard = inactive;
                next.push(preserved);
            }
            if active.is_never() {
                continue;
            }
            let mut active_case = case;
            active_case.guard = active;
            match record {
                Record::Event(event) => {
                    self.event(facts, active_case, event, condition_truth, &mut next)?
                }
                Record::Exit(exit) => {
                    self.exit(facts, &mut active_case, exit)?;
                    next.push(active_case);
                }
            }
            if next.len() > 256 {
                next = merge_cases(next)?;
            }
        }
        self.cases = merge_cases(next)?;
        Ok(())
    }

    fn event(
        &self,
        facts: &SemanticFacts,
        mut case: Case,
        event: &ChannelMessageFact,
        condition_truth: Option<bool>,
        next: &mut Vec<Case>,
    ) -> Check {
        if event
            .task
            .is_some_and(|task| !case.tasks.contains_key(&task))
        {
            return Err("event executing task has no preceding actual fork".into());
        }
        match &event.action {
            ChannelAction::TaskFork { child } => {
                if case.tasks.insert(*child, event.task).is_some() {
                    return Err("actual child was forked twice".into());
                }
                let clock = tick(&mut case.clocks, event.task)?;
                case.clocks.insert(Some(*child), clock);
            }
            ChannelAction::TaskJoin { child } => {
                if case.tasks.get(child) != Some(&event.task) {
                    return Err("join does not belong to its actual fork parent".into());
                }
                let child = case
                    .clocks
                    .get(&Some(*child))
                    .cloned()
                    .ok_or("join lacks the child's actual clock")?;
                merge_clock(case.clocks.entry(event.task).or_default(), &child);
                tick(&mut case.clocks, event.task)?;
            }
            ChannelAction::Send {
                anchor,
                payload,
                transport,
                original_owners,
                ..
            } => {
                snapshot(facts, payload)?;
                case.executed.insert(event.id);
                if payload.value.results.is_empty() {
                    next.push(case);
                    return Ok(());
                }
                let production = super::channel_production::cases(payload, &self.versions)
                    .ok_or("conditional send production cases are incomplete")?;
                for contents in production {
                    let mut case = case.clone();
                    case.guard = case
                        .guard
                        .and(&contents.guard)
                        .ok_or("conditional send case bound exceeded")?;
                    if case.guard.is_never() {
                        continue;
                    }
                    for producer in &contents.producers {
                        let duty = facts
                            .result_duties
                            .get(*producer as usize)
                            .ok_or("message lacks its original producer registry entry")?;
                        let owner = *case.owners.entry(*producer).or_insert(duty.creation_owner);
                        if original_owners.get(producer) != Some(&owner) {
                            return Err(
                                "first send owner lacks an actual historical transfer".into()
                            );
                        }
                        case.custody
                            .entry(*producer)
                            .or_insert(Custody::Caller(owner));
                    }
                    for success in [false, true] {
                        if success && case.closed.contains(anchor) {
                            continue;
                        }
                        let mut branch = case.clone();
                        branch.guard = branch
                            .guard
                            .and(&self.outcome(event.id, transport, success)?)
                            .ok_or("send outcome bound exceeded")?;
                        if branch.guard.is_never() {
                            continue;
                        }
                        if success {
                            for producer in &contents.producers {
                                branch
                                    .custody
                                    .insert(*producer, Custody::Channel(anchor.clone()));
                                branch.returned.remove(producer);
                            }
                            let clock = tick(&mut branch.clocks, event.task)?;
                            let queue = branch.queues.entry(anchor.clone()).or_default();
                            if queue.len() >= 4096 {
                                return Err("independent message queue exceeds its bound".into());
                            }
                            queue.push(Packet {
                                send: event.id,
                                producers: contents.producers.clone(),
                                clock,
                            });
                        }
                        next.push(branch);
                    }
                }
                return Ok(());
            }
            ChannelAction::Receive {
                anchor,
                payload,
                transport,
                sources,
                ..
            } => {
                snapshot(facts, payload)?;
                case.executed.insert(event.id);
                if payload.value.results.is_empty() {
                    next.push(case);
                    return Ok(());
                }
                let queue = case.queues.get(anchor).cloned().unwrap_or_default();
                if let Some(first) = queue.first()
                    && queue
                        .iter()
                        .skip(1)
                        .any(|other| !before(&first.clock, &other.clock))
                {
                    return Err("receive assumes global order between incomparable senders".into());
                }
                let production = super::channel_production::cases(payload, &self.versions)
                    .ok_or("conditional receive production cases are incomplete")?;
                for contents in production {
                    let mut case = case.clone();
                    case.guard = case
                        .guard
                        .and(&contents.guard)
                        .ok_or("conditional receive case bound exceeded")?;
                    if case.guard.is_never() {
                        continue;
                    }
                    for success in [false, true] {
                        if matches!(anchor, ChannelAnchor::Known { .. })
                            && success != !queue.is_empty()
                        {
                            continue;
                        }
                        let mut branch = case.clone();
                        branch.guard = branch
                            .guard
                            .and(&self.outcome(event.id, transport, success)?)
                            .ok_or("receive outcome bound exceeded")?;
                        if branch.guard.is_never() {
                            continue;
                        }
                        if success {
                            let source = queue.first().map(|packet| packet.send);
                            let claims = sources
                                .iter()
                                .filter(|claim| claim.send == source)
                                .try_fold(ChannelGuard::never(), |guard, claim| {
                                    guard.or(&claim.guard)
                                })
                                .ok_or("receive source coverage exceeds its bound")?;
                            if !branch
                                .guard
                                .and(
                                    &claims
                                        .not()
                                        .ok_or("receive source complement unavailable")?,
                                )
                                .ok_or("receive source implication unavailable")?
                                .is_never()
                            {
                                return Err("receive claims another message or lacks its successful source case".into());
                            }
                            let producers = queue
                                .first()
                                .map(|packet| &packet.producers)
                                .unwrap_or(&contents.producers);
                            if producers != &contents.producers {
                                return Err(
                                    "receive payload aliases a different submitted Result".into()
                                );
                            }
                            for producer in producers {
                                branch
                                    .custody
                                    .insert(*producer, Custody::Caller(event.activation));
                                branch.returned.remove(producer);
                            }
                            if let Some(packet) = queue.first() {
                                merge_clock(
                                    branch.clocks.entry(event.task).or_default(),
                                    &packet.clock,
                                );
                                tick(&mut branch.clocks, event.task)?;
                                branch.queues.get_mut(anchor).unwrap().remove(0);
                            }
                        }
                        next.push(branch);
                    }
                }
                return Ok(());
            }
            ChannelAction::Inspect {
                value,
                producer_versions,
            } => {
                for producer in family(facts, &value.value.must_outer_results)? {
                    if self.versions.get(&producer).is_none_or(|version| {
                        producer_versions
                            .get(&producer)
                            .is_none_or(|actual| actual == version)
                    }) {
                        case.inspected.insert(producer);
                    }
                }
            }
            ChannelAction::Select { evaluation, truth } => {
                let proof = facts
                    .condition_evaluations
                    .get(evaluation.0 as usize)
                    .ok_or("selection lacks its actual evaluated boolean")?;
                for producer in family(facts, proof.inspections.outcome(*truth))? {
                    if proof
                        .inspections
                        .versions
                        .get(&producer)
                        .is_some_and(|version| {
                            self.versions
                                .get(&producer)
                                .is_none_or(|actual| version == actual)
                        })
                    {
                        case.inspected.insert(producer);
                    }
                }
            }
            ChannelAction::ResultTransfer {
                from,
                to,
                source,
                producers,
            } => {
                let producers = producers
                    .intersection(&self.business)
                    .copied()
                    .collect::<BTreeSet<_>>();
                if producers.is_empty() {
                    next.push(case);
                    return Ok(());
                }
                let members = family(facts, &source.value.results)?;
                if producers.is_empty() || from == to || !producers.is_subset(&members) {
                    return Err(
                        "owner transition lacks the frozen carrier's actual producer membership"
                            .into(),
                    );
                }
                transfer_evidence(facts, event, *from, source, &producers, &case, self)?;
                for producer in &producers {
                    let creation = facts
                        .result_duties
                        .get(*producer as usize)
                        .ok_or("transfer lacks producer registry")?
                        .creation_owner;
                    let current = case.owners.entry(*producer).or_insert(creation);
                    if current != from {
                        return Err(
                            "owner transition does not start at this actual historical owner"
                                .into(),
                        );
                    }
                    *current = *to;
                    if case.custody.get(producer) == Some(&Custody::Caller(*from)) {
                        case.custody.insert(*producer, Custody::Caller(*to));
                    }
                    case.returned.remove(producer);
                }
            }
            ChannelAction::ConditionEvaluated { evaluation, .. } => {
                if let Some(truth) = condition_truth {
                    case.guard = case
                        .guard
                        .and(&ChannelGuard::literal(GuardLiteral::Boolean {
                            evaluation: *evaluation,
                            truth,
                        }))
                        .ok_or("complete evaluated Boolean refinement exceeds its work bound")?;
                    if case.guard.is_never() {
                        return Ok(());
                    }
                }
            }
            ChannelAction::TagTest { .. } => {}
            ChannelAction::ResultAliases { map } => {
                for (new, old) in map {
                    if old.len() == 1
                        && old.iter().any(|old| case.custody.contains_key(old))
                        && !facts.result_families.contains_key(new)
                    {
                        let owner = facts
                            .result_duties
                            .get(*new as usize)
                            .ok_or("copy alias lacks its new producer")?
                            .creation_owner;
                        case.custody.insert(*new, Custody::Caller(owner));
                    }
                }
            }
        }
        next.push(case);
        Ok(())
    }
    fn outcome(
        &self,
        event: ChannelMessageId,
        transport: &CopyValueSnapshot,
        success: bool,
    ) -> Check<ChannelGuard> {
        let producer = *transport
            .value
            .outer_results
            .first()
            .ok_or("transport lacks its own producer")?;
        if transport.value.outer_results.len() != 1 {
            return Err("transport has an unresolved one-of producer family".into());
        }
        Ok(ChannelGuard::literal(GuardLiteral::Transport {
            event,
            producer,
            version: self.versions.get(&producer).copied().unwrap_or(0),
            success,
        }))
    }
    fn family_outcomes(
        &self,
        facts: &SemanticFacts,
        event: &ChannelMessageFact,
        members: &BTreeSet<u32>,
    ) -> Check<[ChannelGuard; 2]> {
        let mut result = [ChannelGuard::never(), ChannelGuard::never()];
        for member in members {
            let receipts = facts
                .channel_exits
                .iter()
                .filter(|receipt| {
                    receipt.activation == event.activation
                        && receipt.sequence < event.sequence
                        && matches!(
                            receipt.kind,
                            ChannelExitKind::Callable | ChannelExitKind::Return
                        )
                        && receipt.returned.value.must_outer_results.contains(member)
                })
                .collect::<Vec<_>>();
            if receipts.is_empty() {
                return Err("one-of transport family lacks its actual member receipt".into());
            }
            for receipt in receipts {
                let value = &receipt.returned.value;
                if value.outer_results.len() != 1 {
                    return Err("family receipt has an unresolved outer member".into());
                }
                for success in [false, true] {
                    let selection = if let Some(known) = value.result_tag {
                        if known == success {
                            ChannelGuard::always()
                        } else {
                            ChannelGuard::never()
                        }
                    } else if let Some(outcomes) = self.outcomes.get(member) {
                        outcomes[usize::from(success)].clone()
                    } else {
                        let events = self
                            .aliases
                            .get(member)
                            .ok_or("unknown returned tag has no physical event")?;
                        if events.len() != 1 {
                            return Err(
                                "returned tag has unresolved physical event alternatives".into()
                            );
                        }
                        ChannelGuard::literal(GuardLiteral::Transport {
                            event: *events.first().unwrap(),
                            producer: *member,
                            version: self.versions.get(member).copied().unwrap_or(0),
                            success,
                        })
                    };
                    let selected = receipt
                        .guard
                        .and(&selection)
                        .ok_or("family tag selection bound exceeded")?;
                    result[usize::from(success)] = result[usize::from(success)]
                        .or(&selected)
                        .ok_or("family member union bound exceeded")?;
                }
            }
        }
        if !result[0]
            .and(&result[1])
            .ok_or("family tag overlap bound exceeded")?
            .is_never()
        {
            return Err("one physical family occurrence chooses conflicting tags".into());
        }
        let all = result[0]
            .or(&result[1])
            .ok_or("family receipt coverage bound exceeded")?;
        if !event
            .guard
            .and(
                &all.not()
                    .ok_or("family receipt complement bound exceeded")?,
            )
            .ok_or("family receipt implication bound exceeded")?
            .is_never()
        {
            return Err("family receipts omit a completed actual return case".into());
        }
        Ok(result)
    }
    fn exit(&self, facts: &SemanticFacts, case: &mut Case, exit: &ChannelExitFact) -> Check {
        if exit.kind == ChannelExitKind::Complete {
            return Ok(());
        }
        let returned = present(&exit.returned, case, self)?;
        for producer in &returned {
            if case.custody.contains_key(producer) {
                case.returned.insert(*producer, exit.activation);
            }
        }
        if exit.kind == ChannelExitKind::Abnormal {
            if !exit.returned.value.abnormal {
                return Err("business Err is not a cancellation/abnormal receipt".into());
            }
            return Ok(());
        }
        match exit.kind {
            ChannelExitKind::Receiver | ChannelExitKind::Scope => {
                let anchor = exit
                    .anchor
                    .as_ref()
                    .ok_or("channel completion lacks its actual scope/receiver")?;
                let anchors = case
                    .queues
                    .keys()
                    .filter(|actual| {
                        if exit.kind == ChannelExitKind::Receiver {
                            *actual == anchor
                        } else {
                            anchor_scope(actual) == anchor_scope(anchor)
                        }
                    })
                    .cloned()
                    .collect::<Vec<_>>();
                for anchor in anchors {
                    for packet in case.queues.remove(&anchor).unwrap_or_default() {
                        for producer in packet.producers {
                            if returned.contains(&producer) && exit.kind == ChannelExitKind::Scope {
                                case.custody
                                    .insert(producer, Custody::Caller(exit.activation));
                            } else if !case.inspected.contains(&producer)
                                && !case.returned.contains_key(&producer)
                            {
                                return Err(
                                    "normal completion loses an unread uninspected business Result"
                                        .into(),
                                );
                            }
                        }
                    }
                    case.closed.insert(anchor);
                }
                if exit.kind == ChannelExitKind::Receiver {
                    case.closed.insert(anchor.clone());
                }
            }
            ChannelExitKind::Callable | ChannelExitKind::Return => {
                if case.custody.iter().any(|(producer, custody)| {
                    *custody == Custody::Caller(exit.activation)
                        && !case.inspected.contains(producer)
                        && case.returned.get(producer) != Some(&exit.activation)
                }) {
                    return Err("ordinary caller completion loses its business Result".into());
                }
            }
            ChannelExitKind::Abnormal => unreachable!(),
            ChannelExitKind::Complete => unreachable!(),
        }
        let _ = facts;
        Ok(())
    }
}

fn family(facts: &SemanticFacts, roots: &BTreeSet<u32>) -> Check<BTreeSet<u32>> {
    let mut result = BTreeSet::new();
    let mut pending = roots.iter().copied().collect::<Vec<_>>();
    while let Some(producer) = pending.pop() {
        if result.insert(producer) {
            if result.len() > 4096 {
                return Err("producer family exceeds its bound".into());
            }
            if let Some(children) = facts.result_families.get(&producer) {
                pending.extend(children);
            }
        }
    }
    Ok(result)
}
fn transfer_evidence(
    facts: &SemanticFacts,
    event: &ChannelMessageFact,
    from: ScopeId,
    source: &CopyValueSnapshot,
    producers: &BTreeSet<u32>,
    case: &Case,
    replay: &Replay,
) -> Check {
    if from == ScopeId(u32::MAX) {
        if facts.external_instances.iter().any(|external| {
            external
                .sites
                .contains(&(event.span.file.0, event.span.start, event.span.end))
        }) {
            return Ok(());
        }
        return Err("outside producer adoption lacks its actual external return reception".into());
    }
    if facts.channel_exits.iter().any(|exit| {
        exit.sequence < event.sequence
            && exit.activation == from
            && matches!(
                exit.kind,
                ChannelExitKind::Callable | ChannelExitKind::Return
            )
            && case
                .guard
                .and(&exit.guard.not().unwrap_or_else(ChannelGuard::unavailable))
                .is_some_and(|missing| missing.is_never())
            && present(&exit.returned, case, replay)
                .is_ok_and(|present| producers.is_subset(&present))
    }) {
        return Ok(());
    }
    // Before the first channel observation ordinary calls have no channel exit
    // yet. Their completed actual invocation still freezes its returned value.
    if facts.copy_invocations.iter().any(|invocation| {
        invocation.id
            == event
                .context
                .invocation
                .unwrap_or(super::copy_templates::InstanceId(u32::MAX))
            && invocation.result.as_ref().is_some_and(|result| {
                result.value.cause == source.value.cause
                    && present(result, case, replay)
                        .is_ok_and(|present| producers.is_subset(&present))
            })
    }) {
        return Ok(());
    }
    Err("owner transfer lacks an actual completed return carrier".into())
}
fn tick(clocks: &mut BTreeMap<Option<NodeId>, Clock>, actor: Option<NodeId>) -> Check<Clock> {
    if clocks.len() > 4096 {
        return Err("task clock bound exceeded".into());
    }
    let clock = clocks.entry(actor).or_default();
    let time = clock.entry(actor).or_default();
    *time = time.checked_add(1).ok_or("task clock overflow")?;
    Ok(clock.clone())
}
fn merge_clock(target: &mut Clock, source: &Clock) {
    for (actor, time) in source {
        target
            .entry(*actor)
            .and_modify(|old| *old = (*old).max(*time))
            .or_insert(*time);
    }
}
fn before(a: &Clock, b: &Clock) -> bool {
    a.iter()
        .all(|(actor, time)| *time <= b.get(actor).copied().unwrap_or(0))
        && b.iter()
            .any(|(actor, time)| *time > a.get(actor).copied().unwrap_or(0))
}

fn present(snapshot: &CopyValueSnapshot, case: &Case, replay: &Replay) -> Check<BTreeSet<u32>> {
    fn visit(
        value: &Value,
        snapshot: &CopyValueSnapshot,
        case: &Case,
        replay: &Replay,
        active: &mut BTreeSet<NodeId>,
        work: &mut usize,
    ) -> Check<BTreeSet<u32>> {
        *work = work
            .checked_sub(1)
            .ok_or("returned frozen graph exceeds its bound")?;
        if !value.outer_results.is_empty() {
            let mut result = value.must_outer_results.clone();
            let events = value
                .outer_results
                .iter()
                .filter_map(|producer| replay.aliases.get(producer))
                .flatten()
                .filter(|event| case.executed.contains(event))
                .copied()
                .collect::<BTreeSet<_>>();
            let family = (value.outer_results.len() == 1)
                .then(|| replay.outcomes.get(value.outer_results.first().unwrap()))
                .flatten();
            let physical =
                (events.is_empty() && value.result_tag.is_none() && value.outer_results.len() == 1)
                    .then(|| {
                        let producer = *value.outer_results.first().unwrap();
                        [false, true].map(|success| {
                            ChannelGuard::literal(GuardLiteral::Result {
                                producer,
                                version: replay.versions.get(&producer).copied().unwrap_or(0),
                                success,
                            })
                        })
                    });
            let family = family.or(physical.as_ref());
            let selected = if let Some(outcomes) = family {
                let mut selected = None;
                for success in [false, true] {
                    if case
                        .guard
                        .and(
                            &outcomes[usize::from(success)]
                                .not()
                                .ok_or("family presence complement unavailable")?,
                        )
                        .ok_or("family presence intersection unavailable")?
                        .is_never()
                    {
                        selected = Some(success);
                    }
                }
                selected
            } else if events.len() == 1 {
                let event = *events.first().unwrap();
                [false, true].into_iter().find(|success| case.guard.terms.iter().all(|term| term.iter().any(|literal| matches!(literal, GuardLiteral::Transport { event: actual, success: truth, .. } if *actual == event && truth == success))))
            } else if events.is_empty() {
                value.result_tag
            } else {
                None
            };
            if let Some(success) = selected {
                if let Some(payload) = (if success {
                    value.result_success.as_deref()
                } else {
                    value.result_error.as_deref()
                })
                .or_else(|| {
                    (value.result_tag == Some(success))
                        .then_some(value.result_payload.as_deref())
                        .flatten()
                }) {
                    result.extend(visit(payload, snapshot, case, replay, active, work)?);
                }
            } else if let (Some(ok), Some(error)) = (&value.result_success, &value.result_error) {
                let ok = visit(ok, snapshot, case, replay, active, work)?;
                let error = visit(error, snapshot, case, replay, active, work)?;
                result.extend(ok.intersection(&error));
            }
            return Ok(result);
        }
        if value.option_payload.is_some() || value.option_tag.is_some() {
            let selected = value.option_tag.or_else(|| {
                let identity = value.option_identity?;
                let present = ChannelGuard::literal(GuardLiteral::Optional {
                    identity,
                    present: true,
                });
                case.guard
                    .and(&present.not()?)
                    .filter(|missing| missing.is_never())
                    .map(|_| true)
            });
            return if selected == Some(true) {
                visit(
                    value
                        .option_payload
                        .as_deref()
                        .ok_or("Some return lacks its frozen payload")?,
                    snapshot,
                    case,
                    replay,
                    active,
                    work,
                )
            } else {
                Ok(BTreeSet::new())
            };
        }
        if let Some(payload) = &value.variant_payload {
            return visit(payload, snapshot, case, replay, active, work);
        }
        let mut result: Option<BTreeSet<u32>> = None;
        for origin in &value.origins.nodes {
            if !active.insert(*origin) {
                continue;
            }
            let node = snapshot
                .nodes
                .iter()
                .find(|node| node.origin == *origin)
                .ok_or("returned carrier lacks its frozen field graph")?;
            let mut from = BTreeSet::new();
            for (_, child) in &node.fields {
                from.extend(visit(child, snapshot, case, replay, active, work)?);
            }
            active.remove(origin);
            result = Some(match result {
                None => from,
                Some(previous) => previous.intersection(&from).copied().collect(),
            });
        }
        let mut result = result.unwrap_or_default();
        result.retain(|producer| value.must_results.contains(producer));
        Ok(result)
    }
    visit(
        &snapshot.value,
        snapshot,
        case,
        replay,
        &mut BTreeSet::new(),
        &mut 4096,
    )
}
