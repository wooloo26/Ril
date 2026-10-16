//! Test-only prefix observation at the actual record-sequence-957 overflow.
//! It never changes a Case, computes a permission, drops a field or changes 256.
use super::{
    Case, ChannelAction, ChannelAnchor, ChannelGuard, ChannelMessageFact, Custody, GuardLiteral,
    NodeId, Packet, Record, SemanticFacts,
};
use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet},
};

struct Metadata {
    booleans: BTreeMap<u32, serde_json::Value>,
    events: BTreeMap<u32, serde_json::Value>,
    producers: BTreeMap<u32, serde_json::Value>,
    actors: BTreeMap<NodeId, serde_json::Value>,
    anchors: BTreeMap<ChannelAnchor, serde_json::Value>,
    future_guard_refs: BTreeMap<u32, usize>,
}

fn event_source(event: &ChannelMessageFact) -> serde_json::Value {
    let action = match &event.action {
        ChannelAction::TaskFork { .. } => "TaskFork",
        ChannelAction::TaskJoin { .. } => "TaskJoin",
        ChannelAction::Send { .. } => "Send",
        ChannelAction::Receive { .. } => "Receive",
        ChannelAction::TagTest { .. } => "TagTest",
        ChannelAction::ConditionEvaluated { .. } => "ConditionEvaluated",
        ChannelAction::Inspect { .. } => "Inspect",
        ChannelAction::Select { .. } => "Select",
        ChannelAction::ResultAliases { .. } => "ResultAliases",
        ChannelAction::ResultTransfer { .. } => "ResultTransfer",
    };
    serde_json::json!({
        "record_sequence":event.sequence,"actual_channel_message_id":event.id.0,"action":action,
        "source_application_id":event.source_event.map(|id|id.0),
        "context":format!("{:?}",event.context),"activation":event.activation.0,
        "task":event.task.map(|id|id.0),"allocation_epoch":event.allocation_epoch,
        "source_span":{"file":event.span.file.0,"start":event.span.start,"end":event.span.end},"cause":event.cause.0,
    })
}

impl Metadata {
    fn snapshot(facts: &SemanticFacts, sequence: u64) -> Self {
        // Small immutable source summaries only: no heap graph, Case, final
        // inspection/ownership flags or authority certificate is cloned.
        let booleans = facts.condition_evaluations.iter().map(|evaluation| (evaluation.id.0, serde_json::json!({
            "evaluation":evaluation.id.0,"kind":format!("{:?}",evaluation.kind),
            "recorded_constant":evaluation.constant,"actual_context":format!("{:?}",evaluation.context),
            "source_span":{"file":evaluation.span.file.0,"start":evaluation.span.start,"end":evaluation.span.end},
            "cause":evaluation.cause.0,"is_independent_source_truth_proof":false,
        }))).collect();
        let producers = facts.result_duties.iter().map(|duty| (duty.id, serde_json::json!({
            "producer":duty.id,"immutable_creation_owner":duty.creation_owner.0,
            "source_span":{"file":duty.span.file.0,"start":duty.span.start,"end":duty.span.end},
            "cause":duty.cause.0,"borrow_or_current_ownership_proof":false,
        }))).collect();
        let mut result = Self {
            booleans,
            producers,
            events: BTreeMap::new(),
            actors: BTreeMap::new(),
            anchors: BTreeMap::new(),
            future_guard_refs: BTreeMap::new(),
        };
        for event in &facts.channel_messages {
            let source = event_source(event);
            result.events.insert(event.id.0, source.clone());
            if event.sequence < sequence {
                if let Some(actor) = event.task {
                    result.actors.insert(actor, source.clone());
                }
                match &event.action {
                    ChannelAction::TaskFork { child } | ChannelAction::TaskJoin { child } => {
                        result.actors.insert(*child, source.clone());
                    }
                    ChannelAction::Send { anchor, .. } | ChannelAction::Receive { anchor, .. } => {
                        result.anchors.insert(anchor.clone(), source);
                    }
                    _ => {}
                }
            }
        }
        for exit in facts
            .channel_exits
            .iter()
            .filter(|exit| exit.sequence < sequence)
        {
            if let Some(anchor) = &exit.anchor {
                let newer = result
                    .anchors
                    .get(anchor)
                    .and_then(|source| source["record_sequence"].as_u64())
                    .is_none_or(|previous| previous < exit.sequence);
                if newer {
                    result.anchors.insert(anchor.clone(), serde_json::json!({
                        "record_sequence":exit.sequence,"actual_channel_message_id":null,
                        "exit_kind":format!("{:?}",exit.kind),"activation":exit.activation.0,
                        "context":format!("{:?}",exit.context),"cause":exit.cause.0,
                        "source_span":{"file":exit.span.file.0,"start":exit.span.start,"end":exit.span.end},
                    }));
                }
            }
        }
        for guard in facts
            .channel_messages
            .iter()
            .filter(|event| event.sequence > sequence)
            .map(|event| &event.guard)
            .chain(
                facts
                    .channel_exits
                    .iter()
                    .filter(|exit| exit.sequence > sequence)
                    .map(|exit| &exit.guard),
            )
        {
            for literal in guard.terms.iter().flatten() {
                if let GuardLiteral::Transport { event, .. } = literal {
                    *result.future_guard_refs.entry(event.0).or_default() += 1;
                }
            }
        }
        result
    }
}

struct Observation {
    header: serde_json::Value,
    metadata: Metadata,
    merge_ordinal: usize,
    input_cases: usize,
    processed: usize,
    emitted: bool,
}
thread_local! { static ACTIVE: RefCell<Option<Observation>> = const { RefCell::new(None) }; }

pub(super) struct Capture(bool);
impl Capture {
    pub(super) fn begin(facts: &SemanticFacts, record: Record<'_>, cases: usize) -> Self {
        if record.sequence() != 957 {
            return Self(false);
        }
        ACTIVE.with(|active| {
            let mut active=active.borrow_mut();
            if active.is_some() { return Self(false); }
            let header=match record {
                Record::Event(event)=>event_source(event),
                Record::Exit(exit)=>serde_json::json!({"record_sequence":exit.sequence,"actual_channel_message_id":null,
                    "exit_kind":format!("{:?}",exit.kind),"context":format!("{:?}",exit.context),"activation":exit.activation.0,
                    "allocation_epoch":exit.allocation_epoch,"cause":exit.cause.0,
                    "source_span":{"file":exit.span.file.0,"start":exit.span.start,"end":exit.span.end}}),
            };
            *active=Some(Observation { header:serde_json::json!({"record":header,"cases_after_epoch_advance_before_record":cases}),
                metadata:Metadata::snapshot(facts,record.sequence()),merge_ordinal:0,input_cases:0,processed:0,emitted:false });
            Self(true)
        })
    }
}
impl Drop for Capture {
    fn drop(&mut self) {
        if self.0 {
            ACTIVE.with(|active| {
                active.borrow_mut().take();
            });
        }
    }
}
pub(super) fn merge_begin(input_cases: usize) {
    ACTIVE.with(|active| {
        if let Some(observation) = active.borrow_mut().as_mut() {
            observation.merge_ordinal += 1;
            observation.input_cases = input_cases;
            observation.processed = 0;
        }
    });
}
pub(super) fn input_processed() {
    ACTIVE.with(|active| {
        if let Some(observation) = active.borrow_mut().as_mut() {
            observation.processed += 1;
        }
    });
}
pub(super) fn overflow(states: &BTreeMap<Case, ChannelGuard>) {
    ACTIVE.with(|active| {
        let mut active = active.borrow_mut();
        let Some(observation) = active.as_mut() else {
            return;
        };
        if observation.emitted || states.len() != 257 {
            return;
        }
        observation.emitted = true;
        let mut report = prefix_report(
            observation.merge_ordinal,
            observation.input_cases,
            observation.processed,
            states,
            &observation.metadata,
        );
        report["actual_record_context"] = observation.header.clone();
        report["few_exact_difference_witnesses"] =
            difference_witnesses(states, &observation.metadata);
        eprintln!("channel-state-metrics {report}");
    });
}

fn prefix_report(
    merge_ordinal: usize,
    input_cases: usize,
    processed_input_prefix: usize,
    states: &BTreeMap<Case, ChannelGuard>,
    metadata: &Metadata,
) -> serde_json::Value {
    // Reference tuples compare the actual full fields. No hash or projected
    // equality result is used to modify the original states.
    macro_rules! distinct {
        ($($field:ident),+ $(,)?) => {
            states.keys().map(|case| ($(&case.$field,)+)).collect::<BTreeSet<_>>().len()
        };
    }
    let booleans = states
        .values()
        .flat_map(|guard| guard.terms.iter().flatten())
        .filter_map(|literal| match literal {
            GuardLiteral::Boolean { evaluation, .. } => Some(*evaluation),
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    let boolean_rows = booleans
        .iter()
        .take(256)
        .map(|identity| {
            metadata.booleans.get(&identity.0).cloned().unwrap_or_else(
                || serde_json::json!({"evaluation":identity.0,"missing_registry_entry":true}),
            )
        })
        .collect::<Vec<_>>();
    serde_json::json!({
        "record_sequence": 957,
        "merge_ordinal_in_record": merge_ordinal,
        "input_cases": input_cases,
        "processed_input_prefix": processed_input_prefix,
        "unprocessed_input_suffix": input_cases.saturating_sub(processed_input_prefix),
        "unique_complete_prefix_states": states.len(),
        "complete_merge_output_available": false,
        "original_replay_case_limit": 256,
        "field_value_counts": {
            "custody":distinct!(custody), "owners":distinct!(owners),
            "inspected":distinct!(inspected), "returned":distinct!(returned),
            "queues":distinct!(queues), "closed":distinct!(closed),
            "clocks":distinct!(clocks), "tasks":distinct!(tasks), "executed":distinct!(executed),
        },
        "one_field_omission_counts_diagnostic_only": {
            "custody":distinct!(owners,inspected,returned,queues,closed,clocks,tasks,executed),
            "owners":distinct!(custody,inspected,returned,queues,closed,clocks,tasks,executed),
            "inspected":distinct!(custody,owners,returned,queues,closed,clocks,tasks,executed),
            "returned":distinct!(custody,owners,inspected,queues,closed,clocks,tasks,executed),
            "queues":distinct!(custody,owners,inspected,returned,closed,clocks,tasks,executed),
            "closed":distinct!(custody,owners,inspected,returned,queues,clocks,tasks,executed),
            "clocks":distinct!(custody,owners,inspected,returned,queues,closed,tasks,executed),
            "tasks":distinct!(custody,owners,inspected,returned,queues,closed,clocks,executed),
            "executed":distinct!(custody,owners,inspected,returned,queues,closed,clocks,tasks),
        },
        "joint_obligation_related_field_values":distinct!(custody,owners,inspected,returned,queues),
        "joint_possible_history_field_values_not_proven_dead":distinct!(closed,clocks,tasks,executed),
        "boolean_atom_count": booleans.len(),
        "boolean_rows": boolean_rows,
        "boolean_rows_truncated": booleans.len() > 256,
        "liveness_classification": "live-or-unknown until independently reviewed",
        "compression_or_authorization": false,
    })
}

fn first_map_key<'a, K: Ord, V: PartialEq>(
    left: &'a BTreeMap<K, V>,
    right: &'a BTreeMap<K, V>,
) -> Option<&'a K> {
    left.keys()
        .chain(right.keys())
        .find(|key| left.get(*key) != right.get(*key))
}
fn anchor(anchor: &ChannelAnchor) -> serde_json::Value {
    match anchor {
        ChannelAnchor::Known { channel, scope } => {
            serde_json::json!({"kind":"Known","channel":channel.0,"scope":scope.0})
        }
        ChannelAnchor::Formal { endpoint, scope } => {
            serde_json::json!({"kind":"Formal","endpoint":endpoint.0,"scope":scope.0})
        }
    }
}
fn custody(value: Option<&Custody>) -> serde_json::Value {
    match value {
        Some(Custody::Caller(owner)) => serde_json::json!({"kind":"Caller","scope":owner.0}),
        Some(Custody::Channel(channel)) => {
            serde_json::json!({"kind":"Channel","anchor":anchor(channel)})
        }
        None => serde_json::Value::Null,
    }
}
fn packet(value: Option<&Packet>, metadata: &Metadata) -> serde_json::Value {
    let Some(value) = value else {
        return serde_json::Value::Null;
    };
    serde_json::json!({"send":value.send.0,"producer_count":value.producers.len(),
        "producer_sample":value.producers.iter().take(8).collect::<Vec<_>>(),
        "clock_coordinate_count":value.clock.len(),
        "clock_sample":value.clock.iter().take(8).map(|(actor,time)|(actor.map(|id|id.0),*time)).collect::<Vec<_>>(),
        "samples_truncated":value.producers.len()>8 || value.clock.len()>8,
        "source":metadata.events.get(&value.send.0)})
}
fn guard_sample(guard: &ChannelGuard) -> serde_json::Value {
    serde_json::json!({"clauses":guard.terms.len(),
        "literal_count":guard.terms.iter().map(|term|term.len()).sum::<usize>(),
        "sample":guard.terms.iter().take(2).map(|term|term.iter().take(4).map(|literal|format!("{literal:?}")).collect::<Vec<_>>()).collect::<Vec<_>>(),
        "sample_truncated":guard.terms.len()>2 || guard.terms.iter().any(|term|term.len()>4)})
}

fn difference(field: &str, left: &Case, right: &Case, metadata: &Metadata) -> serde_json::Value {
    match field {
        "custody" => {
            let key = first_map_key(&left.custody, &right.custody).unwrap();
            serde_json::json!({"producer":key,"left":custody(left.custody.get(key)),"right":custody(right.custody.get(key)),"creation_source":metadata.producers.get(key)})
        }
        "owners" | "returned" => {
            let (left, right) = if field == "owners" {
                (&left.owners, &right.owners)
            } else {
                (&left.returned, &right.returned)
            };
            let key = first_map_key(left, right).unwrap();
            serde_json::json!({"producer":key,"left_scope":left.get(key).map(|id|id.0),"right_scope":right.get(key).map(|id|id.0),"creation_source":metadata.producers.get(key)})
        }
        "inspected" => {
            let key = left
                .inspected
                .symmetric_difference(&right.inspected)
                .next()
                .unwrap();
            serde_json::json!({"producer":key,"left":left.inspected.contains(key),"right":right.inspected.contains(key),"creation_source":metadata.producers.get(key),"universal_payment_proven":false})
        }
        "queues" => {
            let key = first_map_key(&left.queues, &right.queues).unwrap();
            let a = left.queues.get(key).map(Vec::as_slice).unwrap_or(&[]);
            let b = right.queues.get(key).map(Vec::as_slice).unwrap_or(&[]);
            let index = (0..a.len().max(b.len())).find(|&index| a.get(index) != b.get(index));
            serde_json::json!({"anchor":anchor(key),"left_queue_present":left.queues.contains_key(key),"right_queue_present":right.queues.contains_key(key),
                "left_length":a.len(),"right_length":b.len(),"first_changed_packet":index,
                "left_packet":packet(index.and_then(|index|a.get(index)),metadata),"right_packet":packet(index.and_then(|index|b.get(index)),metadata),
                "preceding_anchor_source":metadata.anchors.get(key)})
        }
        "closed" => {
            let key = left
                .closed
                .symmetric_difference(&right.closed)
                .next()
                .unwrap();
            serde_json::json!({"anchor":anchor(key),"left":left.closed.contains(key),"right":right.closed.contains(key),"preceding_anchor_source":metadata.anchors.get(key),"dead_proven":false})
        }
        "clocks" => {
            let key = first_map_key(&left.clocks, &right.clocks).unwrap();
            let a = left.clocks.get(key);
            let b = right.clocks.get(key);
            let coordinate = a
                .into_iter()
                .flat_map(|clock| clock.keys())
                .chain(b.into_iter().flat_map(|clock| clock.keys()))
                .find(|coordinate| {
                    a.and_then(|clock| clock.get(*coordinate))
                        != b.and_then(|clock| clock.get(*coordinate))
                });
            serde_json::json!({"actor":key.map(|id|id.0),"left_clock_present":a.is_some(),"right_clock_present":b.is_some(),
                "first_changed_coordinate":coordinate.map(|actor|actor.map(|id|id.0)),
                "left_time":coordinate.and_then(|coordinate|a.and_then(|clock|clock.get(coordinate))),
                "right_time":coordinate.and_then(|coordinate|b.and_then(|clock|clock.get(coordinate))),
                "preceding_actor_source":key.and_then(|actor|metadata.actors.get(&actor)),"dead_proven":false})
        }
        "tasks" => {
            let key = first_map_key(&left.tasks, &right.tasks).unwrap();
            serde_json::json!({"child":key.0,"left_entry_present":left.tasks.contains_key(key),"right_entry_present":right.tasks.contains_key(key),
                "left_parent":left.tasks.get(key).and_then(|parent|parent.map(|id|id.0)),
                "right_parent":right.tasks.get(key).and_then(|parent|parent.map(|id|id.0)),
                "preceding_task_source":metadata.actors.get(key),"dead_proven":false})
        }
        "executed" => {
            let key = left
                .executed
                .symmetric_difference(&right.executed)
                .next()
                .unwrap();
            serde_json::json!({"actual_channel_message_id":key.0,"left":left.executed.contains(key),"right":right.executed.contains(key),
                "source":metadata.events.get(&key.0),"future_guard_reference_occurrences_global_diagnostic_only":metadata.future_guard_refs.get(&key.0).copied().unwrap_or(0),"dead_proven":false})
        }
        _ => unreachable!("observer field selector is internal"),
    }
}

fn difference_witnesses(
    states: &BTreeMap<Case, ChannelGuard>,
    metadata: &Metadata,
) -> serde_json::Value {
    let Some((baseline, guard)) = states.first_key_value() else {
        return serde_json::json!([]);
    };
    let mut result = Vec::new();
    macro_rules! witness {
        ($field:ident)=> {
            if let Some((index,(other,other_guard)))=states.iter().enumerate().find(|(_, (other,_))|baseline.$field!=other.$field) {
                result.push(serde_json::json!({"field":stringify!($field),"left_prefix_state":0,"right_prefix_state":index,
                    "first_exact_difference":difference(stringify!($field),baseline,other,metadata),
                    "left_guard_sample":guard_sample(guard),"right_guard_sample":guard_sample(other_guard),
                    "compression_or_authorization":false}));
            }
        };
    }
    witness!(custody);
    witness!(owners);
    witness!(inspected);
    witness!(returned);
    witness!(queues);
    witness!(closed);
    witness!(clocks);
    witness!(tasks);
    witness!(executed);
    serde_json::json!(result)
}
