//! Private flow state for outcome-indexed channel message obligations.
use super::*;
use crate::sema::channel_messages::{ChannelAnchor, ChannelGuard, ChannelMessageId, GuardLiteral};
use crate::sema::channel_production::ProductionCase;
#[path = "messages_conditions.rs"]
mod conditions;
#[path = "messages_optionals.rs"]
mod optionals;

const MAX_WORLDS: usize = 256;
const MAX_PACKETS: usize = 4096;

#[derive(Clone, PartialEq, Eq)]
pub(super) enum Holder {
    Caller(ScopeId),
    Message(ChannelAnchor),
}

#[derive(Clone, PartialEq, Eq)]
pub(super) struct Packet {
    pub send: ChannelMessageId,
    pub payload: Value,
    pub producers: BTreeSet<u32>,
    pub sender: NodeId,
    pub task: Option<NodeId>,
    pub clock: BTreeMap<Option<NodeId>, u64>,
}

#[derive(Clone, Default)]
pub(super) struct World {
    pub guard: ChannelGuard,
    pub queues: BTreeMap<ChannelAnchor, Vec<Packet>>,
    pub holders: BTreeMap<u32, Holder>,
    pub inspected: BTreeSet<u32>,
    pub returned: BTreeMap<u32, ScopeId>,
    pub abnormal_owners: BTreeSet<ScopeId>,
    pub closed_receivers: BTreeSet<ChannelAnchor>,
    pub clocks: BTreeMap<Option<NodeId>, BTreeMap<Option<NodeId>, u64>>,
    pub executed: BTreeSet<ChannelMessageId>,
}

pub(super) struct MessageObservation<'a> {
    pub(super) endpoint: NodeId,
    pub(super) resource: &'a Resource,
    pub(super) source: &'a Value,
    pub(super) payload: &'a Value,
    pub(super) transport: &'a Value,
}
struct SendObservation<'a> {
    id: ChannelMessageId,
    anchor: ChannelAnchor,
    payload: &'a Value,
    production: &'a [ProductionCase],
    transport: &'a Value,
    versions: &'a BTreeMap<u32, u32>,
    owners: &'a BTreeMap<u32, ScopeId>,
    inspected: &'a BTreeSet<u32>,
    sender: NodeId,
    task: Option<NodeId>,
}
struct ReceiveObservation<'a> {
    id: ChannelMessageId,
    anchor: &'a ChannelAnchor,
    production: &'a [ProductionCase],
    transport: &'a Value,
    versions: &'a BTreeMap<u32, u32>,
    owner: ScopeId,
    business_payload: bool,
    task: Option<NodeId>,
}

#[derive(Clone)]
pub(in crate::sema::checker) struct Flow {
    pub(super) worlds: Vec<World>,
    pub aliases: BTreeMap<u32, BTreeSet<ChannelMessageId>>,
    pub producers: BTreeSet<u32>,
    pub generations: BTreeMap<u32, u32>,
    pub result_outcomes: BTreeMap<u32, [ChannelGuard; 2]>,
    pub incomplete: bool,
    repeated_events: BTreeSet<ChannelMessageId>,
    pub boolean_owners: BTreeMap<crate::sema::result_conditions::ConditionEvaluationId, ScopeId>,
    pub current_context: Option<(crate::sema::effect_identity::InvocationContext, ScopeId)>,
}
impl Default for Flow {
    fn default() -> Self {
        Self {
            worlds: vec![World::default()],
            aliases: BTreeMap::new(),
            producers: BTreeSet::new(),
            generations: BTreeMap::new(),
            result_outcomes: BTreeMap::new(),
            incomplete: false,
            repeated_events: BTreeSet::new(),
            boolean_owners: BTreeMap::new(),
            current_context: None,
        }
    }
}

impl Flow {
    pub(super) fn guard(&self) -> ChannelGuard {
        if self.incomplete {
            return ChannelGuard::unavailable();
        }
        self.worlds
            .iter()
            .try_fold(ChannelGuard::never(), |guard, world| guard.or(&world.guard))
            .unwrap_or_else(ChannelGuard::unavailable)
    }

    pub(in crate::sema::checker) fn select(&mut self, guard: &ChannelGuard) -> bool {
        if self.incomplete || guard.incomplete {
            self.incomplete = true;
            return false;
        }
        let mut selected = Vec::new();
        for world in &self.worlds {
            let Some(guard) = world.guard.and(guard) else {
                self.incomplete = true;
                return false;
            };
            let guard = guard_for_events(guard, &world.executed);
            if !guard.is_never() {
                let mut next = world.clone();
                next.guard = guard;
                selected.push(next);
            }
        }
        self.worlds = selected;
        true
    }

    pub(super) fn outcome(
        &self,
        value: &Value,
        versions: &BTreeMap<u32, u32>,
        success: bool,
    ) -> ChannelGuard {
        let mut guard = ChannelGuard::never();
        let mut any = false;
        for producer in &value.outer_results {
            if let Some(outcomes) = self.result_outcomes.get(producer) {
                any = true;
                let Some(joined) = guard.or(&outcomes[usize::from(success)]) else {
                    return ChannelGuard::unavailable();
                };
                guard = joined;
                continue;
            }
            if let Some(events) = self.aliases.get(producer) {
                for event in events {
                    if events.len() > 1
                        && self
                            .worlds
                            .iter()
                            .any(|world| events.intersection(&world.executed).count() > 1)
                    {
                        return ChannelGuard::unavailable();
                    }
                    any = true;
                    let literal = ChannelGuard::literal(GuardLiteral::Transport {
                        event: *event,
                        producer: *producer,
                        version: versions.get(producer).copied().unwrap_or(0),
                        success,
                    });
                    let Some(joined) = guard.or(&literal) else {
                        return ChannelGuard::unavailable();
                    };
                    guard = joined;
                }
            }
        }
        if any {
            guard
        } else if value.result_tag.is_none()
            && value.outer_results.len() == 1
            && value.outer_results == value.must_outer_results
        {
            let producer = *value.outer_results.first().unwrap();
            ChannelGuard::literal(GuardLiteral::Result {
                producer,
                version: versions.get(&producer).copied().unwrap_or(0),
                success,
            })
        } else {
            ChannelGuard::always()
        }
    }

    pub(super) fn alias_results(&mut self, map: &BTreeMap<u32, BTreeSet<u32>>) {
        for (new, old) in map {
            if old.len() == 1
                && let Some(outcomes) = self.result_outcomes.get(old.first().unwrap()).cloned()
            {
                self.result_outcomes.insert(*new, outcomes);
            } else if old.len() == 1
                && let Some(old) = old.first().filter(|old| self.producers.contains(old))
                && !self.aliases.contains_key(old)
                && self.worlds.iter().any(|world| world.guard.terms.iter().flatten().any(|literal| matches!(literal, GuardLiteral::Result { producer, .. } if producer == old)))
            {
                let outcomes = [false, true].map(|success| {
                    ChannelGuard::literal(GuardLiteral::Result {
                        producer: *old,
                        version: self.generations.get(old).copied().unwrap_or(0),
                        success,
                    })
                });
                self.result_outcomes.insert(*new, outcomes);
            }
            let events: BTreeSet<_> = old
                .iter()
                .filter_map(|old| self.aliases.get(old))
                .flatten()
                .copied()
                .collect();
            if !events.is_empty() {
                self.aliases.insert(*new, events);
            }
        }
    }

    fn send(&mut self, observation: SendObservation<'_>) -> bool {
        let SendObservation {
            id,
            anchor,
            payload,
            production,
            transport,
            versions,
            owners,
            inspected,
            sender,
            task,
        } = observation;
        for producer in &transport.outer_results {
            self.aliases.entry(*producer).or_default().insert(id);
        }
        self.producers.extend(&payload.results);
        for producer in &payload.results {
            let version = versions.get(producer).copied().unwrap_or(0);
            if self
                .generations
                .insert(*producer, version)
                .is_some_and(|old| old != version)
            {
                self.incomplete = true;
                return false;
            }
        }
        if payload.results.is_empty() {
            // A scalar-only channel has no business debt. Its physical outcome
            // remains unconstrained; enumerating its queues cannot authorize
            // any later Result transfer and would waste the guarded budget.
            for world in &mut self.worlds {
                world.executed.insert(id);
            }
            return true;
        }
        let mut worlds = Vec::new();
        for world in &self.worlds {
            for contents in production {
                for success in [false, true] {
                    if success && world.closed_receivers.contains(&anchor) {
                        continue;
                    }
                    let mut next = world.clone();
                    next.executed.insert(id);
                    let Some(guard) = next
                        .guard
                        .and(&contents.guard)
                        .and_then(|guard| guard.and(&self.outcome(transport, versions, success)))
                    else {
                        self.incomplete = true;
                        return false;
                    };
                    if guard.is_never() {
                        continue;
                    }
                    next.guard = guard;
                    for producer in &contents.producers {
                        next.holders
                            .entry(*producer)
                            .or_insert(Holder::Caller(owners[producer]));
                        if inspected.contains(producer) {
                            next.inspected.insert(*producer);
                        }
                        if success {
                            next.holders
                                .insert(*producer, Holder::Message(anchor.clone()));
                        }
                    }
                    if success {
                        let Some(clock) = tick(&mut next.clocks, task) else {
                            self.incomplete = true;
                            return false;
                        };
                        let queue = next.queues.entry(anchor.clone()).or_default();
                        if queue.len() >= MAX_PACKETS {
                            self.incomplete = true;
                            return false;
                        }
                        queue.push(Packet {
                            send: id,
                            payload: payload.clone(),
                            producers: contents.producers.clone(),
                            sender,
                            task,
                            clock,
                        });
                    }
                    worlds.push(next);
                    if worlds.len() > MAX_WORLDS {
                        self.incomplete = true;
                        return false;
                    }
                }
            }
        }
        self.worlds = worlds;
        true
    }

    pub(super) fn can_finish(&self, producer: u32, owner: ScopeId) -> bool {
        !self.incomplete
            && self.worlds.iter().all(|world| {
                world.holders.get(&producer) != Some(&Holder::Caller(owner))
                    || world.inspected.contains(&producer)
                    || world.returned.contains_key(&producer)
                    || world.abnormal_owners.contains(&owner)
            })
    }

    pub(super) fn front_values(&self, anchor: &ChannelAnchor) -> Vec<Value> {
        let mut packets = BTreeMap::new();
        for world in &self.worlds {
            if let Some(packet) = world.queues.get(anchor).and_then(|queue| queue.first()) {
                packets
                    .entry(packet.send)
                    .or_insert_with(|| packet.payload.clone());
            }
        }
        packets.into_values().collect()
    }

    pub(super) fn receive_order_known(&self, anchor: &ChannelAnchor) -> bool {
        self.worlds.iter().all(|world| {
            let Some(queue) = world.queues.get(anchor) else {
                return true;
            };
            let Some(first) = queue.first() else {
                return true;
            };
            queue
                .iter()
                .skip(1)
                .all(|packet| before(&first.clock, &packet.clock))
        })
    }

    fn receive(
        &mut self,
        observation: ReceiveObservation<'_>,
    ) -> Option<Vec<crate::sema::channel_messages::ChannelReceiveSource>> {
        let ReceiveObservation {
            id,
            anchor,
            production,
            transport,
            versions,
            owner,
            business_payload,
            task,
        } = observation;
        use crate::sema::channel_messages::ChannelReceiveSource;
        for producer in production.iter().flat_map(|contents| &contents.producers) {
            let version = versions.get(producer).copied().unwrap_or(0);
            if self
                .generations
                .insert(*producer, version)
                .is_some_and(|old| old != version)
            {
                self.incomplete = true;
                return None;
            }
        }
        for producer in &transport.outer_results {
            self.aliases.entry(*producer).or_default().insert(id);
        }
        if !business_payload {
            for world in &mut self.worlds {
                world.executed.insert(id);
            }
            return Some(Vec::new());
        }
        let mut worlds = Vec::new();
        let mut sources = Vec::new();
        for world in &self.worlds {
            let packet = world.queues.get(anchor).and_then(|queue| queue.first());
            let queued;
            let production = if let Some(packet) = packet {
                queued = [ProductionCase {
                    guard: ChannelGuard::always(),
                    producers: packet.producers.clone(),
                }];
                queued.as_slice()
            } else {
                production
            };
            for contents in production {
                for success in [false, true] {
                    if packet.is_some() && !success {
                        continue;
                    }
                    if packet.is_none()
                        && success
                        && !matches!(anchor, ChannelAnchor::Formal { .. })
                    {
                        continue;
                    }
                    let mut next = world.clone();
                    next.executed.insert(id);
                    let guard = next
                        .guard
                        .and(&contents.guard)?
                        .and(&self.outcome(transport, versions, success))?;
                    if guard.is_never() {
                        continue;
                    }
                    next.guard = guard;
                    if success {
                        for producer in &contents.producers {
                            self.producers.insert(*producer);
                            next.holders.insert(*producer, Holder::Caller(owner));
                            next.returned.remove(producer);
                        }
                        sources.push(ChannelReceiveSource {
                            guard: next.guard.clone(),
                            send: packet.map(|packet| packet.send),
                        });
                        if packet.is_some() {
                            let source_clock = &packet?.clock;
                            let receiver = next.clocks.entry(task).or_default();
                            for (actor, time) in source_clock {
                                receiver
                                    .entry(*actor)
                                    .and_modify(|old| *old = (*old).max(*time))
                                    .or_insert(*time);
                            }
                            tick(&mut next.clocks, task)?;
                            next.queues.get_mut(anchor)?.remove(0);
                        }
                    }
                    worlds.push(next);
                    if worlds.len() > MAX_WORLDS {
                        self.incomplete = true;
                        return None;
                    }
                }
            }
        }
        self.worlds = worlds;
        Some(sources)
    }

    pub(super) fn inspect(&mut self, producers: &BTreeSet<u32>) {
        for world in &mut self.worlds {
            world.inspected.extend(
                producers
                    .iter()
                    .filter(|producer| world.holders.contains_key(producer))
                    .copied(),
            );
        }
    }

    pub(super) fn merge(flows: impl IntoIterator<Item = Self>) -> Self {
        let mut result = Self {
            worlds: Vec::new(),
            ..Self::default()
        };
        for flow in flows {
            result.incomplete |= flow.incomplete;
            result.producers.extend(flow.producers);
            for (producer, version) in flow.generations {
                if result
                    .generations
                    .insert(producer, version)
                    .is_some_and(|old| old != version)
                {
                    result.incomplete = true;
                }
            }
            result.boolean_owners.extend(flow.boolean_owners);
            for (producer, outcomes) in flow.result_outcomes {
                if let Some(previous) = result.result_outcomes.get_mut(&producer) {
                    for truth in [0, 1] {
                        match previous[truth].or(&outcomes[truth]) {
                            Some(joined) => previous[truth] = joined,
                            None => result.incomplete = true,
                        }
                    }
                } else {
                    result.result_outcomes.insert(producer, outcomes);
                }
            }
            for (producer, events) in flow.aliases {
                result.aliases.entry(producer).or_default().extend(events);
            }
            result.repeated_events.extend(flow.repeated_events);
            result.worlds.extend(flow.worlds);
            let mut joined: Vec<World> = Vec::new();
            for world in std::mem::take(&mut result.worlds) {
                if let Some(old) = joined.iter_mut().find(|old| {
                    old.queues == world.queues
                        && old.holders == world.holders
                        && old.inspected == world.inspected
                        && old.returned == world.returned
                        && old.abnormal_owners == world.abnormal_owners
                        && old.closed_receivers == world.closed_receivers
                        && old.clocks == world.clocks
                        && old.executed == world.executed
                }) {
                    match old.guard.or(&world.guard) {
                        Some(guard) => old.guard = guard,
                        None => result.incomplete = true,
                    }
                } else {
                    joined.push(world);
                }
            }
            result.worlds = joined;
            if result.worlds.len() > MAX_WORLDS {
                result.incomplete = true;
                result.worlds.truncate(MAX_WORLDS);
            }
        }
        result
    }

    pub(super) fn remap(&mut self, recent: NodeId, older: NodeId) {
        fn anchor(anchor: &ChannelAnchor, recent: NodeId, older: NodeId) -> ChannelAnchor {
            let remap = |node| if node == recent { older } else { node };
            match anchor {
                ChannelAnchor::Known { channel, scope } => ChannelAnchor::Known {
                    channel: remap(*channel),
                    scope: remap(*scope),
                },
                ChannelAnchor::Formal { endpoint, scope } => ChannelAnchor::Formal {
                    endpoint: remap(*endpoint),
                    scope: remap(*scope),
                },
            }
        }
        for world in &mut self.worlds {
            if world.queues.values().any(|queue| !queue.is_empty())
                && (world.clocks.contains_key(&Some(recent))
                    && world.clocks.contains_key(&Some(older))
                    || world.clocks.values().any(|clock| {
                        clock.contains_key(&Some(recent)) && clock.contains_key(&Some(older))
                    }))
            {
                self.incomplete = true;
            }
            let mut queues: BTreeMap<_, Vec<_>> = BTreeMap::new();
            for (key, mut packets) in std::mem::take(&mut world.queues) {
                for packet in &mut packets {
                    copy::remap_value_origins(&mut packet.payload, recent, older);
                    if packet.sender == recent {
                        packet.sender = older;
                    }
                    if packet.task == Some(recent) {
                        packet.task = Some(older);
                    }
                    remap_clock(&mut packet.clock, recent, older);
                }
                queues
                    .entry(anchor(&key, recent, older))
                    .or_default()
                    .extend(packets);
            }
            world.queues = queues;
            let mut clocks: BTreeMap<_, BTreeMap<_, _>> = BTreeMap::new();
            for (actor, mut clock) in std::mem::take(&mut world.clocks) {
                remap_clock(&mut clock, recent, older);
                clocks.insert(
                    if actor == Some(recent) {
                        Some(older)
                    } else {
                        actor
                    },
                    clock,
                );
            }
            world.clocks = clocks;
            for holder in world.holders.values_mut() {
                if let Holder::Message(key) = holder {
                    *key = anchor(key, recent, older);
                }
            }
        }
    }
}

fn guard_for_events(
    mut guard: ChannelGuard,
    executed: &BTreeSet<ChannelMessageId>,
) -> ChannelGuard {
    guard.terms.retain(|term| {
        term.iter().all(|literal| match literal {
            GuardLiteral::Transport { event, .. } => executed.contains(event),
            GuardLiteral::Boolean { .. }
            | GuardLiteral::Result { .. }
            | GuardLiteral::Optional { .. } => true,
        })
    });
    guard
}

fn tick(
    clocks: &mut BTreeMap<Option<NodeId>, BTreeMap<Option<NodeId>, u64>>,
    actor: Option<NodeId>,
) -> Option<BTreeMap<Option<NodeId>, u64>> {
    if clocks.len() >= 4096 && !clocks.contains_key(&actor) {
        return None;
    }
    let clock = clocks.entry(actor).or_default();
    let time = clock.entry(actor).or_default();
    *time = time.checked_add(1)?;
    Some(clock.clone())
}
fn before(left: &BTreeMap<Option<NodeId>, u64>, right: &BTreeMap<Option<NodeId>, u64>) -> bool {
    left != right
        && left
            .iter()
            .all(|(actor, time)| *time <= right.get(actor).copied().unwrap_or(0))
}
fn remap_clock(clock: &mut BTreeMap<Option<NodeId>, u64>, recent: NodeId, older: NodeId) {
    if let Some(time) = clock.remove(&Some(recent)) {
        clock
            .entry(Some(older))
            .and_modify(|old| *old = (*old).max(time))
            .or_insert(time);
    }
}

impl Checker {
    pub(in crate::sema::checker) fn channel_source_event(
        &self,
        frame: &Frame,
    ) -> Option<crate::sema::copy_contract::CopyCallEventId> {
        frame
            .copy_call_event
            .or_else(|| self.application_effect.enclosing_application())
    }
    pub(in crate::sema::checker) fn channel_begin_repetition(
        &mut self,
        frame: &Frame,
    ) -> crate::sema::channel_messages::ChannelRepetitionId {
        use crate::sema::channel_messages::{ChannelRepetition, ChannelRepetitionId};
        let id = ChannelRepetitionId(self.channel_repetitions.len() as u32);
        self.channel_repetitions.push(ChannelRepetition {
            id,
            parent: self.active_channel_repetitions.last().copied(),
            context: self.invocation_context(frame.callable_owner),
            activation: frame.owner,
            call: self.channel_source_event(frame),
            start_sequence: self.channel_message_sequence,
            end_sequence: None,
        });
        self.active_channel_repetitions.push(id);
        id
    }

    pub(in crate::sema::checker) fn channel_finish_repetition(
        &mut self,
        id: crate::sema::channel_messages::ChannelRepetitionId,
        span: Span,
    ) {
        if self.active_channel_repetitions.pop() != Some(id) {
            self.concurrency.message_flow.incomplete = true;
            self.unsupported(span, "channel repetition activation is incomplete");
            return;
        }
        let end = self.channel_message_sequence;
        let entry = &mut self.channel_repetitions[id.0 as usize];
        entry.end_sequence = Some(end);
        let start = entry.start_sequence;
        self.channel_repeated_events(start, end, span);
    }

    pub(in crate::sema::checker) fn channel_repeated_events(
        &mut self,
        start: u64,
        end: u64,
        span: Span,
    ) {
        use crate::sema::channel_messages::ChannelAction;
        let events = self
            .channel_message_facts
            .iter()
            .filter(|event| {
                (start..end).contains(&event.sequence)
                    && matches!(
                        event.action,
                        ChannelAction::Send { .. }
                            | ChannelAction::Receive { .. }
                            | ChannelAction::TaskFork { .. }
                            | ChannelAction::TaskJoin { .. }
                    )
            })
            .map(|event| event.id)
            .collect::<BTreeSet<_>>();
        if events.is_empty() {
            return;
        }
        self.concurrency.message_flow.repeated_events.extend(events);
        if !self.concurrency.message_flow.producers.is_empty() {
            self.concurrency.message_flow.incomplete = true;
            self.unsupported(
                span,
                "repeated channel operations require iteration-indexed physical event coverage",
            );
        }
    }

    fn channel_repeated_admission(&mut self, payload: &Value, span: Span) {
        if !payload.results.is_empty() && !self.concurrency.message_flow.repeated_events.is_empty()
        {
            self.concurrency.message_flow.incomplete = true;
            self.unsupported(
                span,
                "repeated channel operations require iteration-indexed physical event coverage",
            );
        }
    }
    fn channel_value_snapshot(
        &self,
        value: &Value,
    ) -> crate::sema::copy_contract::CopyValueSnapshot {
        // Carrier witnesses need their own roots: a Result's unselected
        // constructor may not be reachable through its current root origins.
        let mut graph = value.clone();
        let mut work = 4096_usize;
        fn roots(value: &Value, output: &mut BTreeSet<NodeId>, work: &mut usize) -> Option<()> {
            *work = work.checked_sub(1)?;
            output.extend(&value.origins.nodes);
            for child in [
                &value.result_payload,
                &value.result_success,
                &value.result_error,
                &value.option_payload,
                &value.variant_payload,
            ]
            .into_iter()
            .flatten()
            .chain(value.variant_witnesses.values())
            {
                roots(child, output, work)?;
            }
            Some(())
        }
        let mut nodes = BTreeSet::new();
        if roots(value, &mut nodes, &mut work).is_none() {
            return self.copy_value_snapshot(value);
        }
        loop {
            let reachable = self.heap.reachable(nodes.iter().copied());
            let previous = nodes.len();
            nodes.extend(&reachable);
            for ((node, _), field) in &self.fields {
                if reachable.contains(node) && roots(field, &mut nodes, &mut work).is_none() {
                    return self.copy_value_snapshot(value);
                }
            }
            if nodes.len() == previous {
                break;
            }
            if nodes.len() > 128 {
                return self.copy_value_snapshot(value);
            }
        }
        graph.origins.nodes = nodes;
        let (nodes, relations) = self.copy_graph_snapshot(&graph);
        crate::sema::copy_contract::CopyValueSnapshot {
            value: value.clone(),
            nodes,
            relations,
        }
    }

    pub(in crate::sema::checker) fn channel_has_messages(&self) -> bool {
        !self.concurrency.message_flow.producers.is_empty()
            || !self.concurrency.message_flow.aliases.is_empty()
    }
    pub(in crate::sema::checker) fn channel_preview(&mut self) {
        self.concurrency.message_flow.worlds.clear();
    }

    pub(super) fn channel_task_order(
        &mut self,
        child: NodeId,
        fork: bool,
        span: Span,
        frame: &Frame,
    ) {
        use crate::sema::channel_messages::{ChannelAction, ChannelMessageFact};
        let task = self.concurrency.task_context.last().copied();
        let Some(sequence) = self.channel_sequence(span) else {
            return;
        };
        self.channel_message_facts.push(ChannelMessageFact {
            repetition: self.active_channel_repetitions.last().copied(),
            source_event: self.channel_source_event(frame),
            id: ChannelMessageId(self.channel_message_facts.len() as u32),
            sequence,
            context: self.invocation_context(frame.callable_owner),
            activation: frame.owner,
            task,
            span,
            cause: self.heap.nodes[child.0 as usize].cause,
            allocation_epoch: self.recency_moves.len(),
            guard: self.concurrency.message_flow.guard(),
            action: if fork {
                ChannelAction::TaskFork { child }
            } else {
                ChannelAction::TaskJoin { child }
            },
        });
        for world in &mut self.concurrency.message_flow.worlds {
            if fork {
                let Some(clock) = tick(&mut world.clocks, task) else {
                    self.concurrency.message_flow.incomplete = true;
                    break;
                };
                if world.clocks.insert(Some(child), clock).is_some() {
                    self.concurrency.message_flow.incomplete = true;
                    break;
                }
            } else {
                let child_clock = world.clocks.get(&Some(child)).cloned().unwrap_or_default();
                let parent = world.clocks.entry(task).or_default();
                for (actor, time) in child_clock {
                    parent
                        .entry(actor)
                        .and_modify(|old| *old = (*old).max(time))
                        .or_insert(time);
                }
                if tick(&mut world.clocks, task).is_none() {
                    self.concurrency.message_flow.incomplete = true;
                    break;
                }
            }
        }
        if self.concurrency.message_flow.incomplete && self.channel_has_messages() {
            self.unsupported(
                span,
                "task order needs an individual bounded channel causality proof",
            );
        }
    }

    pub(in crate::sema::checker) fn channel_save_flow(&self) -> Flow {
        self.concurrency.message_flow.clone()
    }
    pub(in crate::sema::checker) fn channel_restore_flow(&mut self, flow: Flow) {
        self.concurrency.message_flow = flow;
    }

    pub(in crate::sema::checker) fn channel_copy_results(
        &mut self,
        value: &Value,
        map: &BTreeMap<u32, u32>,
        owner: ScopeId,
        span: Span,
    ) {
        let relevant = map.keys().any(|old| {
            self.concurrency.message_flow.aliases.contains_key(old)
                || self.channel_known_producer(*old)
        });
        if !relevant {
            return;
        }
        let flow = &self.concurrency.message_flow;
        let presence = flow
            .worlds
            .iter()
            .map(|world| message_presence::present(value, world, flow, &self.fields))
            .collect::<Option<Vec<_>>>();
        let Some(presence) = presence else {
            self.concurrency.message_flow.incomplete = true;
            self.unsupported(
                span,
                "copied channel Result presence needs a complete bounded proof",
            );
            return;
        };
        for (world, present) in self
            .concurrency
            .message_flow
            .worlds
            .iter_mut()
            .zip(presence)
        {
            for (old, new) in map {
                if present.contains(old) && world.holders.contains_key(old) {
                    world.holders.insert(*new, Holder::Caller(owner));
                    world.inspected.remove(new);
                    world.returned.remove(new);
                }
            }
        }
        let known = map
            .iter()
            .filter_map(|(old, new)| self.channel_known_producer(*old).then_some(*new))
            .collect::<Vec<_>>();
        self.concurrency.message_flow.producers.extend(known);
        let aliases = map.iter().map(|(old, new)| (*new, [*old].into())).collect();
        self.channel_record_aliases(aliases, owner, value.cause, span);
    }

    pub(in crate::sema::checker) fn channel_record_aliases(
        &mut self,
        map: BTreeMap<u32, BTreeSet<u32>>,
        owner: ScopeId,
        cause: CauseId,
        span: Span,
    ) {
        use crate::sema::channel_messages::{ChannelAction, ChannelMessageFact};
        for (new, members) in &map {
            if members.len() > 1
                && members
                    .iter()
                    .any(|old| self.concurrency.message_flow.aliases.contains_key(old))
            {
                match self.channel_family_outcomes(members, owner) {
                    Some(outcomes) => {
                        self.concurrency
                            .message_flow
                            .result_outcomes
                            .insert(*new, outcomes);
                    }
                    None => {
                        self.concurrency.message_flow.incomplete = true;
                        self.unsupported(span, "transport Result family requires complete actual one-of return receipts; physical event aliases alone cannot determine its tag");
                    }
                }
            }
        }
        self.concurrency.message_flow.alias_results(&map);
        if map.values().flatten().all(|producer| {
            !self.concurrency.message_flow.aliases.contains_key(producer)
                && !self.channel_known_producer(*producer)
        }) {
            return;
        }
        let Some(sequence) = self.channel_sequence(span) else {
            return;
        };
        self.channel_message_facts.push(ChannelMessageFact {
            repetition: self.active_channel_repetitions.last().copied(),
            source_event: None,
            id: ChannelMessageId(self.channel_message_facts.len() as u32),
            sequence,
            context: self.invocation_context(self.expression_owners.last().copied().flatten()),
            activation: owner,
            span,
            cause,
            allocation_epoch: self.recency_moves.len(),
            guard: self.concurrency.message_flow.guard(),
            task: self.concurrency.task_context.last().copied(),
            action: ChannelAction::ResultAliases { map },
        });
    }

    fn channel_family_outcomes(
        &self,
        members: &BTreeSet<u32>,
        owner: ScopeId,
    ) -> Option<[ChannelGuard; 2]> {
        use crate::sema::channel_messages::ChannelExitKind;
        let mut outcomes = [ChannelGuard::never(), ChannelGuard::never()];
        for member in members {
            let mut found = false;
            for receipt in self.channel_exit_facts.iter().filter(|receipt| {
                receipt.activation == owner
                    && matches!(
                        receipt.kind,
                        ChannelExitKind::Callable | ChannelExitKind::Return
                    )
                    && receipt.returned.value.must_outer_results.contains(member)
            }) {
                found = true;
                for success in [false, true] {
                    let tag = if let Some(known) = receipt.returned.value.result_tag {
                        if known == success {
                            ChannelGuard::always()
                        } else {
                            ChannelGuard::never()
                        }
                    } else {
                        if !self.concurrency.message_flow.aliases.contains_key(member)
                            && !self
                                .concurrency
                                .message_flow
                                .result_outcomes
                                .contains_key(member)
                        {
                            return None;
                        }
                        self.concurrency.message_flow.outcome(
                            &receipt.returned.value,
                            &self.channel_versions(&receipt.returned.value),
                            success,
                        )
                    };
                    let guard = receipt.guard.and(&tag)?;
                    outcomes[usize::from(success)] = outcomes[usize::from(success)].or(&guard)?;
                }
            }
            if !found {
                return None;
            }
        }
        if !outcomes[0].and(&outcomes[1])?.is_never() {
            return None;
        }
        let covered = outcomes[0].or(&outcomes[1])?;
        self.concurrency
            .message_flow
            .guard()
            .and(&covered.not()?)?
            .is_never()
            .then_some(outcomes)
    }

    pub(in crate::sema::checker) fn channel_known_producer(&self, producer: u32) -> bool {
        self.concurrency.message_flow.producers.contains(&producer)
    }

    pub(in crate::sema::checker) fn channel_can_finish(
        &self,
        producer: u32,
        owner: ScopeId,
    ) -> bool {
        self.concurrency.message_flow.can_finish(producer, owner)
    }

    pub(in crate::sema::checker) fn channel_obligations_complete(&self) -> bool {
        !self.concurrency.message_flow.incomplete
    }

    pub(in crate::sema::checker) fn channel_return_at(&mut self, owner: ScopeId, value: &Value) {
        let flow = &self.concurrency.message_flow;
        let presence = flow
            .worlds
            .iter()
            .map(|world| message_presence::present(value, world, flow, &self.fields))
            .collect::<Option<Vec<_>>>();
        let Some(presence) = presence else {
            self.concurrency.message_flow.incomplete = true;
            self.unsupported(
                self.result_duties
                    .first()
                    .map(|duty| duty.span)
                    .unwrap_or(Span {
                        file: self.file,
                        start: 0,
                        end: 0,
                    }),
                "channel returned payload presence resource limit exceeded",
            );
            return;
        };
        for (world, producers) in self
            .concurrency
            .message_flow
            .worlds
            .iter_mut()
            .zip(presence)
        {
            for producer in producers {
                if world.holders.contains_key(&producer) {
                    world.returned.insert(producer, owner);
                }
            }
        }
    }

    pub(in crate::sema::checker) fn channel_transfer_results(
        &mut self,
        value: &Value,
        from: ScopeId,
        to: ScopeId,
    ) {
        let flow = &self.concurrency.message_flow;
        let presence = flow
            .worlds
            .iter()
            .map(|world| message_presence::present(value, world, flow, &self.fields))
            .collect::<Option<Vec<_>>>();
        let Some(presence) = presence else {
            self.concurrency.message_flow.incomplete = true;
            return;
        };
        for (world, producers) in self
            .concurrency
            .message_flow
            .worlds
            .iter_mut()
            .zip(presence)
        {
            for producer in producers {
                if world.holders.get(&producer) == Some(&Holder::Caller(from))
                    || (world.returned.get(&producer) == Some(&from)
                        && self.result_duties[producer as usize].owner == from)
                {
                    world.holders.insert(producer, Holder::Caller(to));
                }
                world.returned.remove(&producer);
            }
        }
    }

    pub(in crate::sema::checker) fn channel_record_result_transfer(
        &mut self,
        value: &Value,
        from: ScopeId,
        to: ScopeId,
    ) {
        use crate::sema::channel_messages::{ChannelAction, ChannelMessageFact};
        let producers = self
            .result_family_closure(value.results.iter().copied())
            .into_iter()
            .filter(|id| from != to && self.result_duties[*id as usize].owner == from)
            .collect::<BTreeSet<_>>();
        if producers.is_empty() {
            return;
        }
        let span = self
            .explanations
            .causes
            .get(value.cause.0 as usize)
            .and_then(|cause| cause.span)
            .unwrap_or(self.result_duties[*producers.first().unwrap() as usize].span);
        let Some(sequence) = self.channel_sequence(span) else {
            return;
        };
        self.channel_message_facts.push(ChannelMessageFact {
            repetition: self.active_channel_repetitions.last().copied(),
            source_event: None,
            id: ChannelMessageId(self.channel_message_facts.len() as u32),
            sequence,
            context: self.invocation_context(self.expression_owners.last().copied().flatten()),
            activation: to,
            span,
            cause: value.cause,
            allocation_epoch: self.recency_moves.len(),
            guard: self.concurrency.message_flow.guard(),
            task: self.concurrency.task_context.last().copied(),
            action: ChannelAction::ResultTransfer {
                from,
                to,
                source: self.channel_value_snapshot(value),
                producers,
            },
        });
    }

    pub(in crate::sema::checker) fn channel_finish_callable(
        &mut self,
        owner: ScopeId,
        value: &Value,
    ) {
        use crate::sema::channel_messages::{ChannelExitFact, ChannelExitKind};
        if self.concurrency.message_flow.producers.is_empty()
            && self
                .channel_return_states
                .keys()
                .all(|(actual, _)| *actual != owner)
        {
            return;
        }
        // This value is the actual fallthrough receipt. Explicit returns are
        // joined by the language caller later; applying it to their worlds
        // would fabricate a returned payload (or an abnormal waiver).
        if value.ty == Ty::Never
            && !value.abnormal
            && self
                .channel_return_states
                .keys()
                .any(|(actual, _)| *actual == owner)
        {
            // A structural branch join may restore its baseline after every
            // branch returned. That baseline is not another body execution.
            self.concurrency.message_flow.worlds.clear();
        }
        let normal_guard = self.concurrency.message_flow.guard();
        self.channel_return_at(owner, value);
        if value.abnormal {
            for world in &mut self.concurrency.message_flow.worlds {
                world.abnormal_owners.insert(owner);
            }
        }
        let returns = self
            .channel_return_states
            .keys()
            .filter(|(actual, _)| *actual == owner)
            .copied()
            .collect::<Vec<_>>();
        if !returns.is_empty() {
            let mut paths = vec![self.concurrency.message_flow.clone()];
            paths.extend(
                returns
                    .into_iter()
                    .filter_map(|key| self.channel_return_states.remove(&key)),
            );
            self.concurrency.message_flow = Flow::merge(paths);
        }
        if self.concurrency.message_flow.producers.is_empty() {
            return;
        }
        if self.concurrency.message_flow.incomplete {
            let span = self
                .result_duties
                .first()
                .map(|duty| duty.span)
                .unwrap_or(Span {
                    file: self.file,
                    start: 0,
                    end: 0,
                });
            self.unsupported(
                span,
                "channel obligation completion requires a complete bounded actual-event proof",
            );
            return;
        }
        let span = self
            .explanations
            .causes
            .get(value.cause.0 as usize)
            .and_then(|cause| cause.span)
            .unwrap_or(Span {
                file: self.file,
                start: 0,
                end: 0,
            });
        let Some(sequence) = self.channel_sequence(span) else {
            return;
        };
        let context = self
            .concurrency
            .message_flow
            .current_context
            .filter(|(_, actual)| *actual == owner)
            .map(|(context, _)| context)
            .unwrap_or_else(|| {
                self.invocation_context(self.expression_owners.last().copied().flatten())
            });
        self.channel_exit_facts.push(ChannelExitFact {
            sequence,
            context,
            activation: owner,
            span,
            cause: value.cause,
            allocation_epoch: self.recency_moves.len(),
            guard: normal_guard,
            kind: if value.abnormal {
                ChannelExitKind::Abnormal
            } else {
                ChannelExitKind::Callable
            },
            anchor: None,
            returned: self.channel_value_snapshot(value),
        });
        let Some(sequence) = self.channel_sequence(span) else {
            return;
        };
        let unit = self.unit(span);
        self.channel_exit_facts.push(ChannelExitFact {
            sequence,
            context,
            activation: owner,
            span,
            cause: value.cause,
            allocation_epoch: self.recency_moves.len(),
            guard: self.concurrency.message_flow.guard(),
            kind: ChannelExitKind::Complete,
            anchor: None,
            returned: self.channel_value_snapshot(&unit),
        });
    }

    pub(in crate::sema::checker) fn channel_return_exit(&mut self, owner: ScopeId, value: &Value) {
        use crate::sema::channel_messages::{ChannelExitFact, ChannelExitKind};
        if self.concurrency.message_flow.producers.is_empty() {
            return;
        }
        self.channel_return_states
            .entry((owner, value.cause.0))
            .and_modify(|previous| {
                *previous = Flow::merge([previous.clone(), self.concurrency.message_flow.clone()])
            })
            .or_insert_with(|| self.concurrency.message_flow.clone());
        let span = self
            .explanations
            .causes
            .get(value.cause.0 as usize)
            .and_then(|cause| cause.span)
            .unwrap_or(Span {
                file: self.file,
                start: 0,
                end: 0,
            });
        let Some(sequence) = self.channel_sequence(span) else {
            return;
        };
        self.channel_exit_facts.push(ChannelExitFact {
            sequence,
            context: self
                .concurrency
                .message_flow
                .current_context
                .map(|(context, _)| context)
                .unwrap_or_else(|| {
                    self.invocation_context(self.expression_owners.last().copied().flatten())
                }),
            activation: owner,
            span,
            cause: value.cause,
            allocation_epoch: self.recency_moves.len(),
            guard: self.concurrency.message_flow.guard(),
            kind: ChannelExitKind::Return,
            anchor: None,
            returned: self.channel_value_snapshot(value),
        });
    }

    pub(super) fn channel_receiver_exit(
        &mut self,
        endpoint: NodeId,
        resource: &Resource,
        source: &Value,
        span: Span,
        frame: &Frame,
    ) {
        use crate::sema::channel_messages::{ChannelExitFact, ChannelExitKind};
        if self.concurrency.message_flow.incomplete {
            self.unsupported(
                span,
                "receiver completion requires its complete channel obligation proof",
            );
            return;
        }
        let anchor = self.channel_anchor(endpoint, resource);
        let pending = self
            .concurrency
            .message_flow
            .worlds
            .iter()
            .flat_map(|world| {
                world
                    .queues
                    .get(&anchor)
                    .into_iter()
                    .flatten()
                    .flat_map(|packet| &packet.payload.results)
                    .filter(|id| !world.inspected.contains(id) && !world.returned.contains_key(id))
                    .copied()
            })
            .next();
        if let Some(id) = pending {
            self.error(
                "E0720",
                span,
                "normal receiver close loses an uninspected Result message",
                [self.result_duties[id as usize].cause],
            );
        }
        let Some(sequence) = self.channel_sequence(span) else {
            return;
        };
        let unit = self.unit(span);
        let returned = self.channel_value_snapshot(&unit);
        self.channel_exit_facts.push(ChannelExitFact {
            sequence,
            context: self.invocation_context(frame.callable_owner),
            activation: frame.owner,
            span,
            cause: source.cause,
            allocation_epoch: self.recency_moves.len(),
            guard: self.concurrency.message_flow.guard(),
            kind: ChannelExitKind::Receiver,
            anchor: Some(anchor.clone()),
            returned,
        });
        for world in &mut self.concurrency.message_flow.worlds {
            world.closed_receivers.insert(anchor.clone());
            world.queues.remove(&anchor);
        }
    }

    pub(super) fn channel_scope_exit(
        &mut self,
        scope: NodeId,
        result: &Value,
        span: Span,
        frame: &Frame,
    ) {
        use crate::sema::channel_messages::{ChannelExitFact, ChannelExitKind};
        if self.concurrency.message_flow.incomplete {
            self.unsupported(
                span,
                "scope completion requires its complete channel obligation proof",
            );
            return;
        }
        let flow = &self.concurrency.message_flow;
        let presence = flow
            .worlds
            .iter()
            .map(|world| message_presence::present(result, world, flow, &self.fields))
            .collect::<Option<Vec<_>>>();
        let Some(presence) = presence else {
            self.unsupported(
                span,
                "scope Result return presence exceeds its channel proof budget",
            );
            return;
        };
        let mut pending = None;
        for (world, returned) in self
            .concurrency
            .message_flow
            .worlds
            .iter_mut()
            .zip(presence)
        {
            let channels = world.queues.keys().filter(|anchor| matches!(anchor, ChannelAnchor::Known { scope: actual, .. } if *actual == scope)).cloned().collect::<Vec<_>>();
            for channel in channels {
                if let Some(packets) = world.queues.remove(&channel) {
                    for producer in packets.iter().flat_map(|packet| &packet.payload.results) {
                        if result.abnormal {
                            world.holders.remove(producer);
                        } else if returned.contains(producer) {
                            world.holders.insert(*producer, Holder::Caller(frame.owner));
                            world.returned.remove(producer);
                        } else if !world.inspected.contains(producer)
                            && !world.returned.contains_key(producer)
                        {
                            pending.get_or_insert(*producer);
                        }
                    }
                }
                world.closed_receivers.insert(channel);
            }
        }
        if let Some(id) = pending {
            self.error(
                "E0720",
                span,
                "normal scope exit loses an uninspected Result message",
                [self.result_duties[id as usize].cause],
            );
        }
        let Some(sequence) = self.channel_sequence(span) else {
            return;
        };
        self.channel_exit_facts.push(ChannelExitFact {
            sequence,
            context: self.invocation_context(frame.callable_owner),
            activation: frame.owner,
            span,
            cause: result.cause,
            allocation_epoch: self.recency_moves.len(),
            guard: self.concurrency.message_flow.guard(),
            kind: if result.abnormal {
                ChannelExitKind::Abnormal
            } else {
                ChannelExitKind::Scope
            },
            anchor: Some(ChannelAnchor::Known {
                channel: scope,
                scope,
            }),
            returned: self.channel_value_snapshot(result),
        });
    }

    fn channel_anchor(&self, endpoint: NodeId, resource: &Resource) -> ChannelAnchor {
        match resource.channel {
            Some(channel) => ChannelAnchor::Known {
                channel,
                scope: resource.scope,
            },
            None => ChannelAnchor::Formal {
                endpoint,
                scope: resource.scope,
            },
        }
    }

    fn channel_dependencies(
        &self,
        value: &Value,
    ) -> BTreeSet<crate::sema::channel_messages::ChannelBindingPath> {
        use crate::sema::channel_messages::ChannelBindingPath;
        let mut result = BTreeSet::new();
        let mut pending: Vec<_> = value.sources.iter().copied().collect();
        let mut seen = BTreeSet::new();
        while let Some(binding) = pending.pop() {
            if !seen.insert(binding) {
                continue;
            }
            let Some(source) = self.bindings.get(binding) else {
                continue;
            };
            pending.extend(&source.forwarded);
            if source.parameter {
                result.insert(ChannelBindingPath {
                    binding,
                    projection: Vec::new(),
                });
            }
        }
        result
    }

    fn channel_payload_complete(&self, payload: &Value) -> bool {
        if !crate::sema::channel_production::complete(
            &self.channel_value_snapshot(payload),
            &self.types,
            &self.constructors,
        ) {
            return false;
        }
        if payload.results.is_empty() {
            return true;
        }
        if !self.resource_free(payload)
            || self.has_unresolved_row(payload)
            || !payload.scoped.is_empty()
            || !payload.callables.is_empty()
            || payload.mutable_environment
            || payload.observer_environment
            || !self.pending_copy_dependencies(payload).is_empty()
        {
            return false;
        }
        let nodes = self.heap.reachable(payload.origins.nodes.iter().copied());
        nodes.len() <= 128
            && self
                .fields
                .iter()
                .filter(|((node, _), _)| nodes.contains(node))
                .take(4097)
                .count()
                <= 4096
            && self
                .fields
                .iter()
                .filter(|((node, _), _)| nodes.contains(node))
                .all(|(_, field)| {
                    field.scoped.is_empty()
                        && field.callables.is_empty()
                        && !field.mutable_environment
                        && !field.observer_environment
                })
    }

    pub(super) fn channel_record_send(
        &mut self,
        observation: MessageObservation<'_>,
        span: Span,
        frame: &Frame,
    ) {
        use crate::sema::channel_messages::{ChannelAction, ChannelMessageFact};
        let MessageObservation {
            endpoint,
            resource,
            source,
            payload,
            transport,
        } = observation;
        self.channel_repeated_admission(payload, span);
        if !self.channel_payload_complete(payload) {
            self.concurrency
                .message_flow
                .producers
                .extend(&payload.results);
            self.unsupported(span, "channel Result payload requires a complete ordinary graph; resource, scoped and unresolved constituents retain their obligations");
            self.concurrency.message_flow.incomplete = true;
            return;
        }
        let Some(sequence) = self.channel_sequence(span) else {
            return;
        };
        let id = ChannelMessageId(self.channel_message_facts.len() as u32);
        let anchor = self.channel_anchor(endpoint, resource);
        let owners = payload
            .results
            .iter()
            .map(|id| (*id, self.result_duties[*id as usize].owner))
            .collect::<BTreeMap<_, _>>();
        let inspected = payload
            .results
            .iter()
            .copied()
            .filter(|id| self.result_duties[*id as usize].inspected)
            .collect();
        let mut versions = self.channel_versions(transport);
        versions.extend(payload.results.iter().map(|producer| {
            (
                *producer,
                self.result_inspection_versions
                    .get(producer)
                    .copied()
                    .unwrap_or(0),
            )
        }));
        let Some(production) = crate::sema::channel_production::cases(
            &self.channel_value_snapshot(payload),
            &versions,
        ) else {
            self.concurrency.message_flow.incomplete = true;
            self.unsupported(
                span,
                "channel conditional Result production exceeds its bounded complete graph proof",
            );
            return;
        };
        let guard = self.concurrency.message_flow.guard();
        self.channel_message_facts.push(ChannelMessageFact {
            repetition: self.active_channel_repetitions.last().copied(),
            source_event: self.channel_source_event(frame),
            id,
            sequence,
            context: self.invocation_context(frame.callable_owner),
            activation: frame.owner,
            span,
            cause: transport.cause,
            allocation_epoch: self.recency_moves.len(),
            guard,
            task: self.concurrency.task_context.last().copied(),
            action: ChannelAction::Send {
                endpoint: self.channel_value_snapshot(source),
                anchor: anchor.clone(),
                payload: self.channel_value_snapshot(payload),
                transport: self.channel_value_snapshot(transport),
                producer_versions: versions.clone(),
                original_owners: owners.clone(),
                dependencies: self.channel_dependencies(source),
            },
        });
        if !self.concurrency.message_flow.send(SendObservation {
            id,
            anchor,
            payload,
            production: &production,
            transport,
            versions: &versions,
            owners: &owners,
            inspected: &inspected,
            sender: endpoint,
            task: self.concurrency.task_context.last().copied(),
        }) {
            self.unsupported(
                span,
                "channel message outcome ledger resource limit exceeded",
            );
        }
    }

    pub(super) fn channel_receive_value(
        &mut self,
        endpoint: NodeId,
        resource: &Resource,
        ty: &Ty,
        span: Span,
        frame: &Frame,
    ) -> Value {
        let anchor = self.channel_anchor(endpoint, resource);
        if !self.concurrency.message_flow.receive_order_known(&anchor) {
            self.concurrency.message_flow.incomplete = true;
            self.unsupported(span, "Result messages from different senders require a proven happens-before order or correlated interleaving coverage");
        }
        let mut values = self
            .concurrency
            .message_flow
            .front_values(&anchor)
            .into_iter();
        let mut payload = if let Some(first) = values.next() {
            let choice = self.choice();
            values.fold(first, |old, value| old.join(&value, choice, old.cause))
        } else {
            let cached = resource
                .channel
                .and_then(|channel| self.concurrency.messages.get_mut(&channel))
                .and_then(|messages| (!messages.is_empty()).then(|| messages.remove(0)));
            cached.unwrap_or_else(|| {
                let mut value = self.standard_value(ty.clone(), span, frame.owner, 0x6600);
                self.produced_symbolic_results(&mut value, span, frame.owner);
                value
            })
        };
        payload.constant = None;
        payload.ty = ty.clone();
        payload
    }

    pub(super) fn channel_record_receive(
        &mut self,
        observation: MessageObservation<'_>,
        span: Span,
        frame: &Frame,
    ) {
        use crate::sema::channel_messages::{ChannelAction, ChannelMessageFact};
        let MessageObservation {
            endpoint,
            resource,
            source,
            payload,
            transport,
        } = observation;
        self.channel_repeated_admission(payload, span);
        if !self.channel_payload_complete(payload) {
            self.concurrency
                .message_flow
                .producers
                .extend(&payload.results);
            self.unsupported(
                span,
                "channel receive Result payload requires a complete ordinary graph",
            );
            self.concurrency.message_flow.incomplete = true;
            return;
        }
        let Some(sequence) = self.channel_sequence(span) else {
            return;
        };
        let id = ChannelMessageId(self.channel_message_facts.len() as u32);
        let anchor = self.channel_anchor(endpoint, resource);
        let guard = self.concurrency.message_flow.guard();
        let mut versions = self.channel_versions(transport);
        versions.extend(payload.results.iter().map(|producer| {
            (
                *producer,
                self.result_inspection_versions
                    .get(producer)
                    .copied()
                    .unwrap_or(0),
            )
        }));
        let Some(production) = crate::sema::channel_production::cases(
            &self.channel_value_snapshot(payload),
            &versions,
        ) else {
            self.concurrency.message_flow.incomplete = true;
            self.unsupported(
                span,
                "channel receive conditional Result production exceeds its bounded graph proof",
            );
            return;
        };
        self.concurrency
            .message_flow
            .producers
            .extend(&payload.results);
        let sources = self.concurrency.message_flow.receive(ReceiveObservation {
            id,
            anchor: &anchor,
            production: &production,
            transport,
            versions: &versions,
            owner: frame.owner,
            business_payload: !payload.results.is_empty(),
            task: self.concurrency.task_context.last().copied(),
        });
        let Some(sources) = sources else {
            self.unsupported(
                span,
                "channel receive outcome ledger resource limit exceeded",
            );
            return;
        };
        self.channel_message_facts.push(ChannelMessageFact {
            repetition: self.active_channel_repetitions.last().copied(),
            source_event: self.channel_source_event(frame),
            id,
            sequence,
            context: self.invocation_context(frame.callable_owner),
            activation: frame.owner,
            span,
            cause: transport.cause,
            allocation_epoch: self.recency_moves.len(),
            guard,
            task: self.concurrency.task_context.last().copied(),
            action: ChannelAction::Receive {
                endpoint: self.channel_value_snapshot(source),
                anchor,
                payload: self.channel_value_snapshot(payload),
                transport: self.channel_value_snapshot(transport),
                producer_versions: versions,
                sources,
                dependencies: self.channel_dependencies(source),
            },
        });
    }

    fn channel_versions(&self, value: &Value) -> BTreeMap<u32, u32> {
        value
            .outer_results
            .iter()
            .map(|producer| {
                (
                    *producer,
                    self.result_inspection_versions
                        .get(producer)
                        .copied()
                        .unwrap_or(0),
                )
            })
            .collect()
    }

    pub(in crate::sema::checker) fn channel_result_outcome(
        &self,
        value: &Value,
        success: bool,
    ) -> ChannelGuard {
        if value.result_tag.is_some_and(|known| known != success) {
            return ChannelGuard::never();
        }
        self.concurrency
            .message_flow
            .outcome(value, &self.channel_versions(value), success)
    }

    pub(in crate::sema::checker) fn channel_tag_test(
        &mut self,
        value: &Value,
        success: bool,
        pattern: Span,
        frame: &Frame,
    ) {
        self.concurrency.message_flow.current_context =
            Some((self.invocation_context(frame.callable_owner), frame.owner));
        use crate::sema::channel_messages::{ChannelAction, ChannelMessageFact};
        if value.outer_results.iter().all(|producer| {
            !self.concurrency.message_flow.aliases.contains_key(producer)
                && !self.concurrency.message_flow.producers.contains(producer)
        }) && (value.result_tag.is_some() || value.outer_results.len() != 1)
        {
            return;
        }
        let Some(sequence) = self.channel_sequence(pattern) else {
            return;
        };
        self.channel_message_facts.push(ChannelMessageFact {
            repetition: self.active_channel_repetitions.last().copied(),
            source_event: self.channel_source_event(frame),
            id: ChannelMessageId(self.channel_message_facts.len() as u32),
            sequence,
            context: self.invocation_context(frame.callable_owner),
            activation: frame.owner,
            span: pattern,
            cause: value.cause,
            allocation_epoch: self.recency_moves.len(),
            guard: self.concurrency.message_flow.guard(),
            task: self.concurrency.task_context.last().copied(),
            action: ChannelAction::TagTest {
                subject: self.channel_value_snapshot(value),
                success,
                pattern,
                producer_versions: self.channel_versions(value),
            },
        });
    }

    pub(in crate::sema::checker) fn channel_assume_result(
        &mut self,
        value: &Value,
        success: bool,
        pattern: Span,
        frame: &Frame,
    ) {
        self.channel_tag_test(value, success, pattern, frame);
        let guard = self.channel_result_outcome(value, success);
        if !self.concurrency.message_flow.select(&guard) {
            self.unsupported(
                pattern,
                "channel constructor selection exceeds its bounded outcome proof",
            );
        }
    }

    fn channel_sequence(&mut self, span: Span) -> Option<u64> {
        let sequence = self.channel_message_sequence;
        if self
            .channel_message_facts
            .len()
            .saturating_add(self.channel_exit_facts.len())
            >= 16_384
        {
            if self.channel_has_messages() {
                self.unsupported(span, "channel message evidence resource limit exceeded");
            }
            self.concurrency.message_flow.incomplete = true;
            return None;
        }
        let Some(next) = sequence.checked_add(1) else {
            self.unsupported(span, "channel event sequence limit exceeded");
            self.concurrency.message_flow.incomplete = true;
            return None;
        };
        self.channel_message_sequence = next;
        Some(sequence)
    }

    pub(in crate::sema::checker) fn channel_inspect_results(&mut self, value: &Value) {
        use crate::sema::channel_messages::{ChannelAction, ChannelMessageFact};
        let producers = self.result_family_closure(value.must_outer_results.iter().copied());
        // Before a first send, freeze ordinary inspections too. The independent
        // replay must not borrow the duty's final inspected flag. Optional loop
        // bodies do not provide a pre-send must-execute receipt.
        if producers.is_empty()
            || (self.loop_depth > 0 && !self.loop_result_inspection_allowed(value))
        {
            return;
        }
        let span = self.result_duties[*producers.first().unwrap() as usize].span;
        let Some(sequence) = self.channel_sequence(span) else {
            return;
        };
        let context = self.invocation_context(self.expression_owners.last().copied().flatten());
        let activation = self
            .concurrency
            .message_flow
            .current_context
            .filter(|(actual, _)| *actual == context)
            .map(|(_, owner)| owner)
            .unwrap_or(ScopeId(u32::MAX));
        self.channel_message_facts.push(ChannelMessageFact {
            repetition: self.active_channel_repetitions.last().copied(),
            source_event: None,
            id: ChannelMessageId(self.channel_message_facts.len() as u32),
            sequence,
            context,
            activation,
            span,
            cause: value.cause,
            allocation_epoch: self.recency_moves.len(),
            guard: self.concurrency.message_flow.guard(),
            task: self.concurrency.task_context.last().copied(),
            action: ChannelAction::Inspect {
                value: self.channel_value_snapshot(value),
                producer_versions: self.channel_versions(value),
            },
        });
        self.concurrency.message_flow.inspect(&producers);
    }

    pub(in crate::sema::checker) fn channel_invocation_messages(
        &self,
        owner: ScopeId,
    ) -> BTreeSet<ChannelMessageId> {
        use crate::sema::channel_messages::ChannelAction;
        self.channel_message_facts
            .iter()
            .filter(|fact| {
                if !matches!(
                    fact.action,
                    ChannelAction::Send { .. } | ChannelAction::Receive { .. }
                ) {
                    return false;
                }
                let mut current = Some(fact.activation);
                let mut seen = BTreeSet::new();
                while let Some(scope) = current {
                    if scope == owner {
                        return true;
                    }
                    if !seen.insert(scope) {
                        return false;
                    }
                    current = self.scopes.parent(&scope).copied();
                }
                false
            })
            .map(|fact| fact.id)
            .collect()
    }

    pub(in crate::sema::checker) fn channel_boolean_evaluation(
        &mut self,
        value: &mut Value,
        span: Span,
        frame: &Frame,
    ) {
        self.concurrency.message_flow.current_context =
            Some((self.invocation_context(frame.callable_owner), frame.owner));
        if value.ty == Ty::Bool && value.condition_inspections.evaluations.is_empty() {
            self.record_condition_evaluation(
                value,
                crate::sema::result_conditions::ConditionKind::Plain,
                span,
                frame,
            );
        }
    }

    pub(in crate::sema::checker) fn channel_record_boolean_identity(
        &mut self,
        value: &mut Value,
        id: crate::sema::result_conditions::ConditionEvaluationId,
        owner: ScopeId,
    ) {
        self.concurrency
            .message_flow
            .boolean_owners
            .insert(id, owner);
        let dependent = value.condition_inspections.channel_dependent();
        for truth in [false, true] {
            let chosen = value.constant.as_ref().is_none_or(
                |constant| !matches!(constant, Constant::Bool(known) if *known != truth),
            );
            let base = if dependent {
                value.condition_inspections.channel_outcome(truth).clone()
            } else {
                ChannelGuard::always()
            };
            *value.condition_inspections.channel_outcome_mut(truth) = if chosen {
                base.and(&ChannelGuard::literal(GuardLiteral::Boolean {
                    evaluation: id,
                    truth,
                }))
                .unwrap_or_else(ChannelGuard::unavailable)
            } else {
                ChannelGuard::never()
            };
        }
    }

    pub(in crate::sema::checker) fn channel_select_condition(
        &mut self,
        evidence: &crate::sema::result_conditions::ConditionInspections,
        truth: bool,
        span: Span,
        cause: CauseId,
    ) {
        let mut guard = evidence.channel_outcome(truth).clone();
        // A stale producer generation supplies no outcome permission. Removing
        // its restriction broadens the checked cases instead of hiding debt.
        guard.terms = guard
            .terms
            .iter()
            .map(|term| {
                term.iter()
                    .copied()
                    .filter(|literal| match literal {
                        GuardLiteral::Transport {
                            producer, version, ..
                        }
                        | GuardLiteral::Result {
                            producer, version, ..
                        } => {
                            self.result_inspection_versions
                                .get(producer)
                                .copied()
                                .unwrap_or(0)
                                == *version
                        }
                        GuardLiteral::Boolean { .. } | GuardLiteral::Optional { .. } => true,
                    })
                    .collect()
            })
            .collect();
        guard = guard.normalized().unwrap_or_else(ChannelGuard::unavailable);
        let relevant = !self.concurrency.message_flow.aliases.is_empty()
            || !self.concurrency.message_flow.producers.is_empty();
        if !self.concurrency.message_flow.select(&guard) && relevant {
            self.unsupported(
                span,
                "channel outcome guard resource limit exceeded; no message transfer was authorized",
            );
        }
        // Replaying an evaluated boolean is an actual tag-inspection proof on
        // this continuation, including worlds retained by a pattern preview.
        // Use its immutable versions even if the ordinary duty is already a
        // no-op; that global flag is not the guarded world's inspection bit.
        let inspected = self.result_family_closure(evidence.outcome(truth).iter().copied().filter(
            |producer| {
                evidence.versions.get(producer).copied()
                    == Some(
                        self.result_inspection_versions
                            .get(producer)
                            .copied()
                            .unwrap_or(0),
                    )
            },
        ));
        self.concurrency.message_flow.inspect(&inspected);
        if (relevant || (!inspected.is_empty() && self.loop_depth == 0))
            && let Some(evaluation) = evidence.evaluations.last().copied()
        {
            use crate::sema::channel_messages::{ChannelAction, ChannelMessageFact};
            let Some(proof) = self.condition_evaluations.get(evaluation.0 as usize) else {
                return;
            };
            let context = proof.context;
            let activation = self
                .concurrency
                .message_flow
                .boolean_owners
                .get(&evaluation)
                .copied()
                .unwrap_or(ScopeId(u32::MAX));
            let Some(sequence) = self.channel_sequence(span) else {
                return;
            };
            self.channel_message_facts.push(ChannelMessageFact {
                repetition: self.active_channel_repetitions.last().copied(),
                source_event: None,
                id: ChannelMessageId(self.channel_message_facts.len() as u32),
                sequence,
                context,
                activation,
                span,
                cause,
                allocation_epoch: self.recency_moves.len(),
                guard: self.concurrency.message_flow.guard(),
                task: self.concurrency.task_context.last().copied(),
                action: ChannelAction::Select { evaluation, truth },
            });
        }
    }
}
