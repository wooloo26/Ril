//! Test-only observation of measured record-657/661/858 guard calculations.
//! No counter, operand, result or authorization is changed by this observer.
use super::{ChannelGuard, ChannelMessageId, GuardLiteral};
use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet},
};

struct Failure {
    stage: &'static str,
    used: usize,
    limit: usize,
}

#[derive(Default)]
struct Counter {
    charged: usize,
    maximum_counter: usize,
}

struct Trace {
    record_sequence: u64,
    actual_event: Option<ChannelMessageId>,
    left: ChannelGuard,
    event_guard: ChannelGuard,
    complement: Option<ChannelGuard>,
    executed: BTreeSet<ChannelMessageId>,
    transport_support: BTreeSet<ChannelMessageId>,
    phase: &'static str,
    counters: BTreeMap<&'static str, Counter>,
    failure: Option<Failure>,
}

thread_local! {
    static TRACE: RefCell<Option<Trace>> = const { RefCell::new(None) };
}

pub(in crate::sema) struct Capture(bool);
impl Capture {
    pub(in crate::sema) fn begin(
        record_sequence: u64,
        event: Option<ChannelMessageId>,
        left: &ChannelGuard,
        event_guard: &ChannelGuard,
        executed: &BTreeSet<ChannelMessageId>,
    ) -> Self {
        if !matches!(record_sequence, 657 | 661 | 858) {
            return Self(false);
        }
        TRACE.with(|current| {
            let mut current = current.borrow_mut();
            if current.is_some() {
                return Self(false);
            }
            *current = Some(Trace {
                record_sequence,
                actual_event: event,
                left: left.clone(),
                event_guard: event_guard.clone(),
                complement: None,
                executed: executed.clone(),
                transport_support: left
                    .terms
                    .iter()
                    .chain(&event_guard.terms)
                    .flatten()
                    .filter_map(|literal| match literal {
                        GuardLiteral::Transport { event, .. } => Some(*event),
                        _ => None,
                    })
                    .collect(),
                phase: "inactive intersection",
                counters: BTreeMap::new(),
                failure: None,
            });
            Self(true)
        })
    }
}

fn operand(guard: &ChannelGuard) -> serde_json::Value {
    serde_json::json!({
        "clauses": guard.terms.len(),
        "literal_total": guard.terms.iter().map(|term| term.len()).sum::<usize>(),
        "maximum_clause_literals": guard.terms.iter().map(|term| term.len()).max().unwrap_or(0),
        "incomplete": guard.incomplete,
        "exact_guard": format!("{guard:?}"),
    })
}

impl Drop for Capture {
    fn drop(&mut self) {
        if !self.0 {
            return;
        }
        let trace = TRACE.with(|current| current.borrow_mut().take());
        let Some(trace) = trace else { return };
        let Some(failure) = trace.failure else { return };
        let counters = trace
            .counters
            .into_iter()
            .map(|(phase, counter)| {
                (
                    phase,
                    serde_json::json!({
                        "charged": counter.charged,
                        "maximum_counter": counter.maximum_counter,
                    }),
                )
            })
            .collect::<BTreeMap<_, _>>();
        eprintln!(
            "channel-guard-metrics {}",
            serde_json::json!({
                "record_sequence": trace.record_sequence,
                "record_kind": if trace.actual_event.is_some() { "Event" } else { "Exit" },
                "actual_channel_message_id": trace.actual_event.map(|event| event.0),
                "operation": "inactive intersection",
                "left": operand(&trace.left),
                "event_guard": operand(&trace.event_guard),
                "complement": trace.complement.as_ref().map(operand),
                "executed": trace.executed.iter().map(|event| event.0).collect::<Vec<_>>(),
                "transport_support": trace.transport_support.iter().map(|event| event.0).collect::<Vec<_>>(),
                "all_transport_support_executed": trace.transport_support.is_subset(&trace.executed),
                "failure": {"stage":failure.stage,"used":failure.used,"limit":failure.limit},
                "counters": counters,
            })
        );
    }
}

pub(super) struct Phase(Option<&'static str>);
pub(super) fn phase(phase: &'static str) -> Phase {
    TRACE.with(|current| {
        Phase(current.borrow_mut().as_mut().map(|trace| {
            let previous = trace.phase;
            trace.phase = phase;
            previous
        }))
    })
}
impl Drop for Phase {
    fn drop(&mut self) {
        if let Some(previous) = self.0 {
            TRACE.with(|current| {
                if let Some(trace) = current.borrow_mut().as_mut() {
                    trace.phase = previous;
                }
            });
        }
    }
}

pub(super) fn charged(amount: usize, used: usize) {
    TRACE.with(|current| {
        if let Some(trace) = current.borrow_mut().as_mut() {
            let counter = trace.counters.entry(trace.phase).or_default();
            counter.charged = counter.charged.saturating_add(amount);
            counter.maximum_counter = counter.maximum_counter.max(used);
        }
    });
}

pub(super) fn failed(stage: Option<&'static str>, used: usize, limit: usize) {
    TRACE.with(|current| {
        if let Some(trace) = current.borrow_mut().as_mut() {
            trace.failure.get_or_insert(Failure {
                stage: stage.unwrap_or(trace.phase),
                used,
                limit,
            });
        }
    });
}

pub(super) fn complement(guard: &ChannelGuard) {
    TRACE.with(|current| {
        if let Some(trace) = current.borrow_mut().as_mut() {
            trace.complement = Some(guard.clone());
        }
    });
}
