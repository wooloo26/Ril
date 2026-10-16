//! Small independent conservation model for closed ordinary Result messages.
//!
//! This oracle deliberately has no Checker, Value, type expansion or source
//! syntax dependencies. A trace explicitly chooses the send/receive outcomes.
//! Returning a transport wrapper cannot return its submitted business Result.

use std::collections::{BTreeMap, VecDeque};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct Producer(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Holder {
    Caller(u32),
    Message(u32),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Obligation {
    holder: Holder,
    inspected: bool,
    returned: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Event {
    Produce {
        producer: Producer,
        caller: u32,
    },
    Send {
        producer: Producer,
        channel: u32,
        accepted: bool,
    },
    Receive {
        channel: u32,
        caller: u32,
        accepted: bool,
    },
    Inspect(Producer),
    Return(Producer),
    InspectTransport,
    ReturnTransport,
    CloseReceiver(u32),
    FinishCaller(u32),
    FinishScope,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Failure {
    UnknownProducer,
    DuplicateProducer,
    InfeasibleOutcome,
    Outstanding(Producer),
}

#[derive(Debug, Clone, Default)]
pub(super) struct Model {
    obligations: BTreeMap<Producer, Obligation>,
    queues: BTreeMap<u32, VecDeque<Producer>>,
}

impl Model {
    pub(super) fn apply(&mut self, event: Event) -> Result<(), Failure> {
        match event {
            Event::Produce { producer, caller } => {
                if self.obligations.contains_key(&producer) {
                    return Err(Failure::DuplicateProducer);
                }
                self.obligations.insert(
                    producer,
                    Obligation {
                        holder: Holder::Caller(caller),
                        inspected: false,
                        returned: false,
                    },
                );
            }
            Event::Send {
                producer,
                channel,
                accepted,
            } => {
                let duty = self
                    .obligations
                    .get_mut(&producer)
                    .ok_or(Failure::UnknownProducer)?;
                if !matches!(duty.holder, Holder::Caller(_)) {
                    return Err(Failure::InfeasibleOutcome);
                }
                if accepted {
                    duty.holder = Holder::Message(channel);
                    self.queues.entry(channel).or_default().push_back(producer);
                }
            }
            Event::Receive {
                channel,
                caller,
                accepted,
            } => {
                let queue = self.queues.entry(channel).or_default();
                if accepted {
                    let producer = queue.pop_front().ok_or(Failure::InfeasibleOutcome)?;
                    self.obligations
                        .get_mut(&producer)
                        .ok_or(Failure::UnknownProducer)?
                        .holder = Holder::Caller(caller);
                } else if !queue.is_empty() {
                    // Err(Closed) is after the last pending message. It neither
                    // consumes one nor repairs the sender's failed submission.
                    return Err(Failure::InfeasibleOutcome);
                }
            }
            Event::Inspect(producer) | Event::Return(producer) => {
                let duty = self
                    .obligations
                    .get_mut(&producer)
                    .ok_or(Failure::UnknownProducer)?;
                if matches!(event, Event::Inspect(_)) {
                    duty.inspected = true;
                } else {
                    duty.returned = true;
                }
            }
            Event::InspectTransport | Event::ReturnTransport => {}
            Event::CloseReceiver(channel) => {
                for producer in self.queues.get(&channel).into_iter().flatten() {
                    let duty = &self.obligations[producer];
                    if !duty.inspected && !duty.returned {
                        return Err(Failure::Outstanding(*producer));
                    }
                }
                self.queues.remove(&channel);
            }
            Event::FinishCaller(caller) => {
                self.check(|duty| duty.holder == Holder::Caller(caller))?;
            }
            Event::FinishScope => self.check(|_| true)?,
        }
        Ok(())
    }

    fn check(&self, relevant: impl Fn(&Obligation) -> bool) -> Result<(), Failure> {
        for (producer, duty) in &self.obligations {
            if relevant(duty) && !duty.inspected && !duty.returned {
                return Err(Failure::Outstanding(*producer));
            }
        }
        Ok(())
    }

    pub(super) fn holder(&self, producer: Producer) -> Option<Holder> {
        self.obligations.get(&producer).map(|duty| duty.holder)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_single_message_outcome_preserves_the_original_business_duty() {
        let producer = Producer(0);
        // All 64 combinations: two transport outcomes, two tag-inspection
        // choices, and independent original/received inspection choices.
        for bits in 0_u8..64 {
            let sent = bits & 1 != 0;
            let received = bits & 2 != 0;
            let inspect_send = bits & 4 != 0;
            let inspect_receive = bits & 8 != 0;
            let inspect_original = bits & 16 != 0;
            let inspect_received = bits & 32 != 0;
            let mut model = Model::default();
            model
                .apply(Event::Produce {
                    producer,
                    caller: 10,
                })
                .unwrap();
            model
                .apply(Event::Send {
                    producer,
                    channel: 20,
                    accepted: sent,
                })
                .unwrap();
            assert_eq!(
                model.holder(producer),
                Some(if sent {
                    Holder::Message(20)
                } else {
                    Holder::Caller(10)
                })
            );
            if inspect_send {
                model.apply(Event::InspectTransport).unwrap();
            }
            let outcome = model.apply(Event::Receive {
                channel: 20,
                caller: 30,
                accepted: received,
            });
            if sent != received {
                assert_eq!(outcome, Err(Failure::InfeasibleOutcome));
                continue;
            }
            outcome.unwrap();
            if inspect_receive {
                model.apply(Event::InspectTransport).unwrap();
            }
            if inspect_original || (received && inspect_received) {
                model.apply(Event::Inspect(producer)).unwrap();
            }
            assert_eq!(
                model.apply(Event::FinishScope).is_ok(),
                inspect_original || (received && inspect_received),
                "outcomes={bits:06b}"
            );
        }
    }

    #[test]
    fn caller_exit_barrier_and_receive_close_have_distinct_obligations() {
        let producer = Producer(7);
        for accepted in [false, true] {
            let mut model = Model::default();
            model
                .apply(Event::Produce {
                    producer,
                    caller: 1,
                })
                .unwrap();
            model
                .apply(Event::Send {
                    producer,
                    channel: 2,
                    accepted,
                })
                .unwrap();
            model.apply(Event::ReturnTransport).unwrap();
            assert_eq!(model.apply(Event::FinishCaller(1)).is_ok(), accepted);
            assert_eq!(model.apply(Event::CloseReceiver(2)).is_ok(), !accepted);
            assert_eq!(
                model.apply(Event::FinishScope),
                Err(Failure::Outstanding(producer))
            );
            model.apply(Event::Inspect(producer)).unwrap();
            model.apply(Event::CloseReceiver(2)).unwrap();
            model.apply(Event::FinishScope).unwrap();
        }
        let mut model = Model::default();
        model
            .apply(Event::Produce {
                producer,
                caller: 1,
            })
            .unwrap();
        model.apply(Event::Return(producer)).unwrap();
        model.apply(Event::FinishCaller(1)).unwrap();
    }

    #[test]
    fn both_cross_sender_interleavings_keep_two_distinct_business_producers() {
        let first = Producer(10);
        let second = Producer(20);
        // Neither lexical child order nor nested forwarding chooses the queue
        // order. Enumerate both physical orders, then every inspection subset.
        for order in [[first, second], [second, first]] {
            for inspected in 0_u8..4 {
                let mut model = Model::default();
                for producer in [first, second] {
                    model
                        .apply(Event::Produce {
                            producer,
                            caller: producer.0,
                        })
                        .unwrap();
                }
                for producer in order {
                    model
                        .apply(Event::Send {
                            producer,
                            channel: 7,
                            accepted: true,
                        })
                        .unwrap();
                }
                for (index, producer) in order.into_iter().enumerate() {
                    model
                        .apply(Event::Receive {
                            channel: 7,
                            caller: 30,
                            accepted: true,
                        })
                        .unwrap();
                    if inspected & (1 << index) != 0 {
                        model.apply(Event::Inspect(producer)).unwrap();
                    }
                }
                assert_eq!(model.apply(Event::FinishCaller(30)).is_ok(), inspected == 3);
                assert_eq!(model.apply(Event::FinishScope).is_ok(), inspected == 3);
            }
            let mut model = Model::default();
            for producer in [first, second] {
                model
                    .apply(Event::Produce {
                        producer,
                        caller: 1,
                    })
                    .unwrap();
            }
            for producer in order {
                model
                    .apply(Event::Send {
                        producer,
                        channel: 7,
                        accepted: true,
                    })
                    .unwrap();
            }
            for _ in order {
                model
                    .apply(Event::Receive {
                        channel: 7,
                        caller: 30,
                        accepted: true,
                    })
                    .unwrap();
            }
            model.apply(Event::Inspect(order[0])).unwrap();
            model.apply(Event::Return(order[0])).unwrap();
            assert_eq!(
                model.apply(Event::FinishScope),
                Err(Failure::Outstanding(order[1]))
            );
            model.apply(Event::Return(order[1])).unwrap();
            model.apply(Event::FinishScope).unwrap();
        }
    }

    #[test]
    fn same_sender_fifo_and_business_error_scope_exit_preserve_unread_debt() {
        let mut model = Model::default();
        for producer in [Producer(1), Producer(2)] {
            model
                .apply(Event::Produce {
                    producer,
                    caller: 1,
                })
                .unwrap();
            model
                .apply(Event::Send {
                    producer,
                    channel: 7,
                    accepted: true,
                })
                .unwrap();
        }
        model
            .apply(Event::Receive {
                channel: 7,
                caller: 3,
                accepted: true,
            })
            .unwrap();
        assert_eq!(model.holder(Producer(1)), Some(Holder::Caller(3)));
        assert_eq!(model.holder(Producer(2)), Some(Holder::Message(7)));
        model.apply(Event::Inspect(Producer(1))).unwrap();
        // A normal domain Err uses the same scope barrier as a normal Ok.
        assert_eq!(
            model.apply(Event::FinishScope),
            Err(Failure::Outstanding(Producer(2)))
        );
        assert_eq!(
            model.apply(Event::CloseReceiver(7)),
            Err(Failure::Outstanding(Producer(2)))
        );
        assert_eq!(
            model.apply(Event::Receive {
                channel: 7,
                caller: 3,
                accepted: false
            }),
            Err(Failure::InfeasibleOutcome)
        );
    }

    #[test]
    fn physical_repetition_changes_the_feasible_second_receive() {
        for count in 0..=3 {
            let mut model = Model::default();
            for index in 0..count {
                let producer = Producer(index);
                model
                    .apply(Event::Produce {
                        producer,
                        caller: 1,
                    })
                    .unwrap();
                model.apply(Event::Inspect(producer)).unwrap();
                model
                    .apply(Event::Send {
                        producer,
                        channel: 7,
                        accepted: true,
                    })
                    .unwrap();
            }
            let first = model.apply(Event::Receive {
                channel: 7,
                caller: 3,
                accepted: true,
            });
            if count == 0 {
                assert_eq!(first, Err(Failure::InfeasibleOutcome));
                continue;
            }
            first.unwrap();
            let second_err = model.apply(Event::Receive {
                channel: 7,
                caller: 3,
                accepted: false,
            });
            assert_eq!(second_err.is_ok(), count == 1);
            if count > 1 {
                model
                    .apply(Event::Receive {
                        channel: 7,
                        caller: 3,
                        accepted: true,
                    })
                    .unwrap();
                let unpaid = Producer(10);
                model
                    .apply(Event::Produce {
                        producer: unpaid,
                        caller: 3,
                    })
                    .unwrap();
                model
                    .apply(Event::Send {
                        producer: unpaid,
                        channel: 8,
                        accepted: true,
                    })
                    .unwrap();
                assert_eq!(
                    model.apply(Event::CloseReceiver(8)),
                    Err(Failure::Outstanding(unpaid))
                );
            }
        }
    }

    #[test]
    fn inspecting_in_a_zero_entry_callback_cannot_pay_the_later_send() {
        for count in 0..=3 {
            let producer = Producer(0);
            let mut model = Model::default();
            model
                .apply(Event::Produce {
                    producer,
                    caller: 1,
                })
                .unwrap();
            for _ in 0..count {
                model.apply(Event::Inspect(producer)).unwrap();
            }
            model
                .apply(Event::Send {
                    producer,
                    channel: 7,
                    accepted: true,
                })
                .unwrap();
            model.apply(Event::InspectTransport).unwrap();
            assert_eq!(model.apply(Event::CloseReceiver(7)).is_ok(), count > 0);
        }
    }
}
