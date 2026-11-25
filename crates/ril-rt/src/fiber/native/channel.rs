//! Channel endpoints and their scheduler wait queues.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use num_traits::ToPrimitive as _;

use super::{Event, Raw, Task, context, error, invoke, tag, wait};
use crate::{Object, Runtime, Value};

pub(super) struct Pipe {
    cap: Option<usize>,
    queued: VecDeque<Value>,
    waiting_senders: VecDeque<(Task, Value)>,
    delivered: BTreeSet<Task>,
    waiting_receiver: bool,
    senders: usize,
    receiver: bool,
}

impl Pipe {
    fn withdraw(&mut self, sender: Task) -> Option<Value> {
        self.delivered.remove(&sender);
        let index = self
            .waiting_senders
            .iter()
            .position(|&(task, _)| task == sender)?;
        self.waiting_senders.remove(index).map(|(_, value)| value)
    }

    fn take(&mut self) -> Option<Value> {
        if let Some(item) = self.queued.pop_front() {
            return Some(item);
        }
        let (sender, item) = self.waiting_senders.pop_front()?;
        self.delivered.insert(sender);
        Some(item)
    }
}

fn pipe(rt: &mut Runtime, cap: Option<usize>) -> Value {
    let id = rt.fiber.id();
    rt.fiber.channels.insert(
        id,
        Pipe {
            cap,
            queued: VecDeque::new(),
            waiting_senders: VecDeque::new(),
            delivered: BTreeSet::new(),
            waiting_receiver: false,
            senders: 1,
            receiver: true,
        },
    );
    let tx = rt.gc.alloc(Object::Sender(id));
    rt.gc.pin(tx);
    let rx = rt.gc.alloc(Object::Receiver(id));
    rt.gc.unpin(tx);
    rt.gc.alloc(Object::Record(BTreeMap::from([
        ("rx".into(), rx),
        ("tx".into(), tx),
    ])))
}

#[unsafe(no_mangle)]
unsafe extern "C" fn ril_channel_bounded(raw: Raw, capacity: Value) -> Value {
    // SAFETY: allocation does not switch fibers.
    let rt = unsafe { context(raw) };
    let Some(capacity) = rt.gc.integer(capacity).filter(|value| !value.is_negative()) else {
        rt.raise("channel capacity must be a nonnegative int");
        return Value::UNIT;
    };
    let capacity = capacity.to_usize().unwrap_or(usize::MAX);
    pipe(rt, Some(capacity))
}

#[unsafe(no_mangle)]
unsafe extern "C" fn ril_channel_unbounded(raw: Raw) -> Value {
    // SAFETY: allocation does not switch fibers.
    pipe(unsafe { context(raw) }, None)
}

#[unsafe(no_mangle)]
unsafe extern "C" fn ril_channel_clone(raw: Raw, sender: Value) -> Value {
    // SAFETY: increments the handle count without a stack switch.
    let rt = unsafe { context(raw) };
    let Some(Object::Sender(id)) = rt.gc.object(sender) else {
        return error(rt, "invalid channel sender");
    };
    let id = *id;
    if let Some(channel) = rt.fiber.channels.get_mut(&id) {
        channel.senders += 1;
    }
    rt.gc.alloc(Object::Sender(id))
}

fn maybe_reap_channel(rt: &mut Runtime, id: u64) {
    let reap = rt.fiber.channels.get(&id).is_some_and(|channel| {
        channel.senders == 0
            && !channel.receiver
            && channel.waiting_senders.is_empty()
            && channel.queued.is_empty()
    });
    if reap {
        rt.fiber.channels.remove(&id);
    }
}

#[unsafe(no_mangle)]
unsafe extern "C" fn ril_channel_close(raw: Raw, sender: Value) -> Value {
    // SAFETY: closes the handle synchronously.
    let rt = unsafe { context(raw) };
    let Some(Object::Sender(id)) = rt.gc.object(sender) else {
        return error(rt, "invalid channel sender");
    };
    let id = *id;
    if let Some(channel) = rt.fiber.channels.get_mut(&id) {
        channel.senders = channel.senders.saturating_sub(1);
    }
    if let Some(value) = rt.gc.object_mut(sender) {
        *value = Object::Array(Vec::new());
    }
    rt.fiber.wake.insert(id);
    maybe_reap_channel(rt, id);
    Value::UNIT
}

#[unsafe(no_mangle)]
unsafe extern "C" fn ril_channel_close_recv(raw: Raw, receiver: Value) -> Value {
    // SAFETY: closes the handle synchronously and releases buffered roots.
    let rt = unsafe { context(raw) };
    let Some(Object::Receiver(id)) = rt.gc.object(receiver) else {
        return error(rt, "invalid channel receiver");
    };
    let id = *id;
    if let Some(channel) = rt.fiber.channels.get_mut(&id) {
        channel.receiver = false;
        for item in channel.queued.drain(..) {
            rt.gc.unpin(item);
        }
    }
    rt.fiber.wake.insert(id);
    maybe_reap_channel(rt, id);
    Value::UNIT
}

fn send(raw: Raw, sender: Value, item: Value, blocking: bool) -> Value {
    loop {
        // SAFETY: this borrow ends before waiting or returning to generated code.
        let rt = unsafe { context(raw) };
        let Some(Object::Sender(id)) = rt.gc.object(sender) else {
            return error(rt, "invalid channel sender");
        };
        let id = *id;
        let active = rt.fiber.active;
        let Some(channel) = rt.fiber.channels.get_mut(&id) else {
            let fault = tag(rt, "Closed", Some(item));
            return tag(rt, "Err", Some(fault));
        };
        if channel.delivered.remove(&active) {
            return tag(rt, "Ok", Some(Value::UNIT));
        }
        if !channel.receiver {
            if let Some(item) = channel.withdraw(active) {
                rt.gc.unpin(item);
            }
            maybe_reap_channel(rt, id);
            let fault = tag(rt, "Closed", Some(item));
            return tag(rt, "Err", Some(fault));
        }
        let rendezvous = channel.cap == Some(0);
        if channel.cap.is_none_or(|cap| channel.queued.len() < cap)
            || rendezvous && channel.waiting_receiver && channel.waiting_senders.is_empty()
        {
            channel.waiting_receiver = false;
            channel.queued.push_back(item);
            rt.gc.pin(item);
            rt.fiber.wake.insert(id);
            return tag(rt, "Ok", Some(Value::UNIT));
        }
        if !blocking {
            let fault = tag(rt, "Full", Some(item));
            return tag(rt, "Err", Some(fault));
        }
        if rendezvous
            && !channel
                .waiting_senders
                .iter()
                .any(|&(task, _)| task == active)
        {
            channel.waiting_senders.push_back((active, item));
            rt.gc.pin(item);
            rt.fiber.wake.insert(id);
        }
        if !wait(raw, Event::Channel(id)) {
            // SAFETY: the parked sender has resumed; remove any undelivered item before unwinding.
            let rt = unsafe { context(raw) };
            if let Some(item) = rt
                .fiber
                .channels
                .get_mut(&id)
                .and_then(|channel| channel.withdraw(active))
            {
                rt.gc.unpin(item);
            }
            maybe_reap_channel(rt, id);
            return Value::UNIT;
        }
    }
}

fn receive(raw: Raw, receiver: Value, blocking: bool) -> Value {
    loop {
        // SAFETY: access to the active runtime ends before any suspension.
        let rt = unsafe { context(raw) };
        let Some(Object::Receiver(id)) = rt.gc.object(receiver) else {
            return error(rt, "invalid channel receiver");
        };
        let id = *id;
        let Some(channel) = rt.fiber.channels.get_mut(&id) else {
            if blocking {
                return tag(rt, "None", None);
            }
            let fault = tag(rt, "Closed", None);
            return tag(rt, "Err", Some(fault));
        };
        if let Some(item) = channel.take() {
            rt.gc.unpin(item);
            rt.fiber.wake.insert(id);
            maybe_reap_channel(rt, id);
            return tag(rt, if blocking { "Some" } else { "Ok" }, Some(item));
        }
        if blocking && (!channel.receiver || channel.senders == 0) {
            maybe_reap_channel(rt, id);
            return tag(rt, "None", None);
        }
        if !blocking {
            let name = if !channel.receiver || channel.senders == 0 {
                "Closed"
            } else {
                "Empty"
            };
            maybe_reap_channel(rt, id);
            let fault = tag(rt, name, None);
            return tag(rt, "Err", Some(fault));
        }
        channel.waiting_receiver = channel.cap == Some(0);
        let resumed = wait(raw, Event::Channel(id));
        // SAFETY: the receiver has resumed and owns the endpoint.
        let rt = unsafe { context(raw) };
        if let Some(channel) = rt.fiber.channels.get_mut(&id) {
            channel.waiting_receiver = false;
        }
        if !resumed {
            return Value::UNIT;
        }
    }
}

#[unsafe(no_mangle)]
extern "C" fn ril_channel_send(raw: Raw, sender: Value, item: Value) -> Value {
    send(raw, sender, item, true)
}

#[unsafe(no_mangle)]
extern "C" fn ril_channel_try_send(raw: Raw, sender: Value, item: Value) -> Value {
    send(raw, sender, item, false)
}

#[unsafe(no_mangle)]
extern "C" fn ril_channel_recv(raw: Raw, receiver: Value) -> Value {
    receive(raw, receiver, true)
}

#[unsafe(no_mangle)]
extern "C" fn ril_channel_try_recv(raw: Raw, receiver: Value) -> Value {
    receive(raw, receiver, false)
}

#[unsafe(no_mangle)]
unsafe extern "C" fn ril_channel_drain(raw: Raw, receiver: Value, consumer: Value) -> Value {
    // SAFETY: drop the runtime borrow before calling the consumer.
    let rt = unsafe { context(raw) };
    let Some(Object::Receiver(id)) = rt.gc.object(receiver) else {
        return error(rt, "invalid receiver");
    };
    let id = *id;
    let Some(channel) = rt.fiber.channels.get_mut(&id) else {
        return error(rt, "unknown channel");
    };
    channel.receiver = false;
    let queued = std::mem::take(&mut channel.queued);
    rt.fiber.wake.insert(id);
    for value in queued {
        // SAFETY: synchronous inspection between invocations.
        let active = unsafe { context(raw) }.unwinding == 0;
        if active {
            // SAFETY: the channel consumer has a single payload argument.
            unsafe { invoke(raw, consumer, Some(value)) };
        }
        // SAFETY: this invocation returned and the item no longer needs pinning.
        unsafe { context(raw) }.gc.unpin(value);
    }
    // SAFETY: channel drain finished; reap channel if no endpoints remain.
    maybe_reap_channel(unsafe { context(raw) }, id);
    Value::UNIT
}

pub(super) fn symbols() -> [(&'static str, *const u8); 10] {
    [
        ("ril_channel_bounded", ril_channel_bounded as *const u8),
        ("ril_channel_unbounded", ril_channel_unbounded as *const u8),
        ("ril_channel_clone", ril_channel_clone as *const u8),
        ("ril_channel_close", ril_channel_close as *const u8),
        (
            "ril_channel_close_recv",
            ril_channel_close_recv as *const u8,
        ),
        ("ril_channel_send", ril_channel_send as *const u8),
        ("ril_channel_try_send", ril_channel_try_send as *const u8),
        ("ril_channel_recv", ril_channel_recv as *const u8),
        ("ril_channel_try_recv", ril_channel_try_recv as *const u8),
        ("ril_channel_drain", ril_channel_drain as *const u8),
    ]
}
