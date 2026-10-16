//! Scope-owned channel authorities and host waits. Managed callers retain the
//! send arguments while waiting and acknowledge receive receipts only after
//! publishing the received value under the heap gate. Dropping an Arc never
//! closes authority: task and scope boundaries perform explicit cleanup.
use crate::{
    concurrent::TaskOwner,
    heap::Handle,
    process_io::Cancellation,
    value::{Result, RuntimeError},
};
use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    sync::{Arc, Condvar, Mutex, MutexGuard},
    time::Duration,
};

mod pending;
pub(crate) use pending::{ReceiveFuture, SendFuture};

#[derive(Debug, Clone, Copy)]
pub struct Context<'a> {
    pub owner: TaskOwner,
    pub lineage: &'a [u64],
}
impl Context<'_> {
    fn require_scope(self, scope: u64) -> Result<()> {
        if scope == 0 || !self.lineage.contains(&scope) {
            return Err(RuntimeError::panic(
                "channel authority left its owning scope",
            ));
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Copy)]
enum Kind {
    Sender,
    Receiver,
}

struct Channel {
    scope: u64,
    capacity: usize,
    state: Mutex<State>,
    wake: Condvar,
}
impl std::fmt::Debug for Channel {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Detached endpoints can form channel cycles; never recursively format
        // queued descriptors while debugging an endpoint or a runtime fault.
        formatter
            .debug_struct("Channel")
            .field("scope", &self.scope)
            .field("capacity", &self.capacity)
            .finish_non_exhaustive()
    }
}
#[derive(Debug)]
struct State {
    senders: usize,
    receiver_open: bool,
    scope_closed: bool,
    queued: VecDeque<Message>,
    in_flight: BTreeMap<u64, Message>,
    next_receipt: u64,
    next_waiter: u64,
    waiters: BTreeMap<u64, std::task::Waker>,
}
fn lock<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(|error| error.into_inner())
}

// Publish queue changes before waking either kind of waiter. User-defined
// Wakers never execute while a channel lock is held.
fn notify(channel: &Channel, mut state: MutexGuard<'_, State>) {
    let waiters = std::mem::take(&mut state.waiters);
    channel.wake.notify_all();
    drop(state);
    for waiter in waiters.into_values() {
        waiter.wake();
    }
}

#[derive(Debug, Clone)]
pub struct Sender {
    channel: Arc<Channel>,
    owner: Arc<Mutex<Option<TaskOwner>>>,
}
#[derive(Debug, Clone)]
pub struct Receiver {
    channel: Arc<Channel>,
    owner: Arc<Mutex<Option<TaskOwner>>>,
}
#[derive(Debug, Clone, Copy)]
enum TicketState {
    Owned(TaskOwner),
    Transit,
    Consumed,
}
#[derive(Debug, Clone)]
pub struct Detached {
    channel: Arc<Channel>,
    kind: Kind,
    state: Arc<Mutex<TicketState>>,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Endpoint {
    Sender(Arc<Sender>),
    Receiver(Arc<Receiver>),
}
impl PartialEq for Sender {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.owner, &other.owner)
    }
}
impl Eq for Sender {}
impl PartialEq for Receiver {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.owner, &other.owner)
    }
}
impl Eq for Receiver {}
impl PartialEq for Detached {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.state, &other.state)
    }
}
impl Eq for Detached {}

/// Every reachable detached payload descriptor, including those in aggregates.
/// Repeated entries for the same authority preserve sharing and consume once.
#[derive(Debug, Clone)]
pub struct Message {
    pub value: Handle,
    pub transfers: Vec<(Handle, Arc<Detached>)>,
}
impl Message {
    pub fn new(value: Handle, transfers: Vec<(Handle, Arc<Detached>)>) -> Self {
        Self { value, transfers }
    }
    pub fn references(&self) -> Vec<Handle> {
        let mut roots = vec![self.value];
        roots.extend(self.transfers.iter().map(|(handle, _)| *handle));
        roots.extend(references(
            self.transfers
                .iter()
                .map(|(_, ticket)| ticket.channel.clone())
                .collect(),
        ));
        roots.retain(|handle| *handle != Handle::INVALID);
        roots
    }
    fn move_tickets(self, context: Context<'_>, receiving: bool) -> Result<Self> {
        let mut moved = BTreeMap::<usize, Arc<Detached>>::new();
        let mut transfers = Vec::with_capacity(self.transfers.len());
        for (handle, ticket) in self.transfers {
            let key = Arc::as_ptr(&ticket.state) as usize;
            let next = if let Some(next) = moved.get(&key) {
                next.clone()
            } else {
                match ticket.moved(context, receiving) {
                    Ok(next) => {
                        moved.insert(key, next.clone());
                        next
                    }
                    Err(error) => {
                        close_tickets(moved.into_values().collect());
                        return Err(error);
                    }
                }
            };
            transfers.push((handle, next));
        }
        Ok(Self {
            value: self.value,
            transfers,
        })
    }
}

/// A received message remains traced in the channel until ack/discard. The
/// caller replaces each old managed ticket handle with a fresh heap descriptor,
/// retaining aggregate sharing, before publishing its Result and acknowledging.
#[derive(Debug)]
pub struct Receipt {
    channel: Arc<Channel>,
    id: u64,
    value: Handle,
    replacements: Vec<(Handle, Arc<Detached>)>,
}
impl Receipt {
    pub fn value(&self) -> Handle {
        self.value
    }
    pub fn replacements(&self) -> &[(Handle, Arc<Detached>)] {
        &self.replacements
    }
    pub fn ack(self) {
        lock(&self.channel.state).in_flight.remove(&self.id);
    }
    pub fn discard(self) {
        let message = lock(&self.channel.state).in_flight.remove(&self.id);
        if let Some(message) = message {
            close_tickets(
                message
                    .transfers
                    .into_iter()
                    .map(|(_, ticket)| ticket)
                    .collect(),
            );
        }
    }
}

pub fn bounded(
    capacity: i128,
    scope: u64,
    context: Context<'_>,
) -> Result<(Arc<Sender>, Arc<Receiver>)> {
    let capacity = usize::try_from(capacity)
        .ok()
        .filter(|capacity| *capacity > 0)
        .ok_or_else(|| {
            RuntimeError::panic("channel capacity must be positive and representable")
        })?;
    context.require_scope(scope)?;
    let channel = Arc::new(Channel {
        scope,
        capacity,
        state: Mutex::new(State {
            senders: 1,
            receiver_open: true,
            scope_closed: false,
            queued: VecDeque::new(),
            in_flight: BTreeMap::new(),
            next_receipt: 0,
            next_waiter: 0,
            waiters: BTreeMap::new(),
        }),
        wake: Condvar::new(),
    });
    Ok((
        Arc::new(Sender {
            channel: channel.clone(),
            owner: Arc::new(Mutex::new(Some(context.owner))),
        }),
        Arc::new(Receiver {
            channel,
            owner: Arc::new(Mutex::new(Some(context.owner))),
        }),
    ))
}

fn require_owner(owner: Option<TaskOwner>, context: Context<'_>) -> Result<()> {
    match owner {
        Some(owner) if owner == context.owner => Ok(()),
        Some(_) => Err(RuntimeError::panic(
            "channel endpoint belongs to another task",
        )),
        None => Err(RuntimeError::panic(
            "channel endpoint authority was consumed",
        )),
    }
}
fn take_owner(owner: &Mutex<Option<TaskOwner>>, context: Context<'_>) -> Result<()> {
    let mut owner = lock(owner);
    require_owner(*owner, context)?;
    *owner = None;
    Ok(())
}

impl Sender {
    pub fn scope_id(&self) -> u64 {
        self.channel.scope
    }
    pub fn clone_for(&self, context: Context<'_>) -> Result<Arc<Self>> {
        context.require_scope(self.channel.scope)?;
        // A descendant may borrow a live immutable Sender only as a clone source.
        let owner = lock(&self.owner);
        if owner.is_none() {
            return Err(RuntimeError::panic("channel clone source was consumed"));
        }
        let mut state = lock(&self.channel.state);
        if state.scope_closed {
            return Err(RuntimeError::panic("channel scope has ended"));
        }
        state.senders = state
            .senders
            .checked_add(1)
            .ok_or_else(|| RuntimeError::internal("channel sender count exhausted"))?;
        Ok(Arc::new(Self {
            channel: self.channel.clone(),
            owner: Arc::new(Mutex::new(Some(context.owner))),
        }))
    }
    /// true is Ok(()), false is ChannelError::Closed; cancellation is Err.
    pub fn send(
        &self,
        context: Context<'_>,
        message: Message,
        cancellation: &Cancellation,
    ) -> Result<bool> {
        let message = self.prepare_message(context, message)?;
        let mut state = lock(&self.channel.state);
        loop {
            if cancellation.requested() {
                drop(state);
                discard_message(message);
                return Err(RuntimeError::cancelled());
            }
            if !state.receiver_open || state.scope_closed {
                drop(state);
                discard_message(message);
                return Ok(false);
            }
            if state.queued.len() < self.channel.capacity {
                state.queued.push_back(message);
                notify(&self.channel, state);
                return Ok(true);
            }
            (state, _) = self
                .channel
                .wake
                .wait_timeout(state, Duration::from_millis(5))
                .unwrap_or_else(|error| error.into_inner());
        }
    }

    fn prepare_message(&self, context: Context<'_>, message: Message) -> Result<Message> {
        context.require_scope(self.channel.scope)?;
        require_owner(*lock(&self.owner), context)?;
        let message = message.move_tickets(context, false)?;
        let destination = context
            .lineage
            .iter()
            .position(|scope| *scope == self.channel.scope)
            .expect("validated channel scope");
        if message.transfers.iter().any(|(_, ticket)| {
            context
                .lineage
                .iter()
                .position(|scope| *scope == ticket.channel.scope)
                .is_none_or(|source| source > destination)
        }) {
            discard_message(message);
            return Err(RuntimeError::panic(
                "detached channel payload escapes its owning scope",
            ));
        }
        Ok(message)
    }
    pub fn close(&self, context: Context<'_>) -> Result<()> {
        context.require_scope(self.channel.scope)?;
        take_owner(&self.owner, context)?;
        close_authorities(vec![(self.channel.clone(), Kind::Sender)], vec![]);
        Ok(())
    }
    pub fn detach(&self, context: Context<'_>) -> Result<Arc<Detached>> {
        context.require_scope(self.channel.scope)?;
        take_owner(&self.owner, context)?;
        Ok(Detached::new(
            self.channel.clone(),
            Kind::Sender,
            TicketState::Owned(context.owner),
        ))
    }
    pub fn close_if_owned(&self, owner: TaskOwner) {
        let mut current = lock(&self.owner);
        let matches = *current == Some(owner);
        if matches {
            *current = None;
        }
        drop(current);
        if matches {
            close_authorities(vec![(self.channel.clone(), Kind::Sender)], vec![]);
        }
    }
    pub fn close_in_scope(&self, scope: u64) {
        close_scope(&self.channel, scope);
    }
    pub fn references(&self) -> Vec<Handle> {
        references(vec![self.channel.clone()])
    }
}

impl Receiver {
    pub fn scope_id(&self) -> u64 {
        self.channel.scope
    }
    pub fn recv(
        &self,
        context: Context<'_>,
        cancellation: &Cancellation,
    ) -> Result<Option<Receipt>> {
        context.require_scope(self.channel.scope)?;
        require_owner(*lock(&self.owner), context)?;
        let mut state = lock(&self.channel.state);
        loop {
            if cancellation.requested() {
                return Err(RuntimeError::cancelled());
            }
            if !state.receiver_open || state.scope_closed {
                return Ok(None);
            }
            if !state.queued.is_empty() {
                let id = state
                    .next_receipt
                    .checked_add(1)
                    .ok_or_else(|| RuntimeError::internal("channel receipt identity exhausted"))?;
                // Move between traced domains under one queue lock. An in-flight
                // receipt remains rooted while the native caller reacquires GC.
                let message = state.queued.pop_front().expect("checked nonempty queue");
                state.next_receipt = id;
                state.in_flight.insert(id, message.clone());
                notify(&self.channel, state);
                return self.accept_message(context, id, message).map(Some);
            }
            if state.senders == 0 {
                return Ok(None);
            }
            (state, _) = self
                .channel
                .wake
                .wait_timeout(state, Duration::from_millis(5))
                .unwrap_or_else(|error| error.into_inner());
        }
    }
    fn accept_message(&self, context: Context<'_>, id: u64, message: Message) -> Result<Receipt> {
        // Ticket validation/error cleanup may close this same channel. The
        // in-flight message is rooted before releasing the queue lock.
        let message = match message.move_tickets(context, true) {
            Ok(message) => message,
            Err(error) => {
                let original = lock(&self.channel.state).in_flight.remove(&id);
                if let Some(original) = original {
                    discard_message(original);
                }
                return Err(error);
            }
        };
        let receipt = Receipt {
            channel: self.channel.clone(),
            id,
            value: message.value,
            replacements: message.transfers.clone(),
        };
        let mut state = lock(&self.channel.state);
        if state.scope_closed {
            drop(state);
            discard_message(message);
            return Err(RuntimeError::cancelled());
        }
        state.in_flight.insert(id, message);
        notify(&self.channel, state);
        Ok(receipt)
    }
    pub fn close(&self, context: Context<'_>) -> Result<()> {
        context.require_scope(self.channel.scope)?;
        take_owner(&self.owner, context)?;
        close_authorities(vec![(self.channel.clone(), Kind::Receiver)], vec![]);
        Ok(())
    }
    pub fn detach(&self, context: Context<'_>) -> Result<Arc<Detached>> {
        context.require_scope(self.channel.scope)?;
        take_owner(&self.owner, context)?;
        Ok(Detached::new(
            self.channel.clone(),
            Kind::Receiver,
            TicketState::Owned(context.owner),
        ))
    }
    pub fn close_if_owned(&self, owner: TaskOwner) {
        let mut current = lock(&self.owner);
        let matches = *current == Some(owner);
        if matches {
            *current = None;
        }
        drop(current);
        if matches {
            close_authorities(vec![(self.channel.clone(), Kind::Receiver)], vec![]);
        }
    }
    pub fn close_in_scope(&self, scope: u64) {
        close_scope(&self.channel, scope);
    }
    pub fn references(&self) -> Vec<Handle> {
        references(vec![self.channel.clone()])
    }
}

impl Endpoint {
    pub fn scope_id(&self) -> u64 {
        match self {
            Self::Sender(value) => value.scope_id(),
            Self::Receiver(value) => value.scope_id(),
        }
    }
    pub fn detach(&self, context: Context<'_>) -> Result<Arc<Detached>> {
        match self {
            Self::Sender(value) => value.detach(context),
            Self::Receiver(value) => value.detach(context),
        }
    }
    pub fn close(&self, context: Context<'_>) -> Result<()> {
        match self {
            Self::Sender(value) => value.close(context),
            Self::Receiver(value) => value.close(context),
        }
    }
    pub fn close_if_owned(&self, owner: TaskOwner) {
        match self {
            Self::Sender(value) => value.close_if_owned(owner),
            Self::Receiver(value) => value.close_if_owned(owner),
        }
    }
    pub fn close_in_scope(&self, scope: u64) {
        match self {
            Self::Sender(value) => value.close_in_scope(scope),
            Self::Receiver(value) => value.close_in_scope(scope),
        }
    }
    pub fn references(&self) -> Vec<Handle> {
        match self {
            Self::Sender(value) => value.references(),
            Self::Receiver(value) => value.references(),
        }
    }
}

impl Detached {
    pub(crate) fn identity(&self) -> usize {
        Arc::as_ptr(&self.state) as usize
    }
    pub(crate) fn validate_owner(&self, context: Context<'_>) -> Result<()> {
        context.require_scope(self.channel.scope)?;
        if matches!(*lock(&self.state), TicketState::Owned(owner) if owner == context.owner) {
            Ok(())
        } else {
            Err(RuntimeError::panic(
                "detached channel ticket is consumed or belongs to another task",
            ))
        }
    }
    pub fn scope_id(&self) -> u64 {
        self.channel.scope
    }
    /// Task result transport creates a fresh descriptor as well: transferring
    /// the existing descriptor back to its earlier owner would revive aliases.
    pub fn reissue(&self, source: Context<'_>, target: Context<'_>) -> Result<Arc<Self>> {
        source.require_scope(self.channel.scope)?;
        target.require_scope(self.channel.scope)?;
        let mut state = lock(&self.state);
        if !matches!(*state, TicketState::Owned(owner) if owner == source.owner) {
            return Err(RuntimeError::panic(
                "detached channel ticket reissue has no owner authority",
            ));
        }
        *state = TicketState::Consumed;
        Ok(Self::new(
            self.channel.clone(),
            self.kind,
            TicketState::Owned(target.owner),
        ))
    }
    fn new(channel: Arc<Channel>, kind: Kind, state: TicketState) -> Arc<Self> {
        Arc::new(Self {
            channel,
            kind,
            state: Arc::new(Mutex::new(state)),
        })
    }
    fn moved(&self, context: Context<'_>, receiving: bool) -> Result<Arc<Self>> {
        context.require_scope(self.channel.scope)?;
        let mut state = lock(&self.state);
        let valid = matches!((*state, receiving), (TicketState::Transit, true))
            || matches!((*state, receiving), (TicketState::Owned(owner), false) if owner == context.owner);
        if !valid {
            return Err(RuntimeError::panic(
                "detached channel ticket is consumed or belongs to another task",
            ));
        }
        *state = TicketState::Consumed;
        Ok(Self::new(
            self.channel.clone(),
            self.kind,
            if receiving {
                TicketState::Owned(context.owner)
            } else {
                TicketState::Transit
            },
        ))
    }
    /// Fork capture transfer is separately authorized by the compiler. Existing
    /// aliases in the parent then fail the task-owner check without reviving a
    /// consumed channel-send ticket.
    pub fn transfer_owner(&self, from: TaskOwner, target: Context<'_>) -> Result<()> {
        target.require_scope(self.channel.scope)?;
        let mut state = lock(&self.state);
        if !matches!(*state, TicketState::Owned(owner) if owner == from) {
            return Err(RuntimeError::panic(
                "detached channel ticket transfer has no owner authority",
            ));
        }
        *state = TicketState::Owned(target.owner);
        Ok(())
    }
    pub fn attach(&self, context: Context<'_>) -> Result<Endpoint> {
        context.require_scope(self.channel.scope)?;
        let mut state = lock(&self.state);
        if !matches!(*state, TicketState::Owned(owner) if owner == context.owner) {
            return Err(RuntimeError::panic(
                "detached channel ticket is consumed or belongs to another task",
            ));
        }
        *state = TicketState::Consumed;
        let owner = Arc::new(Mutex::new(Some(context.owner)));
        Ok(match self.kind {
            Kind::Sender => Endpoint::Sender(Arc::new(Sender {
                channel: self.channel.clone(),
                owner,
            })),
            Kind::Receiver => Endpoint::Receiver(Arc::new(Receiver {
                channel: self.channel.clone(),
                owner,
            })),
        })
    }
    pub fn close_if_owned(&self, owner: TaskOwner) {
        let mut state = lock(&self.state);
        let matches = matches!(*state, TicketState::Owned(current) if current == owner);
        if matches {
            *state = TicketState::Consumed;
        }
        drop(state);
        if matches {
            close_authorities(vec![(self.channel.clone(), self.kind)], vec![]);
        }
    }
    pub fn close_in_scope(&self, scope: u64) {
        close_scope(&self.channel, scope);
    }
    pub fn references(&self) -> Vec<Handle> {
        references(vec![self.channel.clone()])
    }
    fn take(&self) -> bool {
        let mut state = lock(&self.state);
        let live = !matches!(*state, TicketState::Consumed);
        *state = TicketState::Consumed;
        live
    }
}

fn close_tickets(tickets: Vec<Arc<Detached>>) {
    close_authorities(vec![], tickets);
}
fn discard_message(message: Message) {
    close_tickets(
        message
            .transfers
            .into_iter()
            .map(|(_, ticket)| ticket)
            .collect(),
    );
}
fn close_authorities(mut pending: Vec<(Arc<Channel>, Kind)>, mut tickets: Vec<Arc<Detached>>) {
    // No channel/ticket lock spans the next work item, even for self-transfers
    // or a cycle of channels containing each other's receiver authority.
    let mut closed_receivers = BTreeSet::new();
    while !pending.is_empty() || !tickets.is_empty() {
        if let Some(ticket) = tickets.pop() {
            if ticket.take() {
                pending.push((ticket.channel.clone(), ticket.kind));
            }
            continue;
        }
        let (channel, kind) = pending.pop().expect("nonempty close worklist");
        if matches!(kind, Kind::Receiver)
            && !closed_receivers.insert(Arc::as_ptr(&channel) as usize)
        {
            continue;
        }
        let mut state = lock(&channel.state);
        match kind {
            Kind::Sender => {
                state.senders = state.senders.saturating_sub(1);
            }
            Kind::Receiver if state.receiver_open => {
                state.receiver_open = false;
                for message in state.queued.drain(..) {
                    tickets.extend(message.transfers.into_iter().map(|(_, ticket)| ticket));
                }
            }
            Kind::Receiver => {}
        }
        notify(&channel, state);
    }
}
fn close_scope(channel: &Arc<Channel>, scope: u64) {
    if channel.scope != scope {
        return;
    }
    let mut state = lock(&channel.state);
    if state.scope_closed {
        return;
    }
    state.scope_closed = true;
    state.receiver_open = false;
    state.senders = 0;
    let mut tickets = Vec::new();
    for message in state.queued.drain(..) {
        tickets.extend(message.transfers.into_iter().map(|(_, ticket)| ticket));
    }
    for message in std::mem::take(&mut state.in_flight).into_values() {
        tickets.extend(message.transfers.into_iter().map(|(_, ticket)| ticket));
    }
    notify(channel, state);
    close_tickets(tickets);
}
fn references(mut pending: Vec<Arc<Channel>>) -> Vec<Handle> {
    let mut visited = BTreeSet::new();
    let mut roots = BTreeSet::new();
    while let Some(channel) = pending.pop() {
        if !visited.insert(Arc::as_ptr(&channel) as usize) {
            continue;
        }
        let state = lock(&channel.state);
        for message in state.queued.iter().chain(state.in_flight.values()) {
            roots.insert(message.value);
            for (handle, ticket) in &message.transfers {
                roots.insert(*handle);
                pending.push(ticket.channel.clone());
            }
        }
    }
    roots.remove(&Handle::INVALID);
    roots.into_iter().collect()
}

#[cfg(test)]
mod tests;
