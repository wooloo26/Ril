//! Queue predicates and wake registration share the channel lock. Managed
//! callers keep the original call rooted until publication/receipt acknowledgement.
use super::*;
use std::{
    future::Future,
    pin::Pin,
    task::{Context as PollContext, Poll},
};

struct Wait {
    channel: Arc<Channel>,
    cancellation: Arc<Cancellation>,
    cancel_wake: Option<crate::process_io::CancellationWake>,
    id: Option<u64>,
}
impl Wait {
    fn new(channel: Arc<Channel>, cancellation: Arc<Cancellation>) -> Self {
        Self {
            channel,
            cancellation,
            cancel_wake: None,
            id: None,
        }
    }
    fn cancellation_wake(&mut self, context: &PollContext<'_>) -> Result<()> {
        if let Some(wake) = &mut self.cancel_wake {
            wake.refresh(context.waker());
        } else {
            self.cancel_wake = Some(
                self.cancellation
                    .subscribe(context.waker())
                    .map_err(|error| RuntimeError::internal(error.to_string()))?,
            );
        }
        Ok(())
    }
    fn register(&mut self, state: &mut State, context: &PollContext<'_>) -> Result<()> {
        let id = if let Some(id) = self.id {
            id
        } else {
            let id = state
                .next_waiter
                .checked_add(1)
                .ok_or_else(|| RuntimeError::internal("channel waiter identity exhausted"))?;
            state.next_waiter = id;
            self.id = Some(id);
            id
        };
        if state
            .waiters
            .get(&id)
            .is_none_or(|old| !old.will_wake(context.waker()))
        {
            state.waiters.insert(id, context.waker().clone());
        }
        Ok(())
    }
    fn clear(&mut self) {
        if let Some(id) = self.id.take() {
            lock(&self.channel.state).waiters.remove(&id);
        }
        self.cancel_wake = None;
    }
}
impl Drop for Wait {
    fn drop(&mut self) {
        self.clear();
    }
}

pub(crate) struct SendFuture {
    sender: Arc<Sender>,
    owner: TaskOwner,
    lineage: Vec<u64>,
    submitted: Option<Message>,
    prepared: Option<Message>,
    wait: Wait,
    done: bool,
}
impl Sender {
    pub(crate) fn send_async(
        self: &Arc<Self>,
        context: Context<'_>,
        message: Message,
        cancellation: Arc<Cancellation>,
    ) -> SendFuture {
        SendFuture {
            sender: self.clone(),
            owner: context.owner,
            lineage: context.lineage.to_vec(),
            submitted: Some(message),
            prepared: None,
            wait: Wait::new(self.channel.clone(), cancellation),
            done: false,
        }
    }
}
impl Drop for SendFuture {
    fn drop(&mut self) {
        // Only authority already consumed by submission belongs to this wait.
        if let Some(message) = self.prepared.take() {
            discard_message(message);
        }
    }
}
impl Future for SendFuture {
    type Output = Result<bool>;
    fn poll(self: Pin<&mut Self>, context: &mut PollContext<'_>) -> Poll<Self::Output> {
        let this = self.get_mut();
        if this.done {
            return Poll::Ready(Err(RuntimeError::internal(
                "channel send polled after completion",
            )));
        }
        let result = (|| {
            // Submission consumes payload authority even if already cancelled.
            if let Some(message) = this.submitted.take() {
                this.prepared = Some(this.sender.prepare_message(
                    Context {
                        owner: this.owner,
                        lineage: &this.lineage,
                    },
                    message,
                )?);
            }
            this.wait.cancellation_wake(context)?;
            let channel = this.wait.channel.clone();
            let mut state = lock(&channel.state);
            if this.wait.cancellation.requested() {
                return Poll::Ready(Err(RuntimeError::cancelled()));
            }
            if !state.receiver_open || state.scope_closed {
                return Poll::Ready(Ok(false));
            }
            if state.queued.len() < channel.capacity {
                state
                    .queued
                    .push_back(this.prepared.take().expect("prepared send"));
                notify(&channel, state);
                return Poll::Ready(Ok(true));
            }
            this.wait.register(&mut state, context)?;
            Poll::Pending
        })();
        if result.is_ready() {
            this.done = true;
            this.wait.clear();
            if let Some(message) = this.prepared.take() {
                discard_message(message);
            }
        }
        result
    }
}

pub(crate) struct ReceiveFuture {
    receiver: Arc<Receiver>,
    owner: TaskOwner,
    lineage: Vec<u64>,
    wait: Wait,
    done: bool,
}
impl Receiver {
    pub(crate) fn recv_async(
        self: &Arc<Self>,
        context: Context<'_>,
        cancellation: Arc<Cancellation>,
    ) -> ReceiveFuture {
        ReceiveFuture {
            receiver: self.clone(),
            owner: context.owner,
            lineage: context.lineage.to_vec(),
            wait: Wait::new(self.channel.clone(), cancellation),
            done: false,
        }
    }
}
impl Future for ReceiveFuture {
    type Output = Result<Option<Receipt>>;
    fn poll(self: Pin<&mut Self>, context: &mut PollContext<'_>) -> Poll<Self::Output> {
        let this = self.get_mut();
        if this.done {
            return Poll::Ready(Err(RuntimeError::internal(
                "channel receive polled after completion",
            )));
        }
        let result = (|| {
            let authority = Context {
                owner: this.owner,
                lineage: &this.lineage,
            };
            authority.require_scope(this.receiver.channel.scope)?;
            require_owner(*lock(&this.receiver.owner), authority)?;
            this.wait.cancellation_wake(context)?;
            let channel = this.wait.channel.clone();
            let mut state = lock(&channel.state);
            if this.wait.cancellation.requested() {
                return Poll::Ready(Err(RuntimeError::cancelled()));
            }
            if !state.receiver_open || state.scope_closed {
                return Poll::Ready(Ok(None));
            }
            if !state.queued.is_empty() {
                let id = state
                    .next_receipt
                    .checked_add(1)
                    .ok_or_else(|| RuntimeError::internal("channel receipt identity exhausted"))?;
                let message = state.queued.pop_front().expect("nonempty channel");
                state.next_receipt = id;
                state.in_flight.insert(id, message.clone());
                notify(&channel, state);
                return Poll::Ready(
                    this.receiver
                        .accept_message(authority, id, message)
                        .map(Some),
                );
            }
            if state.senders == 0 {
                return Poll::Ready(Ok(None));
            }
            this.wait.register(&mut state, context)?;
            Poll::Pending
        })();
        if result.is_ready() {
            this.done = true;
            this.wait.clear();
        }
        result
    }
}

#[cfg(test)]
mod tests;
