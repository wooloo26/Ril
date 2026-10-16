//! Native channel calls split managed preparation/publication from host waits.
//! A receive receipt is explicitly acknowledged or discarded on every path.
use super::*;
use crate::{
    channel::{Context, Message, Receipt},
    concurrent::TaskOwner,
    process_io::Cancellation,
};
use std::sync::Arc;

struct CallContext {
    owner: TaskOwner,
    lineage: Vec<u64>,
    cancellation: Arc<Cancellation>,
}
impl CallContext {
    fn from_runtime(runtime: &Runtime) -> Self {
        Self {
            owner: runtime.task_owner,
            lineage: runtime.scope_lineage.clone(),
            cancellation: runtime.host_cancellation(),
        }
    }
    fn authority(&self) -> Context<'_> {
        Context {
            owner: self.owner,
            lineage: &self.lineage,
        }
    }
}

pub(super) fn dispatch(callable: Handle, arguments: Handle, continuation: Handle) -> Option<u64> {
    let name = with_runtime(|runtime| match runtime.heap.get(callable) {
        Ok(Object::Builtin(name)) => {
            let name = name.strip_prefix("Prelude::").unwrap_or(name);
            Some(
                ril_runtime_api::builtins::canonical_builtin(name)
                    .unwrap_or(name)
                    .to_owned(),
            )
        }
        _ => None,
    })?;
    Some(match name.as_str() {
        "Channel::send" => send(arguments, continuation),
        "Channel::recv" => recv(arguments, continuation),
        "Channel::close" => close(arguments, continuation),
        "Channel::bounded" | "Channel::detach" | "Channel::attach" => {
            finite(&name, arguments, continuation)
        }
        _ => return None,
    })
}
fn unary_argument(runtime: &Runtime, arguments: Handle) -> Result<Handle> {
    let arguments = runtime.sequence(arguments)?;
    let [value] = arguments.as_slice() else {
        return Err(RuntimeError::internal(
            "channel operation requires one argument",
        ));
    };
    Ok(*value)
}
fn closed(runtime: &mut Runtime) -> Result<Handle> {
    let error = runtime.variant("Channel::ChannelError::Closed", vec![])?;
    runtime.variant("Err", vec![error])
}
fn finish(value: u64, continuation: Handle) -> u64 {
    if value == 0 {
        0
    } else {
        return_step(continuation, value)
    }
}
fn finite(name: &str, arguments: Handle, continuation: Handle) -> u64 {
    let value = handle(|runtime| {
        let value = unary_argument(runtime, arguments)?;
        match name {
            "Channel::bounded" => runtime.create_channel(runtime.as_integer(value)?),
            "Channel::detach" => {
                let endpoint = runtime.channel_endpoint(value)?;
                let ticket = endpoint.detach(runtime.channel_context())?;
                runtime.allocate_channel_ticket(ticket)
            }
            "Channel::attach" => {
                let Object::ChannelDetached(ticket) = runtime.heap.get(value)? else {
                    return Err(RuntimeError::internal(
                        "attach requires a detached channel ticket",
                    ));
                };
                let endpoint = ticket.attach(runtime.channel_context())?;
                runtime.allocate_channel_endpoint(endpoint)
            }
            _ => Err(RuntimeError::internal("invalid finite channel operation")),
        }
    });
    finish(value, continuation)
}
fn send(arguments: Handle, continuation: Handle) -> u64 {
    // Once arguments were evaluated, detached payloads are consumed even when
    // cancellation is already pending. Sender::send consumes before checking it.
    let prepared = guarded_control(|runtime| send_arguments(runtime, arguments).map(Some));
    let Some((sender, message, context)) = prepared else {
        return 0;
    };
    let outcome = sender.send(context.authority(), message, &context.cancellation);
    finish_send(outcome, continuation)
}
fn send_arguments(
    runtime: &Runtime,
    arguments: Handle,
) -> Result<(Arc<crate::channel::Sender>, Message, CallContext)> {
    let args = runtime.sequence(arguments)?;
    let [sender, value] = args.as_slice() else {
        return Err(RuntimeError::internal("send requires a sender and payload"));
    };
    let Object::ChannelSender(sender) = runtime.heap.get(*sender)? else {
        return Err(RuntimeError::internal("send requires a channel sender"));
    };
    Ok((
        sender.clone(),
        Message::new(*value, runtime.channel_tickets(*value)?),
        CallContext::from_runtime(runtime),
    ))
}
pub(super) fn prepare_send(
    runtime: &Runtime,
    arguments: Handle,
) -> Result<crate::channel::SendFuture> {
    let (sender, message, context) = send_arguments(runtime, arguments)?;
    Ok(sender.send_async(context.authority(), message, context.cancellation.clone()))
}
pub(super) fn finish_send(outcome: Result<bool>, continuation: Handle) -> u64 {
    let value = guarded_control(|runtime| {
        let value = if outcome? {
            runtime.variant("Ok", vec![])?
        } else {
            closed(runtime)?
        };
        runtime.keep_temporary(value);
        Ok(value.0)
    });
    finish(value, continuation)
}
fn recv(arguments: Handle, continuation: Handle) -> u64 {
    let prepared = guarded(|runtime| receive_arguments(runtime, arguments).map(Some));
    let Some((receiver, context)) = prepared else {
        return 0;
    };
    finish_recv(
        receiver.recv(context.authority(), &context.cancellation),
        continuation,
    )
}
fn receive_arguments(
    runtime: &Runtime,
    arguments: Handle,
) -> Result<(Arc<crate::channel::Receiver>, CallContext)> {
    let receiver = unary_argument(runtime, arguments)?;
    let Object::ChannelReceiver(receiver) = runtime.heap.get(receiver)? else {
        return Err(RuntimeError::internal("recv requires a channel receiver"));
    };
    Ok((receiver.clone(), CallContext::from_runtime(runtime)))
}
pub(super) fn prepare_recv(
    runtime: &Runtime,
    arguments: Handle,
) -> Result<crate::channel::ReceiveFuture> {
    let (receiver, context) = receive_arguments(runtime, arguments)?;
    Ok(receiver.recv_async(context.authority(), context.cancellation.clone()))
}
pub(super) fn finish_recv(outcome: Result<Option<Receipt>>, continuation: Handle) -> u64 {
    match outcome {
        Ok(Some(receipt)) => finish_receive(receipt, continuation),
        Ok(None) => finish(handle(closed), continuation),
        Err(error) => {
            guarded_control::<()>(|_| Err(error));
            0
        }
    }
}
fn finish_receive(receipt: Receipt, continuation: Handle) -> u64 {
    let value = handle(|runtime| {
        let payload = runtime.replace_received_tickets(receipt.value(), receipt.replacements())?;
        runtime.variant("Ok", vec![payload])
    });
    if value == 0 {
        // Includes pending cancellation before publication, heap errors, and
        // contained Rust faults. The receipt owns accepted transfer authority.
        receipt.discard();
        0
    } else {
        receipt.ack();
        return_step(continuation, value)
    }
}
fn close(arguments: Handle, continuation: Handle) -> u64 {
    let prepared = guarded(|runtime| {
        let endpoint = runtime.channel_endpoint(unary_argument(runtime, arguments)?)?;
        Ok(Some((endpoint, CallContext::from_runtime(runtime))))
    });
    let Some((endpoint, context)) = prepared else {
        return 0;
    };
    let outcome = endpoint.close(context.authority());
    let value = handle(|runtime| {
        outcome?;
        runtime.unit()
    });
    finish(value, continuation)
}

#[cfg(test)]
#[path = "ffi_channel/tests.rs"]
mod tests;
