//! Buffered transfers suspend through the same native callback trampoline as
//! ordinary calls. Committed prefixes survive error, cancellation and abort.
use super::*;
use crate::{
    byte_string::Bytes,
    io_buffered::{Binding, Invocation, Pending, Phase},
};
#[cfg(test)]
#[path = "ffi_io_buffered_tests.rs"]
mod tests;

pub(super) fn dispatch(
    callable: Handle,
    arguments: Handle,
    continuation: Handle,
    handlers: Handle,
) -> Option<u64> {
    let name = with_runtime(|runtime| match runtime.heap.get(callable) {
        Ok(Object::Builtin(name)) => {
            Some(name.strip_prefix("Prelude::").unwrap_or(name).to_owned())
        }
        _ => None,
    })?;
    if !matches!(
        name.as_str(),
        "Io::read_buffered" | "Io::read_buffered_at" | "Io::write_buffered" | "Io::flush"
    ) {
        return None;
    }
    let prepared: Option<Invocation> = guarded(|runtime| {
        let args = runtime.sequence(arguments)?;
        let explicit_position = name == "Io::read_buffered_at";
        let expected = if explicit_position {
            5
        } else if name == "Io::flush" {
            3
        } else {
            4
        };
        if args.len() != expected {
            return Err(RuntimeError::internal("invalid buffered operation arity"));
        }
        let buffer = args[0];
        let read = matches!(name.as_str(), "Io::read_buffered" | "Io::read_buffered_at");
        let capacity = match runtime.heap.get(buffer)? {
            Object::ReadBuffer(state) if read => state.capacity,
            Object::WriteBuffer(state) if !read => state.capacity,
            _ => return Err(RuntimeError::internal("incorrect buffered stream state")),
        };
        if capacity == 0 {
            return Err(RuntimeError::panic("buffer capacity must be positive"));
        }
        let phase = if read {
            let maximum = usize::try_from(runtime.as_integer(args[3])?)
                .map_err(|_| RuntimeError::panic("negative read count"))?;
            Phase::Read { maximum }
        } else {
            let input = if name == "Io::flush" {
                vec![].into()
            } else {
                let Object::Bytes(bytes) = runtime.heap.get(args[3])? else {
                    return Err(RuntimeError::internal("buffer input is not bytes"));
                };
                bytes.clone()
            };
            Phase::Write {
                validate_empty: input.is_empty(),
                draining: matches!(runtime.heap.get(buffer)?, Object::WriteBuffer(buffer) if !input.is_empty() && buffer.pending.draining()),
                input,
                accepted: 0,
                flush: name == "Io::flush",
            }
        };
        let receiver = args[1];
        if buffer == receiver {
            return Err(RuntimeError::panic("buffer and receiver overlap"));
        }
        let callback = runtime.field(args[2], if read { "read" } else { "write" })?;
        let position = if explicit_position {
            runtime.read_position_identity(args[4])?
        } else {
            receiver
        };
        let mut binding = Binding::new(runtime, receiver, callback)?;
        binding.position = position;
        match runtime.heap.get(buffer)? {
            Object::ReadBuffer(state) => {
                if let Some(previous) = &state.binding {
                    previous.check(&binding)?;
                }
            }
            Object::WriteBuffer(state) => {
                if let Some(previous) = &state.binding {
                    previous.check(&binding)?;
                }
            }
            _ => unreachable!("checked buffer"),
        }
        let cache_hit = matches!(&phase, Phase::Read { maximum } if *maximum > 0)
            && matches!(runtime.heap.get(buffer)?, Object::ReadBuffer(state) if !state.pending.is_empty());
        if read && !cache_hit {
            runtime.check_buffered_position(buffer, position)?;
        }
        let activation = runtime.new_activation()?;
        if read {
            runtime.permit_buffered_read(activation, buffer, receiver, callback)?;
        }
        Ok(Some(Invocation {
            buffer,
            receiver,
            position,
            callback,
            outer: continuation,
            handlers,
            activation,
            offered: Handle::INVALID,
            phase,
        }))
    });
    Some(prepared.map_or(0, advance))
}

enum Action {
    Call(Invocation),
    Done(Invocation, Handle),
}

fn advance(state: Invocation) -> u64 {
    let action: Option<Action> = guarded(|runtime| next(runtime, state).map(Some));
    action.map_or(0, publish)
}

fn next(runtime: &mut Runtime, mut state: Invocation) -> Result<Action> {
    match &mut state.phase {
        Phase::Read { maximum } => {
            let Object::ReadBuffer(buffer) = runtime.heap.get(state.buffer)? else {
                return Err(RuntimeError::internal("lost read buffer"));
            };
            if *maximum > 0 && !buffer.pending.is_empty() {
                let value = take_read(runtime, state.buffer, *maximum)?;
                return Ok(Action::Done(state, value));
            }
            state.offered = runtime.int(if *maximum == 0 {
                0
            } else {
                buffer.capacity as i128
            })?;
            Ok(Action::Call(state))
        }
        Phase::Write {
            input,
            accepted,
            flush,
            validate_empty,
            draining,
        } => {
            let binding = Binding::new(runtime, state.receiver, state.callback)?;
            let Object::WriteBuffer(buffer) = runtime.heap.get_mut(state.buffer)? else {
                return Err(RuntimeError::internal("lost write buffer"));
            };
            if *draining && buffer.pending.is_empty() {
                *draining = false;
            }
            if !*flush && !*draining && *accepted < input.len() {
                let count = (buffer.capacity - buffer.pending.len()).min(input.len() - *accepted);
                buffer
                    .pending
                    .append(&input[*accepted..*accepted + count])?;
                *accepted += count;
                if !buffer.pending.is_empty() {
                    buffer.binding = Some(binding);
                }
            }
            if !*validate_empty
                && ((*flush && buffer.pending.is_empty()) || (!*flush && *accepted == input.len()))
            {
                let value = if *flush {
                    runtime.io_unit_result(Ok(()))?
                } else {
                    runtime.write_progress(*accepted, None)?
                };
                return Ok(Action::Done(state, value));
            }
            let offered = if *validate_empty && !*flush {
                Bytes::from(vec![])
            } else {
                buffer.pending.snapshot()?
            };
            *validate_empty = false;
            if !offered.is_empty() {
                *draining = true;
            }
            state.offered = runtime.allocate(Object::Bytes(offered))?;
            Ok(Action::Call(state))
        }
    }
}

fn take_read(runtime: &mut Runtime, handle: Handle, maximum: usize) -> Result<Handle> {
    let Object::ReadBuffer(buffer) = runtime.heap.get_mut(handle)? else {
        return Err(RuntimeError::internal("lost read buffer"));
    };
    let count = maximum.min(buffer.pending.len());
    let data = buffer.pending.take(count)?;
    let end = buffer.end && buffer.pending.is_empty();
    if buffer.pending.is_empty() {
        buffer.binding = None;
        buffer.end = false;
    }
    let binding = buffer.binding.clone();
    runtime.heap.set_read_reservation(handle, binding);
    let data = runtime.allocate(Object::Bytes(data))?;
    let end = runtime.boolean(end)?;
    let chunk = runtime.allocate(Object::Record(
        [("data".into(), data), ("end".into(), end)].into(),
    ))?;
    runtime.variant("Ok", vec![chunk])
}

fn publish(action: Action) -> u64 {
    match action {
        Action::Call(state) => handle(|runtime| {
            let callback = state.callback;
            let handlers = state.handlers;
            let receiver = state.receiver;
            let offered = state.offered;
            let continuation = runtime.allocate(Object::CpsContinuation {
                state: Continuation::IoBuffered(Box::new(state)),
                used: false,
            })?;
            let arguments = runtime.allocate(Object::Tuple(vec![receiver, offered]))?;
            runtime.allocate(Object::CpsStep(Step::Call {
                callable: callback,
                arguments,
                continuation,
                handlers,
                callback_entry: true,
            }))
        }),
        Action::Done(state, value) => {
            exits::close_return(state.activation, state.outer, value, Some(state.handlers))
        }
    }
}

pub(super) fn resume(state: Invocation, reply: Handle) -> u64 {
    let action: Option<Action> = guarded(|runtime| {
        let action = match state.phase.clone() {
            Phase::Read { maximum } => {
                runtime.validate_read(reply, state.offered)?;
                let Object::Variant { tag, fields } = runtime.heap.get(reply)? else {
                    unreachable!("validated read result");
                };
                if tag == "Err" || maximum == 0 {
                    Action::Done(state, reply)
                } else {
                    let chunk = fields[0];
                    let data = runtime.field(chunk, "data")?;
                    let end = runtime.field(chunk, "end")?;
                    let end = runtime.truth(end)?;
                    let Object::Bytes(data) = runtime.heap.get(data)? else {
                        unreachable!("validated read bytes");
                    };
                    let data = data.clone();
                    let mut binding = Binding::new(runtime, state.receiver, state.callback)?;
                    binding.position = state.position;
                    let Object::ReadBuffer(buffer) = runtime.heap.get_mut(state.buffer)? else {
                        return Err(RuntimeError::internal("lost read buffer"));
                    };
                    buffer.pending = Pending::new(data);
                    buffer.end = end;
                    buffer.binding = Some(binding);
                    let value = take_read(runtime, state.buffer, maximum)?;
                    Action::Done(state, value)
                }
            }
            Phase::Write {
                accepted, flush, ..
            } => {
                runtime.validate_write(reply, state.offered)?;
                let count = runtime.field(reply, "written")?;
                let count = usize::try_from(runtime.as_integer(count)?)
                    .map_err(|_| RuntimeError::internal("invalid validated write count"))?;
                let option = runtime.field(reply, "error")?;
                let error = match runtime.heap.get(option)? {
                    Object::Variant { tag, fields } if tag == "Some" => Some(fields[0]),
                    _ => None,
                };
                let Object::WriteBuffer(buffer) = runtime.heap.get_mut(state.buffer)? else {
                    return Err(RuntimeError::internal("lost write buffer"));
                };
                buffer.pending.take(count)?;
                if buffer.pending.is_empty() {
                    buffer.binding = None;
                }
                if let Some(error) = error {
                    let value = if flush {
                        runtime.variant("Err", vec![error])?
                    } else {
                        runtime.write_progress(accepted, Some(error))?
                    };
                    Action::Done(state, value)
                } else {
                    next(runtime, state)?
                }
            }
        };
        Ok(Some(action))
    });
    action.map_or(0, publish)
}
