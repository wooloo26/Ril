//! The native ABI is the only module permitted to interpret foreign buffers.
//! Every exported entry contains host unwinding before returning to native code.
#![allow(unsafe_code)]

use crate::{
    heap::{Handle, Object},
    value::{Result, Runtime, RuntimeError},
};
use ril_runtime_api::abi::{BinaryOp, OutcomeTag};
use std::{
    cell::RefCell,
    collections::BTreeMap,
    panic::{AssertUnwindSafe, catch_unwind},
};
#[path = "ffi_cps.rs"]
mod cps;
#[cfg(test)]
#[path = "ffi_host_tests.rs"]
mod host_tests;
#[path = "ffi_order.rs"]
mod order;

thread_local! { static RUNTIME: RefCell<Runtime> = RefCell::new(Runtime::default()); static ENTRY_STARTED: RefCell<bool> = const { RefCell::new(false) }; }

fn with_runtime<T>(operation: impl FnOnce(&mut Runtime) -> T) -> T {
    RUNTIME.with_borrow_mut(|runtime| crate::shared::with_runtime(runtime, operation))
}

fn guarded<T: Default>(operation: impl FnOnce(&mut Runtime) -> Result<T>) -> T {
    guarded_inner(true, operation)
}
fn guarded_control<T: Default>(operation: impl FnOnce(&mut Runtime) -> Result<T>) -> T {
    guarded_inner(false, operation)
}
fn guarded_inner<T: Default>(
    poll_cancellation: bool,
    operation: impl FnOnce(&mut Runtime) -> Result<T>,
) -> T {
    let outcome = catch_unwind(AssertUnwindSafe(|| {
        with_runtime(|runtime| {
            if runtime.fault.is_some() {
                return T::default();
            }
            if poll_cancellation
                && runtime.cancellation_mask == 0
                && runtime.cancellation.requested()
            {
                let mut cancelled = RuntimeError::cancelled();
                cancelled.location = Some(runtime.source_location);
                runtime.fault = Some(cancelled);
                return T::default();
            }
            match operation(runtime) {
                Ok(value) => value,
                Err(mut error) => {
                    error.location.get_or_insert(runtime.source_location);
                    runtime.fault = Some(error);
                    T::default()
                }
            }
        })
    }));
    match outcome {
        Ok(value) => value,
        Err(_) => {
            with_runtime(|runtime| {
                runtime.fault = Some(RuntimeError::internal("unexpected Rust panic in runtime"))
            });
            T::default()
        }
    }
}
fn handle(operation: impl FnOnce(&mut Runtime) -> Result<Handle>) -> u64 {
    guarded(|runtime| {
        let value = operation(runtime)?;
        runtime.keep_temporary(value);
        Ok(value.0)
    })
}
fn handle_control(operation: impl FnOnce(&mut Runtime) -> Result<Handle>) -> u64 {
    guarded_control(|runtime| {
        let value = operation(runtime)?;
        runtime.keep_temporary(value);
        Ok(value.0)
    })
}
/// An unexpected host failure must remain distinguishable from cancellation,
/// including a cancellation arriving while the heap gate was released.
fn finish_host<T>(
    outcome: Result<T>,
    finish: impl FnOnce(&mut Runtime, T) -> Result<Handle>,
) -> u64 {
    match outcome {
        Err(mut error) if error.tag == OutcomeTag::InternalFault => {
            with_runtime(|runtime| {
                error.location.get_or_insert(runtime.source_location);
                runtime.fault = Some(error);
            });
            0
        }
        outcome => handle(|runtime| finish(runtime, outcome?)),
    }
}

/// Replies may acquire host authority before the task next checks cancellation.
/// Discarding that unpublished authority must run outside the managed heap gate.
fn finish_host_with_discard<T>(
    outcome: Result<T>,
    finish: impl FnOnce(&mut Runtime, T) -> Result<Handle>,
    discard: impl FnOnce(T) -> Result<()>,
) -> u64 {
    if matches!(&outcome, Err(error) if error.tag == OutcomeTag::InternalFault) {
        return finish_host(outcome, finish);
    }
    let mut pending = Some(outcome);
    let value = handle(|runtime| finish(runtime, pending.take().expect("unpublished host reply")?));
    if let Some(Ok(reply)) = pending
        && let Err(mut error) = discard(reply)
    {
        with_runtime(|runtime| {
            error.primary = runtime.fault.take().map(Box::new);
            error.location.get_or_insert(runtime.source_location);
            runtime.fault = Some(error);
        });
        return 0;
    }
    value
}

#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_init() {
    RUNTIME.with_borrow_mut(|runtime| *runtime = Runtime::default());
    ENTRY_STARTED.with_borrow_mut(|value| *value = false);
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_require_contract(expected: u32) -> u32 {
    guarded(|_| {
        if expected != ril_runtime_api::CONTRACT_VERSION {
            return Err(RuntimeError::internal(format!(
                "native runtime contract mismatch: expected {expected}, loaded {}",
                ril_runtime_api::CONTRACT_VERSION,
            )));
        }
        Ok(1)
    })
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_enter() {
    guarded_control(|runtime| {
        runtime.enter();
        Ok(())
    });
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_leave(value: u64) -> u64 {
    // Leaving a frame must work during language failure too.
    match catch_unwind(AssertUnwindSafe(|| {
        run_cleanups(0, value);
        with_runtime(|runtime| {
            let value = if runtime.fault.is_some() {
                Handle::INVALID
            } else {
                Handle(value)
            };
            runtime.leave(value).0
        })
    })) {
        Ok(value) => value,
        Err(_) => {
            with_runtime(|runtime| {
                runtime.fault = Some(RuntimeError::internal(
                    "unexpected Rust panic while leaving frame",
                ))
            });
            0
        }
    }
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_scope_enter() -> u32 {
    guarded(|runtime| Ok(runtime.cleanup_marker()))
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_scope_register(resource: u64) -> u64 {
    handle(|runtime| runtime.register_cleanup(Handle(resource)))
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_scope_leave(marker: u32, value: u64) -> u64 {
    match catch_unwind(AssertUnwindSafe(|| run_cleanups(marker, value))) {
        Ok(()) => {
            if ril_rt_status() == 0 {
                value
            } else {
                0
            }
        }
        Err(_) => {
            with_runtime(|runtime| {
                runtime.fault = Some(RuntimeError::internal(
                    "unexpected Rust panic during cleanup",
                ))
            });
            0
        }
    }
}
fn run_cleanups(marker: u32, value: u64) {
    run_cleanup_stack(None, marker, value);
}
struct CleanupAllowanceMask(Option<crate::budget::CleanupMask>);
impl Drop for CleanupAllowanceMask {
    fn drop(&mut self) {
        if let Some(mask) = self.0.take() {
            with_runtime(|runtime| runtime.budgets.restore_after_cleanup(mask));
        }
    }
}
struct CleanupCancellationMask(u32);
impl Drop for CleanupCancellationMask {
    fn drop(&mut self) {
        with_runtime(|runtime| runtime.cancellation_mask = self.0);
    }
}
fn run_cleanup_stack(activation: Option<Handle>, marker: u32, value: u64) {
    let _cancellation = CleanupCancellationMask(with_runtime(|runtime| {
        let previous = runtime.cancellation_mask;
        runtime.cancellation_mask = previous
            .checked_add(1)
            .expect("cleanup cancellation mask depth");
        previous
    }));
    let _allowances = CleanupAllowanceMask(Some(with_runtime(|runtime| {
        runtime.budgets.suspend_for_cleanup()
    })));
    let mut primary = with_runtime(|runtime| {
        runtime.keep_temporary(Handle(value));
        runtime.fault.take()
    });
    if primary.as_ref().is_some_and(|fault| {
        matches!(
            fault.tag,
            OutcomeTag::DoubleFault | OutcomeTag::InternalFault
        )
    }) {
        with_runtime(|runtime| {
            runtime.abandon_cleanup_stack(activation, marker);
            runtime.fault = primary;
        });
        return;
    }
    loop {
        let resource = with_runtime(|runtime| runtime.pop_cleanup_stack(activation, marker));
        let resource = match resource {
            Ok(Some(resource)) => resource,
            Ok(None) => break,
            Err(error) => {
                primary = Some(error);
                break;
            }
        };
        match with_runtime(|runtime| crate::host_cleanup::prepare(runtime, resource)).and_then(
            |action| match action {
                Some(action) => action.perform().map(|()| true),
                None => Ok(false),
            },
        ) {
            Ok(true) => continue,
            Ok(false) => {}
            Err(error) => {
                primary = Some(error);
                break;
            }
        }
        // Read the current field only when exiting. Replacing on_close does
        // not keep a stale callback alive or invoke the initial callback.
        let action = handle(|runtime| runtime.field(resource, "on_close"));
        if action != 0 {
            let arguments = handle(|runtime| runtime.allocate(Object::Tuple(vec![])));
            if arguments != 0 {
                invoke_callable(action, arguments);
            }
        }
        let secondary = with_runtime(|runtime| runtime.fault.take());
        if let Some(secondary) = secondary {
            if matches!(
                secondary.tag,
                OutcomeTag::InternalFault | OutcomeTag::DoubleFault
            ) {
                // A nested cleanup frame has already failed fatally. Preserve
                // its actual two causes and stop this frame too; composing it
                // again would invent a nested UnwindCause that the language
                // does not have, or execute more callbacks after task failure.
                primary = Some(secondary);
                with_runtime(|runtime| runtime.abandon_cleanup_stack(activation, marker));
                break;
            }
            if let Some(previous) = primary.take() {
                primary = Some(RuntimeError::double_fault(previous, secondary));
                with_runtime(|runtime| runtime.abandon_cleanup_stack(activation, marker));
                break;
            }
            primary = Some(secondary);
        }
    }
    with_runtime(|runtime| runtime.fault = primary);
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_begin_entry() {
    ENTRY_STARTED.with_borrow_mut(|value| *value = true);
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_root(slot: u32, value: u64) -> u64 {
    handle_control(|runtime| runtime.root(slot, Handle(value)))
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_statement_end() {
    guarded_control(|runtime| {
        runtime.statement_end();
        Ok(())
    });
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_location(file: u32, start: u32, end: u32) {
    guarded_control(|runtime| {
        runtime.source_location = (file, start, end);
        Ok(())
    });
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_status() -> u32 {
    with_runtime(|runtime| {
        runtime
            .fault
            .as_ref()
            .map_or(OutcomeTag::Running, |error| error.tag) as u32
    })
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_unit() -> u64 {
    handle(Runtime::unit)
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_bool(value: u32) -> u64 {
    handle(|runtime| runtime.boolean(value != 0))
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_int(low: u64, high: u64, bits: u32, signed: u32) -> u64 {
    handle(|runtime| {
        runtime.integer(
            ((u128::from(high) << 64) | u128::from(low)) as i128,
            bits as u8,
            signed != 0,
        )
    })
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_float(value: f64, bits: u32) -> u64 {
    handle(|runtime| runtime.float(value, bits as u8))
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_bigint(value: u64) -> u64 {
    handle(|runtime| {
        let spelling = runtime.as_string(Handle(value))?.to_owned();
        let (negative, digits) = spelling
            .strip_prefix('-')
            .map_or((false, spelling.as_str()), |digits| (true, digits));
        let (radix, digits) = if let Some(digits) = digits
            .strip_prefix("0x")
            .or_else(|| digits.strip_prefix("0X"))
        {
            (16, digits)
        } else if let Some(digits) = digits
            .strip_prefix("0o")
            .or_else(|| digits.strip_prefix("0O"))
        {
            (8, digits)
        } else if let Some(digits) = digits
            .strip_prefix("0b")
            .or_else(|| digits.strip_prefix("0B"))
        {
            (2, digits)
        } else {
            (10, digits)
        };
        let value = num_bigint::BigInt::parse_bytes(digits.as_bytes(), radix)
            .ok_or_else(|| RuntimeError::internal("invalid compiled bigint constant"))?;
        runtime.allocate(Object::BigInteger(if negative { -value } else { value }))
    })
}

/// # Safety
/// `pointer` must designate `length` readable bytes for this call. The generated
/// object owns the static data; the runtime copies it before returning.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn ril_rt_str(pointer: *const u8, length: u64) -> u64 {
    handle(|runtime| {
        let length = usize::try_from(length)
            .map_err(|_| RuntimeError::internal("string length exceeds address space"))?;
        if pointer.is_null() && length != 0 {
            return Err(RuntimeError::internal("null string buffer"));
        }
        let bytes = if length == 0 {
            &[]
        } else {
            // SAFETY: the native emitter supplies a live static byte range.
            unsafe { std::slice::from_raw_parts(pointer, length) }
        };
        let value = std::str::from_utf8(bytes)
            .map_err(|_| RuntimeError::internal("invalid UTF-8 string constant"))?
            .to_owned();
        runtime.string(value)
    })
}
/// # Safety
/// The buffer must be readable for `length` bytes for the duration of this call.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn ril_rt_bytes(pointer: *const u8, length: u64) -> u64 {
    handle(|runtime| {
        let length = usize::try_from(length)
            .map_err(|_| RuntimeError::internal("byte length exceeds address space"))?;
        if pointer.is_null() && length != 0 {
            return Err(RuntimeError::internal("null byte buffer"));
        }
        let bytes = if length == 0 {
            Vec::new()
        } else {
            // SAFETY: the native emitter supplies a live static byte range.
            unsafe { std::slice::from_raw_parts(pointer, length) }.to_vec()
        };
        runtime.allocate(Object::Bytes(bytes.into()))
    })
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_sequence(kind: u32) -> u64 {
    handle(|runtime| {
        runtime.allocate(if kind == 0 {
            Object::Array(vec![])
        } else {
            Object::Tuple(vec![])
        })
    })
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_push(sequence: u64, value: u64) -> u64 {
    handle(|runtime| runtime.append(Handle(sequence), Handle(value)))
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_record() -> u64 {
    handle(|runtime| runtime.allocate(Object::Record(BTreeMap::new())))
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_map() -> u64 {
    handle(|runtime| runtime.allocate(Object::Map(Default::default())))
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_map_set(items: u64, key: u64, value: u64) -> u64 {
    handle(|runtime| {
        runtime.map_set(Handle(items), Handle(key), Handle(value))?;
        Ok(Handle(items))
    })
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_get_field(base: u64, name: u64) -> u64 {
    handle(|runtime| {
        let name = runtime.as_string(Handle(name))?.to_owned();
        runtime.field(Handle(base), &name)
    })
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_set_field(base: u64, name: u64, value: u64) -> u64 {
    handle(|runtime| {
        let name = runtime.as_string(Handle(name))?.to_owned();
        runtime.set_field(Handle(base), name, Handle(value))
    })
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_index(base: u64, index: u64, safe: u32) -> u64 {
    handle(|runtime| runtime.index(Handle(base), Handle(index), safe != 0))
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_set_index(base: u64, index: u64, value: u64) -> u64 {
    handle(|runtime| runtime.set_index(Handle(base), Handle(index), Handle(value)))
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_binary(operation: u32, left: u64, right: u64) -> u64 {
    handle(|runtime| {
        runtime.binary(
            BinaryOp::from_raw(operation)
                .ok_or_else(|| RuntimeError::internal("invalid binary operation"))?,
            Handle(left),
            Handle(right),
        )
    })
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_unary(operation: u32, operand: u64) -> u64 {
    handle(|runtime| runtime.unary(operation, Handle(operand)))
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_truth(value: u64) -> u32 {
    guarded(|runtime| runtime.truth(Handle(value)).map(u32::from))
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_builtin(name: u64, arguments: u64) -> u64 {
    match catch_unwind(AssertUnwindSafe(|| dispatch_builtin(name, arguments))) {
        Ok(value) => value,
        Err(_) => {
            with_runtime(|runtime| {
                runtime.fault = Some(RuntimeError::internal(
                    "unexpected host fault in callback operation",
                ))
            });
            0
        }
    }
}
fn dispatch_builtin(name: u64, arguments: u64) -> u64 {
    guarded(|runtime| runtime.check_read_reservation(Handle(name), Handle(arguments)));
    if ril_rt_status() != 0 {
        return 0;
    }
    let constructor: bool = guarded(|runtime| {
        Ok(matches!(
            runtime.heap.get(Handle(name))?,
            Object::DataConstructor { .. }
        ))
    });
    if constructor {
        return handle(|runtime| runtime.construct(Handle(name), Handle(arguments)));
    }
    let name: Option<String> =
        guarded(|runtime| Ok(Some(runtime.as_string(Handle(name))?.to_owned())));
    let Some(name) = name else {
        return 0;
    };
    let name = name.strip_prefix("Prelude::").unwrap_or(&name);
    let name = ril_runtime_api::builtins::canonical_builtin(name)
        .unwrap_or(name)
        .to_owned();
    if crate::host_stdio::is_operation(&name) {
        let request: Option<crate::host_stdio::Request> = guarded(|runtime| {
            let args = runtime.sequence(Handle(arguments))?;
            crate::host_stdio::prepare(runtime, &name, &args).map(Some)
        });
        let Some(request) = request else {
            return 0;
        };
        // No managed heap access/gate or Runtime borrow survives this wait.
        let reply = request.perform();
        return finish_host(reply, crate::host_stdio::finish);
    }
    if crate::host_service::is_operation(&name) {
        let request: Option<crate::host_service::Request> = guarded(|runtime| {
            let args = runtime.sequence(Handle(arguments))?;
            crate::host_service::prepare(runtime, &name, &args).map(Some)
        });
        let Some(request) = request else {
            return 0;
        };
        let reply = request.perform();
        return finish_host(reply, crate::host_service::finish);
    }
    if crate::process::host::is_operation(&name) {
        let request: Option<crate::process::host::Request> = guarded(|runtime| {
            let args = runtime.sequence(Handle(arguments))?;
            crate::process::host::prepare(runtime, &name, &args).map(Some)
        });
        let Some(request) = request else {
            return 0;
        };
        let reply = request.perform();
        return finish_host_with_discard(
            reply,
            crate::process::host::finish,
            crate::process::host::discard,
        );
    }
    if crate::file::host::is_operation(&name) {
        let request: Option<crate::file::host::Request> = guarded(|runtime| {
            let args = runtime.sequence(Handle(arguments))?;
            crate::file::host::prepare(runtime, &name, &args).map(Some)
        });
        let Some(request) = request else {
            return 0;
        };
        let reply = request.perform();
        return finish_host(reply, crate::file::host::finish);
    }
    if crate::file::filesystem::is_operation(&name) {
        let request: Option<crate::file::filesystem::Request> = guarded(|runtime| {
            let args = runtime.sequence(Handle(arguments))?;
            crate::file::filesystem::prepare(runtime, &name, &args).map(Some)
        });
        let Some(request) = request else {
            return 0;
        };
        let reply = request.perform();
        return finish_host(reply, crate::file::filesystem::finish);
    }
    if matches!(
        name.as_str(),
        "Options::map"
            | "Options::and_then"
            | "Options::unwrap_or_else"
            | "Results::map"
            | "Results::map_err"
            | "Results::and_then"
            | "Results::recover"
    ) {
        return variant_operation(&name, arguments);
    }
    if matches!(name.as_str(), "Order::sorted" | "Order::binary_search")
        || name.starts_with("Heap::")
    {
        return order::invoke(&name, arguments);
    }
    if matches!(
        name.as_str(),
        "Array::map"
            | "Array::filter"
            | "Array::fold"
            | "Array::find"
            | "Array::any"
            | "Array::all"
            | "Array::for_each"
    ) {
        return array_callback(&name, arguments);
    }
    handle(|runtime| runtime.builtin(&name, Handle(arguments)))
}
fn invoke_callable(callback: u64, arguments: u64) -> u64 {
    if ril_rt_read_reservation_check(callback, arguments) == 0 {
        return 0;
    }
    if cps::ril_rt_is_cps(callback) != 0 {
        return handle(|_| {
            Err(RuntimeError::internal(
                "suspending callback requires a native continuation bridge",
            ))
        });
    }
    let address = ril_rt_function(callback);
    if ril_rt_status() != 0 {
        return 0;
    }
    if address == 0 {
        return ril_rt_builtin(callback, arguments);
    }
    let environment = ril_rt_environment(callback);
    if environment == 0 {
        return 0;
    }
    invoke_address(address, environment, arguments)
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_read_reservation_check(callable: u64, arguments: u64) -> u32 {
    guarded(|runtime| {
        runtime.check_read_reservation(Handle(callable), Handle(arguments))?;
        Ok(1)
    })
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_read_reservation_native(
    function: u64,
    environment: u64,
    arguments: u64,
) -> u32 {
    guarded(|runtime| {
        runtime.check_native_read_reservation(function, Handle(environment), Handle(arguments))?;
        Ok(1)
    })
}
fn invoke_address(address: u64, environment: u64, arguments: u64) -> u64 {
    if ril_rt_read_reservation_native(address, environment, arguments) == 0 {
        return 0;
    }
    // SAFETY: closure addresses are minted by the native emitter, whose uniform
    // C ABI is (environment handle, argument-tuple handle) -> result handle.
    // No runtime borrow is held across invocation, so callbacks may re-enter.
    let function: extern "C" fn(u64, u64) -> u64 = unsafe { std::mem::transmute(address as usize) };
    function(environment, arguments)
}
fn variant_operation(name: &str, arguments: u64) -> u64 {
    ril_rt_enter();
    ril_rt_root(0, arguments);
    let inputs: Option<(Vec<Handle>, String, Vec<Handle>)> = guarded(|runtime| {
        let args = runtime.sequence(Handle(arguments))?;
        let input = args
            .first()
            .ok_or_else(|| RuntimeError::internal("missing variant input"))?;
        let Object::Variant { tag, fields } = runtime.heap.get(*input)? else {
            return Err(RuntimeError::internal("expected variant input"));
        };
        let valid = if name.starts_with("Options::") {
            (tag == "Some" && fields.len() == 1) || (tag == "None" && fields.is_empty())
        } else {
            matches!(tag.as_str(), "Ok" | "Err") && fields.len() == 1
        };
        if !valid || args.len() != 2 {
            return Err(RuntimeError::internal(
                "invalid variant operation arguments",
            ));
        }
        Ok(Some((args, tag.clone(), fields.clone())))
    });
    let Some((args, tag, fields)) = inputs else {
        return ril_rt_leave(0);
    };
    let success = matches!(tag.as_str(), "Some" | "Ok");
    let needs_callback = match name {
        "Options::map" | "Options::and_then" | "Results::map" | "Results::and_then" => success,
        "Options::unwrap_or_else" | "Results::map_err" | "Results::recover" => !success,
        _ => false,
    };
    let value = if needs_callback {
        let callback_args = ril_rt_sequence(1);
        if name != "Options::unwrap_or_else" {
            ril_rt_push(callback_args, fields[0].0);
        }
        let value = invoke_callable(args[1].0, callback_args);
        if value == 0 {
            return ril_rt_leave(0);
        }
        match name {
            "Options::map" | "Results::map" | "Results::map_err" => {
                handle(|runtime| runtime.variant(&tag, vec![Handle(value)]))
            }
            _ => value,
        }
    } else {
        match name {
            "Options::unwrap_or_else" | "Results::recover" => fields[0].0,
            _ => args[0].0,
        }
    };
    ril_rt_leave(value)
}
fn array_callback(name: &str, arguments: u64) -> u64 {
    let inputs: Option<(Vec<Handle>, u64)> = guarded(|runtime| {
        let args = runtime.sequence(Handle(arguments))?;
        let input = args
            .first()
            .copied()
            .ok_or_else(|| RuntimeError::internal("missing collection argument"))?;
        if !matches!(runtime.heap.get(input)?, Object::Array(_)) {
            return Err(RuntimeError::internal("expected callback array"));
        }
        Ok(Some((args, runtime.length(input)?)))
    });
    let Some((args, count)) = inputs else {
        return 0;
    };
    let callback_index = if name == "Array::fold" { 2 } else { 1 };
    let Some(callback) = args.get(callback_index).copied() else {
        return handle(|_| Err(RuntimeError::internal("missing collection callback")));
    };
    ril_rt_enter();
    ril_rt_root(0, arguments);
    let output = ril_rt_sequence(0);
    ril_rt_root(1, output);
    let mut accumulator = args.get(1).copied().unwrap_or(Handle::INVALID).0;
    if name == "Array::fold" {
        ril_rt_root(2, accumulator);
    }
    let mut selected = None;
    for index in 0..count {
        let item = handle(|runtime| match runtime.heap.get(args[0])? {
            Object::Array(items) => items
                .get(index as usize)
                .copied()
                .ok_or_else(|| RuntimeError::internal("array changed during traversal")),
            _ => Err(RuntimeError::internal("expected callback array")),
        });
        if item == 0 {
            return ril_rt_leave(0);
        }
        let item = Handle(item);
        let callback_args = ril_rt_sequence(1);
        if name == "Array::fold" {
            ril_rt_push(callback_args, accumulator);
        }
        ril_rt_push(callback_args, item.0);
        let value = invoke_callable(callback.0, callback_args);
        if value == 0 {
            return ril_rt_leave(0);
        }
        match name {
            "Array::map" => {
                ril_rt_push(output, value);
            }
            "Array::filter" => {
                if ril_rt_truth(value) != 0 {
                    ril_rt_push(output, item.0);
                }
            }
            "Array::fold" => {
                accumulator = value;
                ril_rt_root(2, value);
            }
            "Array::find" | "Array::any" | "Array::all" => {
                let truth = ril_rt_truth(value) != 0;
                if truth != (name == "Array::all") {
                    selected = Some(item);
                    break;
                }
            }
            _ => {}
        }
        if ril_rt_status() != 0 {
            return ril_rt_leave(0);
        }
        ril_rt_statement_end();
    }
    let result = match name {
        "Array::fold" => accumulator,
        "Array::find" => handle(|runtime| {
            runtime.variant(
                if selected.is_some() { "Some" } else { "None" },
                selected.into_iter().collect(),
            )
        }),
        "Array::any" => ril_rt_bool(u32::from(selected.is_some())),
        "Array::all" => ril_rt_bool(u32::from(selected.is_none())),
        "Array::for_each" => ril_rt_unit(),
        _ => output,
    };
    ril_rt_leave(result)
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_builtin_value(name: u64) -> u64 {
    handle(|runtime| {
        let name = runtime.as_string(Handle(name))?.to_owned();
        let constant = match name.as_str() {
            "Math::PI" => Some((std::f64::consts::PI, 64)),
            "Math::TAU" => Some((std::f64::consts::TAU, 64)),
            "Math::PI_F32" => Some((f64::from(std::f32::consts::PI), 32)),
            "Math::TAU_F32" => Some((f64::from(std::f32::consts::TAU), 32)),
            _ => None,
        };
        if let Some((value, bits)) = constant {
            return runtime.float(value, bits);
        }
        if ril_runtime_api::builtins::constant(&name) {
            return runtime.variant(&name, vec![]);
        }
        runtime.allocate(Object::Builtin(name))
    })
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_variant(tag: u64, arguments: u64) -> u64 {
    handle(|runtime| {
        let tag = runtime.as_string(Handle(tag))?.to_owned();
        let args = runtime.sequence(Handle(arguments))?;
        runtime.variant(&tag, args)
    })
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_closure(function: u64, environment: u64) -> u64 {
    handle(|runtime| {
        runtime.heap.get(Handle(environment))?;
        runtime.allocate(Object::Closure {
            function,
            environment: Handle(environment),
        })
    })
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_function(value: u64) -> u64 {
    guarded(|runtime| match runtime.heap.get(Handle(value))? {
        Object::Closure { function, .. } if !runtime.budgets.is_active() => Ok(*function),
        Object::BudgetClosure {
            normal,
            normal_is_cps: false,
            ..
        } if !runtime.budgets.is_active() => Ok(*normal),
        Object::Closure { .. } | Object::CpsClosure { .. } | Object::BudgetClosure { .. } => {
            Err(RuntimeError::internal(
                "a suspending or metered callable cannot use the direct managed calling convention",
            ))
        }
        Object::Builtin(_) | Object::DataConstructor { .. } => Ok(0),
        _ => Err(RuntimeError::internal("value is not callable")),
    })
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_callable_with_budget(
    normal: u64,
    metered: u64,
    environment: u64,
    flags: u32,
) -> u64 {
    handle(|runtime| {
        runtime.heap.get(Handle(environment))?;
        use ril_runtime_api::abi::{CALLABLE_METERED_ENTRY_EVENT, CALLABLE_NORMAL_IS_CPS};
        if normal == 0
            || metered == 0
            || flags & !(CALLABLE_METERED_ENTRY_EVENT | CALLABLE_NORMAL_IS_CPS) != 0
        {
            return Err(RuntimeError::internal("invalid dual-entry native callable"));
        }
        runtime.heap.register_native_entries(normal, metered);
        runtime.allocate(Object::BudgetClosure {
            normal,
            metered,
            environment: Handle(environment),
            normal_is_cps: flags & CALLABLE_NORMAL_IS_CPS != 0,
            metered_entry_event: flags & CALLABLE_METERED_ENTRY_EVENT != 0,
        })
    })
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_environment(value: u64) -> u64 {
    handle(|runtime| match runtime.heap.get(Handle(value))? {
        Object::Closure { environment, .. } | Object::CpsClosure { environment, .. } => {
            Ok(*environment)
        }
        Object::BudgetClosure { environment, .. } => Ok(*environment),
        _ => Err(RuntimeError::internal("value has no environment")),
    })
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_apply_builtin(value: u64, arguments: u64) -> u64 {
    ril_rt_builtin(value, arguments)
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_global_get(name: u64) -> u64 {
    handle(|runtime| {
        let name = runtime.as_string(Handle(name))?;
        runtime
            .globals
            .get(name)
            .copied()
            .ok_or_else(|| RuntimeError::internal("global not initialized"))
    })
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_global_set(name: u64, value: u64) -> u64 {
    handle(|runtime| {
        let name = runtime.as_string(Handle(name))?.to_owned();
        runtime.heap.get(Handle(value))?;
        runtime.globals.insert(name, Handle(value));
        Ok(Handle(value))
    })
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_length(value: u64) -> u64 {
    guarded(|runtime| runtime.length(Handle(value)))
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_range(lower: u64, upper: u64, inclusive: u32) -> u64 {
    handle(|runtime| {
        for endpoint in [lower, upper] {
            if endpoint != 0
                && !matches!(
                    runtime.heap.get(Handle(endpoint))?,
                    Object::Integer { .. } | Object::BigInteger(_)
                )
            {
                return Err(RuntimeError::internal("range endpoint is not an integer"));
            }
        }
        runtime.allocate(Object::Range {
            lower: (lower != 0).then_some(Handle(lower)),
            upper: (upper != 0).then_some(Handle(upper)),
            inclusive: inclusive != 0,
        })
    })
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_len(value: u64) -> u64 {
    ril_rt_length(value)
}
/// Check the container and complete arity before a pattern reads any slot.
/// Unit is the zero-component tuple; ordinary len keeps its original domain.
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_sequence_matches(value: u64, array: u32, minimum: u64, rest: u32) -> u32 {
    guarded(|runtime| {
        let length = match runtime.heap.get(Handle(value))? {
            Object::Unit if array == 0 => 0,
            Object::Tuple(values) if array == 0 => values.len() as u64,
            Object::Array(values) if array != 0 => values.len() as u64,
            Object::ArrayWindow { len, .. } if array != 0 => *len as u64,
            _ => return Ok(0),
        };
        Ok(u32::from(if rest == 0 {
            length == minimum
        } else {
            length >= minimum
        }))
    })
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_contains(element: u64, collection: u64) -> u64 {
    handle(|runtime| runtime.contains(Handle(element), Handle(collection)))
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_iter_start(source: u64) -> u64 {
    handle(|runtime| runtime.iterator(Handle(source)))
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_iter_next(cursor: u64) -> u64 {
    handle(|runtime| {
        let next = runtime.iterator_next(Handle(cursor))?;
        runtime.variant(
            if next.is_some() { "Some" } else { "None" },
            next.into_iter().collect(),
        )
    })
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_iter_item(cursor: u64, index: u64) -> u64 {
    handle(|runtime| runtime.iterator_item(Handle(cursor), index))
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_callable(address: u64, environment: u64) -> u64 {
    ril_rt_closure(address, environment)
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_callable_address(value: u64) -> u64 {
    ril_rt_function(value)
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_callable_environment(value: u64) -> u64 {
    ril_rt_environment(value)
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_callable_instantiate(value: u64, choices: u64) -> u64 {
    handle(|runtime| runtime.instantiate_callable(Handle(value), Handle(choices)))
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_uninstantiated_callable(template: u64) -> u64 {
    handle(|_| {
        Err(RuntimeError::internal(format!(
            "uninstantiated callable template {template} was invoked"
        )))
    })
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_clone(value: u64, _immutable: u32) -> u64 {
    handle(|runtime| runtime.copy(Handle(value)))
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_cell(value: u64) -> u64 {
    handle(|runtime| {
        runtime.heap.get(Handle(value))?;
        runtime.allocate(Object::Cell(Handle(value)))
    })
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_cell_get(value: u64) -> u64 {
    handle(|runtime| match runtime.heap.get(Handle(value))? {
        Object::Cell(value) => Ok(*value),
        _ => Err(RuntimeError::internal("expected binding cell")),
    })
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_cell_set(cell: u64, value: u64) -> u64 {
    handle(|runtime| {
        runtime.heap.get(Handle(value))?;
        match runtime.heap.get_mut(Handle(cell))? {
            Object::Cell(target) => {
                *target = Handle(value);
                Ok(Handle(value))
            }
            _ => Err(RuntimeError::internal("expected binding cell")),
        }
    })
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_variant_is(value: u64, tag: u64) -> u32 {
    guarded(|runtime| {
        let expected = runtime.as_string(Handle(tag))?;
        match runtime.heap.get(Handle(value))? {
            Object::Variant { tag, .. } | Object::Nominal { tag, .. } => {
                fn canonical(tag: &str) -> &str {
                    match tag {
                        "Prelude::Some" => "Some",
                        "Prelude::None" => "None",
                        "Prelude::Ok" => "Ok",
                        "Prelude::Err" => "Err",
                        _ => tag,
                    }
                }
                Ok(u32::from(canonical(tag) == canonical(expected)))
            }
            _ => Ok(0),
        }
    })
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_variant_field(value: u64, index: u32) -> u64 {
    handle(|runtime| match runtime.heap.get(Handle(value))? {
        Object::Variant { fields, .. } => fields
            .get(index as usize)
            .copied()
            .ok_or_else(|| RuntimeError::internal("variant field is absent")),
        Object::Nominal { payload, .. } if index == 0 => Ok(*payload),
        _ => Err(RuntimeError::internal("expected variant")),
    })
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_constructor(tag: u64, nominal: u32, has_payload: u32) -> u64 {
    handle(|runtime| {
        let tag = runtime.as_string(Handle(tag))?.to_owned();
        runtime.constructor(tag, nominal != 0, has_payload != 0)
    })
}
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_record_copy(value: u64) -> u64 {
    handle(|runtime| {
        let object = runtime.heap.get(Handle(value))?.clone();
        if !matches!(object, Object::Record(_)) {
            return Err(RuntimeError::internal("expected record"));
        }
        runtime.allocate(object)
    })
}

/// Copy only the container: remainder fields retain their original child
/// handles, including cycles, shared fields and opaque runtime payloads.
#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_record_without(value: u64, excluded: u64) -> u64 {
    handle(|runtime| {
        let labels = runtime
            .heap
            .array_elements(Handle(excluded))?
            .ok_or_else(|| RuntimeError::internal("record remainder exclusions are not an array"))?
            .iter()
            .map(|label| runtime.as_string(*label).map(str::to_owned))
            .collect::<Result<std::collections::BTreeSet<_>>>()?;
        let Object::Record(fields) = runtime.heap.get(Handle(value))? else {
            return Err(RuntimeError::internal(
                "record remainder source is not a record",
            ));
        };
        let fields = fields
            .iter()
            .filter(|(label, _)| !labels.contains(*label))
            .map(|(label, value)| (label.clone(), *value))
            .collect();
        runtime.allocate(Object::Record(fields))
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_record_merge(target: u64, source: u64) -> u64 {
    handle(|runtime| {
        let fields = match runtime.heap.get(Handle(source))? {
            Object::Record(fields) => fields.clone(),
            _ => {
                return Err(RuntimeError::internal(
                    "record spread source is not a record",
                ));
            }
        };
        match runtime.heap.get_mut(Handle(target))? {
            Object::Record(target) => target.extend(fields),
            _ => {
                return Err(RuntimeError::internal(
                    "record spread target is not a record",
                ));
            }
        };
        Ok(Handle(target))
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn ril_rt_finish(value: u64) -> i32 {
    let outcome = catch_unwind(AssertUnwindSafe(|| {
        with_runtime(|runtime| {
            let (kind, exit, message) = if let Some(error) = &runtime.fault {
                (
                    match error.tag {
                        OutcomeTag::LanguagePanic => "language-panic",
                        OutcomeTag::Cancelled => "cancelled",
                        OutcomeTag::DoubleFault => "double-fault",
                        _ => "native-crash",
                    },
                    1,
                    Some(error.message.clone()),
                )
            } else {
                match runtime.heap.get(Handle(value)) {
                    Ok(Object::Unit) => ("returned-unit", 0, None),
                    Ok(Object::Variant { tag, .. }) if tag == "Ok" => ("returned-ok", 0, None),
                    Ok(Object::Variant { tag, fields }) if tag == "Err" => {
                        let text = fields
                            .first()
                            .and_then(|value| runtime.format(*value).ok())
                            .unwrap_or_else(|| "returned Err".into());
                        ("returned-err", 1, Some(text))
                    }
                    _ => ("native-crash", 1, Some("invalid program result".into())),
                }
            };
            if let Some(message) = &message {
                let _ = crate::platform_stdio::write_all(format!("{message}\n").as_bytes(), true);
            }
            if let Some(mut path) = std::env::var_os("RIL_EXECUTION_REPORT") {
                let pid = std::process::id();
                path.push(format!(".{pid}"));
                let (file, start, end) = runtime
                    .fault
                    .as_ref()
                    .and_then(|error| error.location)
                    .unwrap_or(runtime.source_location);
                let origin = ENTRY_STARTED.with_borrow(|started| {
                    if *started {
                        "designated-operation"
                    } else {
                        "fixture-setup"
                    }
                });
                fn cause(error: &RuntimeError) -> serde_json::Value {
                    serde_json::json!({"tag":error.tag as u32,"message":error.message,"location":error.location,"primary":error.primary.as_ref().map(|error|cause(error)),"cleanup":error.cleanup.as_ref().map(|error|cause(error))})
                }
                let report = serde_json::json!({"pid":pid,"runtime":kind,"exit":exit,"origin":origin,"message":message,"span":{"file":file,"start":start,"end":end},"cause":runtime.fault.as_ref().map(cause)});
                if let Err(error) = std::fs::write(path, report.to_string()) {
                    let _ = crate::platform_stdio::write_all(
                        format!("cannot write execution report: {error}\n").as_bytes(),
                        true,
                    );
                    return 1;
                }
            }
            exit
        })
    }));
    outcome.unwrap_or(1)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn record_remainders_keep_child_identity_and_exclude_only_written_fields() {
        ril_rt_init();
        ril_rt_enter();
        let source = ril_rt_record();
        let shared = ril_rt_sequence(0);
        let item = ril_rt_int(7, 0, 64, 1);
        ril_rt_push(shared, item);
        let key = |name: &str| handle(|runtime| runtime.string(name.to_owned()));
        ril_rt_set_field(source, key("drop"), item);
        ril_rt_set_field(source, key("left"), shared);
        ril_rt_set_field(source, key("right"), shared);
        ril_rt_set_field(source, key("self"), source);
        let excluded = ril_rt_sequence(0);
        ril_rt_push(excluded, key("drop"));
        let result = ril_rt_record_without(source, excluded);
        assert_ne!(result, source);
        ril_rt_root(0, result);
        ril_rt_statement_end();
        with_runtime(|runtime| {
            runtime.collect().unwrap();
            let Object::Record(fields) = runtime.heap.get(Handle(result)).unwrap() else {
                panic!("record remainder");
            };
            assert!(!fields.contains_key("drop"));
            assert_eq!(fields["left"], Handle(shared));
            assert_eq!(fields["right"], Handle(shared));
            assert_eq!(fields["self"], Handle(source));
            assert_eq!(runtime.field(Handle(source), "drop").unwrap(), Handle(item));
        });
        assert_eq!(ril_rt_status(), 0);
        ril_rt_leave(result);
    }

    #[test]
    fn sequence_patterns_distinguish_unit_and_arrays_without_changing_language_len() {
        ril_rt_init();
        ril_rt_enter();
        let unit = ril_rt_unit();
        assert_eq!(ril_rt_sequence_matches(unit, 0, 0, 0), 1);
        assert_eq!(ril_rt_sequence_matches(unit, 1, 0, 0), 0);
        assert_eq!(ril_rt_sequence_matches(unit, 0, 1, 1), 0);
        assert_eq!(ril_rt_status(), 0);
        with_runtime(|runtime| assert!(runtime.length(Handle(unit)).is_err()));
        let tuple = ril_rt_sequence(1);
        ril_rt_push(tuple, unit);
        assert_eq!(ril_rt_sequence_matches(tuple, 0, 1, 0), 1);
        assert_eq!(ril_rt_sequence_matches(tuple, 0, 2, 1), 0);
        assert_eq!(ril_rt_sequence_matches(tuple, 1, 1, 0), 0);
        let array = ril_rt_sequence(0);
        assert_eq!(ril_rt_sequence_matches(array, 1, 0, 0), 1);
        assert_eq!(ril_rt_sequence_matches(array, 0, 0, 0), 0);
        ril_rt_leave(tuple);
    }
    #[test]
    fn direct_callable_addresses_cannot_misinterpret_a_native_step_as_a_value() {
        for (suspends, metered) in [(false, false), (true, false), (false, true)] {
            ril_rt_init();
            let environment = ril_rt_unit();
            let flags = if suspends {
                ril_runtime_api::abi::CALLABLE_NORMAL_IS_CPS
            } else {
                0
            };
            let callable = ril_rt_callable_with_budget(17, 19, environment, flags);
            if metered {
                with_runtime(|runtime| runtime.budgets.begin(10, Handle(environment)).unwrap());
            }
            let address = ril_rt_callable_address(callable);
            with_runtime(|runtime| {
                if suspends || metered {
                    assert_eq!(address, 0);
                    assert_eq!(
                        runtime.fault.as_ref().unwrap().tag,
                        OutcomeTag::InternalFault
                    );
                } else {
                    assert_eq!(address, 17);
                    assert!(runtime.fault.is_none());
                }
            });
        }
        ril_rt_init();
        let environment = ril_rt_unit();
        let callable = cps::ril_rt_cps_callable(17, environment);
        assert_eq!(ril_rt_callable_address(callable), 0);
        with_runtime(|runtime| {
            assert_eq!(
                runtime.fault.as_ref().unwrap().tag,
                OutcomeTag::InternalFault
            )
        });
    }
    #[test]
    fn publishing_host_failure_does_not_convert_it_to_cancellation() {
        ril_rt_init();
        with_runtime(|runtime| runtime.cancellation.request());
        assert_eq!(
            finish_host::<()>(
                Err(RuntimeError::internal("host failed")),
                |_, _| unreachable!()
            ),
            0
        );
        with_runtime(|runtime| {
            assert_eq!(
                runtime.fault.as_ref().unwrap().tag,
                OutcomeTag::InternalFault
            )
        });
        ril_rt_init();
        with_runtime(|runtime| runtime.cancellation.request());
        assert_eq!(finish_host(Ok(()), |runtime, ()| runtime.unit()), 0);
        with_runtime(|runtime| {
            assert_eq!(runtime.fault.as_ref().unwrap().tag, OutcomeTag::Cancelled)
        });
    }
    #[test]
    fn a_mismatched_native_runtime_contract_fails_before_language_execution() {
        ril_rt_init();
        assert_eq!(
            ril_rt_require_contract(ril_runtime_api::CONTRACT_VERSION),
            1
        );
        assert_eq!(ril_rt_status(), 0);
        assert_eq!(
            ril_rt_require_contract(ril_runtime_api::CONTRACT_VERSION + 1),
            0
        );
        with_runtime(|runtime| {
            assert_eq!(
                runtime.fault.as_ref().unwrap().tag,
                OutcomeTag::InternalFault
            );
        });
    }
    extern "C" fn double(_environment: u64, arguments: u64) -> u64 {
        ril_rt_enter();
        ril_rt_root(0, arguments);
        let index = ril_rt_int(0, 0, 64, 1);
        let value = ril_rt_index(arguments, index, 0);
        ril_rt_root(1, value);
        let two = ril_rt_int(2, 0, 64, 1);
        let result = ril_rt_binary(BinaryOp::Multiply as u32, value, two);
        ril_rt_leave(result)
    }
    #[test]
    fn callback_operations_release_runtime_borrows_and_keep_roots_during_reentry() {
        callback_reentry(false);
    }
    #[test]
    fn shared_heap_callbacks_release_the_gate_and_keep_roots_during_native_reentry() {
        callback_reentry(true);
    }
    fn callback_reentry(shared: bool) {
        ril_rt_init();
        if shared {
            with_runtime(crate::shared::activate);
        }
        ril_rt_enter();
        let input = ril_rt_sequence(0);
        for value in 0..1200 {
            let value = ril_rt_int(value, 0, 64, 1);
            ril_rt_push(input, value);
        }
        let environment = ril_rt_unit();
        let callback = ril_rt_callable(double as *const () as usize as u64, environment);
        let arguments = ril_rt_sequence(1);
        ril_rt_push(arguments, input);
        ril_rt_push(arguments, callback);
        let name = handle(|runtime| runtime.string("Array::map".into()));
        let mapped = ril_rt_builtin(name, arguments);
        assert_ne!(mapped, 0);
        assert_eq!(ril_rt_status(), 0);
        assert_eq!(ril_rt_len(mapped), 1200);
        with_runtime(|runtime| {
            let mapped = runtime.sequence(Handle(mapped)).unwrap();
            assert_eq!(runtime.as_integer(mapped[1199]).unwrap(), 2398);
        });
        ril_rt_leave(mapped);
    }
    extern "C" fn cleanup(environment: u64, _arguments: u64) -> u64 {
        ril_rt_enter();
        ril_rt_root(0, environment);
        let result = handle(|runtime| {
            let fields = runtime.sequence(Handle(environment))?;
            runtime.append(fields[0], fields[1])?;
            if runtime.truth(fields[2])? {
                return Err(RuntimeError::panic(
                    runtime.as_integer(fields[1])?.to_string(),
                ));
            }
            runtime.unit()
        });
        ril_rt_leave(result)
    }
    fn resource(events: u64, index: i128, panics: bool) -> u64 {
        handle(|runtime| {
            let index = runtime.int(index)?;
            let fault = runtime.boolean(panics)?;
            let environment =
                runtime.allocate(Object::Tuple(vec![Handle(events), index, fault]))?;
            let action = runtime.allocate(Object::Closure {
                function: cleanup as *const () as usize as u64,
                environment,
            })?;
            runtime.allocate(Object::Record([("on_close".into(), action)].into()))
        })
    }
    fn event_values(events: u64) -> Vec<i128> {
        with_runtime(|runtime| {
            runtime
                .sequence(Handle(events))
                .unwrap()
                .iter()
                .map(|&event| runtime.as_integer(event).unwrap())
                .collect()
        })
    }
    #[test]
    fn cleanup_runs_current_actions_in_reverse_order_and_preserves_return_roots() {
        ril_rt_init();
        ril_rt_enter();
        let events = ril_rt_sequence(0);
        ril_rt_root(0, events);
        let marker = ril_rt_scope_enter();
        let first = resource(events, 1, false);
        let second = resource(events, 2, false);
        ril_rt_scope_register(first);
        ril_rt_scope_register(second);
        let replacement = resource(events, 3, false);
        handle(|runtime| {
            let current = runtime.field(Handle(replacement), "on_close")?;
            runtime.set_field(Handle(second), "on_close".into(), current)
        });
        ril_rt_statement_end();
        with_runtime(|runtime| runtime.collect().unwrap());
        let value = ril_rt_int(42, 0, 64, 1);
        assert_eq!(ril_rt_scope_leave(marker, value), value);
        assert_eq!(event_values(events), [3, 1]);
        assert_eq!(ril_rt_status(), 0);
        assert_eq!(ril_rt_scope_leave(marker, value), value);
        assert_eq!(event_values(events), [3, 1]);
        ril_rt_leave(value);
    }
    #[test]
    fn cleanup_panic_starts_unwinding_and_second_fault_abandons_remaining_actions() {
        ril_rt_init();
        ril_rt_enter();
        let events = ril_rt_sequence(0);
        ril_rt_root(0, events);
        for (index, panics) in [(1, false), (2, true), (3, true)] {
            let resource = resource(events, index, panics);
            ril_rt_scope_register(resource);
        }
        let value = ril_rt_unit();
        assert_eq!(ril_rt_scope_leave(0, value), 0);
        assert_eq!(event_values(events), [3, 2]);
        with_runtime(|runtime| {
            let error = runtime.fault.as_ref().unwrap();
            assert_eq!(error.tag, OutcomeTag::DoubleFault);
            assert_eq!(error.primary.as_ref().unwrap().message, "3");
            assert_eq!(error.cleanup.as_ref().unwrap().message, "2");
        });
        ril_rt_leave(0);
        assert_eq!(event_values(events), [3, 2]);
    }
    #[test]
    fn variant_callbacks_are_lazy_and_unvisited_payloads_keep_their_handles() {
        ril_rt_init();
        ril_rt_enter();
        let callback = handle(|runtime| {
            let environment = runtime.unit()?;
            runtime.allocate(Object::Closure {
                function: double as *const () as usize as u64,
                environment,
            })
        });
        let number = ril_rt_int(21, 0, 64, 1);
        let some = handle(|runtime| runtime.variant("Some", vec![Handle(number)]));
        let arguments = ril_rt_sequence(1);
        ril_rt_push(arguments, some);
        ril_rt_push(arguments, callback);
        let name = handle(|runtime| runtime.string("Options::map".into()));
        let result = ril_rt_builtin(name, arguments);
        with_runtime(|runtime| {
            let Object::Variant { tag, fields } = runtime.heap.get(Handle(result)).unwrap() else {
                panic!("option")
            };
            assert_eq!(tag, "Some");
            assert_eq!(runtime.as_integer(fields[0]).unwrap(), 42);
        });
        let message = handle(|runtime| runtime.string("business failure".into()));
        let error = handle(|runtime| runtime.variant("Err", vec![Handle(message)]));
        let arguments = ril_rt_sequence(1);
        ril_rt_push(arguments, error);
        ril_rt_push(arguments, callback);
        let name = handle(|runtime| runtime.string("Results::map".into()));
        assert_eq!(ril_rt_builtin(name, arguments), error);
        assert_eq!(ril_rt_status(), 0);
        let arguments = ril_rt_sequence(1);
        ril_rt_push(arguments, some);
        let panic = handle(|runtime| runtime.allocate(Object::Builtin("panic".into())));
        ril_rt_push(arguments, panic);
        let name = handle(|runtime| runtime.string("Options::unwrap_or_else".into()));
        assert_eq!(ril_rt_builtin(name, arguments), number);
        assert_eq!(ril_rt_status(), 0);
        ril_rt_leave(result);
    }
}
