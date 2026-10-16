use super::*;

fn call(name: &str, arguments: Vec<Handle>) -> Result<Handle> {
    let initial = handle(|runtime| {
        let callable = runtime.allocate(Object::Builtin(name.into()))?;
        let arguments = runtime.allocate(Object::Tuple(arguments))?;
        let continuation = runtime.allocate(Object::CpsContinuation {
            state: Continuation::End,
            used: false,
        })?;
        runtime.allocate(Object::CpsStep(Step::Call {
            callable,
            arguments,
            continuation,
            handlers: Handle::INVALID,
            callback_entry: false,
        }))
    });
    let value = ril_rt_cps_run(initial);
    with_runtime(|runtime| match runtime.fault.take() {
        Some(error) => Err(error),
        None => Ok(Handle(value)),
    })
}

fn fixture(runtime: &mut Runtime, function: u64, field: &str) -> (Handle, Handle) {
    let calls = runtime.int(0).unwrap();
    let bad = runtime.boolean(true).unwrap();
    let receiver = runtime
        .allocate(Object::Record(
            [("calls".into(), calls), ("bad".into(), bad)].into(),
        ))
        .unwrap();
    let environment = runtime.unit().unwrap();
    let callback = runtime
        .allocate(Object::Closure {
            function,
            environment,
        })
        .unwrap();
    let operations = runtime
        .allocate(Object::Record([(field.into(), callback)].into()))
        .unwrap();
    (receiver, operations)
}
fn count_call(runtime: &mut Runtime, receiver: Handle) -> Result<()> {
    let count = runtime.field(receiver, "calls")?;
    let count = runtime.int(runtime.as_integer(count)? + 1)?;
    runtime.set_field(receiver, "calls".into(), count)?;
    Ok(())
}
extern "C" fn invalid_read(_: u64, arguments: u64) -> u64 {
    handle(|runtime| {
        let receiver = runtime.sequence(Handle(arguments))?[0];
        count_call(runtime, receiver)?;
        let chunk = runtime.read_chunk_value(b"abc".to_vec(), false)?;
        runtime.variant("Ok", vec![chunk])
    })
}

#[test]
fn invalid_read_response_does_not_populate_cache_or_keep_an_invocation_permit() {
    ril_rt_init();
    let (buffer, receiver, operations, maximum) = with_runtime(|runtime| {
        let buffer = runtime
            .allocate(Object::ReadBuffer(crate::io_buffered::ReadBuffer::new(2)))
            .unwrap();
        let (receiver, operations) =
            fixture(runtime, invalid_read as *const () as usize as u64, "read");
        (buffer, receiver, operations, runtime.int(1).unwrap())
    });
    let error = call(
        "Io::read_buffered",
        vec![buffer, receiver, operations, maximum],
    )
    .unwrap_err();
    assert_eq!(error.message, "read exceeds requested count");
    with_runtime(|runtime| {
        let Object::ReadBuffer(buffer) = runtime.heap.get(buffer).unwrap() else {
            panic!("buffer state")
        };
        assert!(buffer.pending.is_empty());
        assert!(buffer.binding.is_none());
        assert!(runtime.read_permits.is_empty());
        let calls = runtime.field(receiver, "calls").unwrap();
        assert_eq!(runtime.as_integer(calls).unwrap(), 1);
    });
    ril_rt_init();
}

extern "C" fn switchable_write(_: u64, arguments: u64) -> u64 {
    handle(|runtime| {
        let args = runtime.sequence(Handle(arguments))?;
        count_call(runtime, args[0])?;
        let bad = runtime.field(args[0], "bad")?;
        let count = runtime.as_bytes(args[1])?.len() + usize::from(runtime.truth(bad)?);
        runtime.write_progress(count, None)
    })
}

#[test]
fn invalid_write_progress_preserves_the_entire_unconfirmed_suffix_without_retry() {
    ril_rt_init();
    let (buffer, receiver, operations, data) = with_runtime(|runtime| {
        let buffer = runtime
            .allocate(Object::WriteBuffer(crate::io_buffered::WriteBuffer::new(4)))
            .unwrap();
        let (receiver, operations) = fixture(
            runtime,
            switchable_write as *const () as usize as u64,
            "write",
        );
        let data = runtime
            .allocate(Object::Bytes(b"abcd".to_vec().into()))
            .unwrap();
        (buffer, receiver, operations, data)
    });
    call(
        "Io::write_buffered",
        vec![buffer, receiver, operations, data],
    )
    .unwrap();
    let error = call("Io::flush", vec![buffer, receiver, operations]).unwrap_err();
    assert_eq!(error.message, "excess progress");
    with_runtime(|runtime| {
        let Object::WriteBuffer(state) = runtime.heap.get_mut(buffer).unwrap() else {
            panic!("buffer state")
        };
        assert_eq!(state.pending.snapshot().unwrap().as_slice(), b"abcd");
        let count = runtime.field(receiver, "calls").unwrap();
        assert_eq!(runtime.as_integer(count).unwrap(), 1);
        let valid = runtime.boolean(false).unwrap();
        runtime.set_field(receiver, "bad".into(), valid).unwrap();
    });
    call("Io::flush", vec![buffer, receiver, operations]).unwrap();
    with_runtime(|runtime| {
        let Object::WriteBuffer(state) = runtime.heap.get(buffer).unwrap() else {
            panic!("buffer state")
        };
        assert!(state.pending.is_empty());
        assert!(state.binding.is_none());
    });
    ril_rt_init();
}
