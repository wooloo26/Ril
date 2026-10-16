use super::*;

extern "C" fn request(_environment: u64, arguments: u64) -> u64 {
    ril_rt_enter();
    ril_rt_root(0, arguments);
    let continuation = with_runtime(|runtime| {
        runtime
            .sequence(Handle(arguments))
            .unwrap()
            .last()
            .unwrap()
            .0
    });
    let arguments = ril_rt_sequence(1);
    let step = ril_rt_cps_perform(7, arguments, continuation);
    ril_rt_leave(step)
}
extern "C" fn read_capture(environment: u64, arguments: u64) -> u64 {
    ril_rt_enter();
    ril_rt_root(0, environment);
    ril_rt_root(1, arguments);
    let (value, resumption) = with_runtime(|runtime| {
        let value = runtime.field(Handle(environment), "capture").unwrap();
        let arguments = runtime.sequence(Handle(arguments)).unwrap();
        (value.0, arguments[0].0)
    });
    let step = ril_rt_cps_resume(resumption, value);
    ril_rt_leave(step)
}
fn install(runtime: &mut Runtime, value: i128, definition: u64) -> Result<(Handle, Handle)> {
    let old_activation = runtime.new_activation()?;
    let old_continuation = runtime.allocate(Object::CpsContinuation {
        state: Continuation::End,
        used: false,
    })?;
    let value = runtime.int(value)?;
    let environment = runtime.allocate(Object::Record(
        [
            ("capture".into(), value),
            ("\0ril.cps.activation".into(), old_activation),
            ("\0ril.cps.continuation".into(), old_continuation),
            ("\0ril.cps.function-return".into(), old_continuation),
        ]
        .into(),
    ))?;
    let arm = runtime.allocate(Object::CpsClosure {
        function: read_capture as *const () as usize as u64,
        environment,
    })?;
    let table = runtime.allocate(Object::CpsHandlers([(7, arm)].into()))?;
    runtime.cps_handlers = runtime.allocate(Object::CpsHandlerFrame(HandlerFrame {
        definition,
        table,
        parent: runtime.cps_handlers,
        delimiter: old_continuation,
    }))?;
    Ok((old_activation, old_continuation))
}

#[test]
fn escaped_recipe_collects_old_control_state_and_rebuilds_each_invocation() {
    ril_rt_init();
    ril_rt_enter();
    let (old_activation, old_continuation) =
        with_runtime(|runtime| install(runtime, 42, 123).unwrap());
    let definitions = handle(|runtime| {
        let definition = runtime.int(123)?;
        runtime.allocate(Object::Tuple(vec![definition]))
    });
    let empty = ril_rt_unit();
    let action = ril_rt_cps_callable(request as *const () as usize as u64, empty);
    let retained = ril_rt_cps_retain(action, definitions);
    assert_ne!(retained, 0);
    with_runtime(|runtime| {
        runtime.cps_handlers = Handle::INVALID;
        runtime.cps_activation = Handle::INVALID;
    });
    ril_rt_leave(retained);
    with_runtime(|runtime| {
        runtime.collect().unwrap();
        assert!(runtime.heap.get(old_activation).is_err());
        assert!(runtime.heap.get(old_continuation).is_err());
        assert_eq!(
            runtime.heap.deep_clone(Handle(retained)),
            Err(crate::heap::HeapError::NonClonable)
        );
    });
    for _ in 0..3 {
        ril_rt_enter();
        // A later caller with the same operation must not replace the captured
        // handler, nor cause the second invocation to reuse an affine delimiter.
        with_runtime(|runtime| {
            install(runtime, 99, 999).unwrap();
        });
        let end = ril_rt_cps_end();
        let arguments = ril_rt_sequence(1);
        let step = ril_rt_cps_call(retained, arguments, end);
        let answer = ril_rt_cps_run(step);
        assert_eq!(ril_rt_status(), 0);
        with_runtime(|runtime| {
            assert_eq!(runtime.as_integer(Handle(answer)).unwrap(), 42);
            assert!(runtime.cps_delimiters.is_empty());
            runtime.cps_handlers = Handle::INVALID;
            runtime.cps_activation = Handle::INVALID;
        });
        ril_rt_leave(0);
        with_runtime(|runtime| {
            runtime.collect().unwrap();
        });
    }
}

#[test]
fn missing_selected_handler_fails_closed() {
    ril_rt_init();
    ril_rt_enter();
    let empty = ril_rt_unit();
    let action = ril_rt_cps_callable(request as *const () as usize as u64, empty);
    let definitions = handle(|runtime| {
        let definition = runtime.int(123)?;
        runtime.allocate(Object::Tuple(vec![definition]))
    });
    assert_eq!(ril_rt_cps_retain(action, definitions), 0);
    with_runtime(|runtime| {
        assert_eq!(
            runtime.fault.as_ref().unwrap().tag,
            OutcomeTag::InternalFault
        )
    });
    ril_rt_leave(0);
}
