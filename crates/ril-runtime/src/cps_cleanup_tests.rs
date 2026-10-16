use super::*;

fn arguments(value: u64) -> Vec<Handle> {
    with_runtime(|runtime| runtime.sequence(Handle(value)).unwrap())
}
extern "C" fn cleanup(environment: u64, _arguments: u64) -> u64 {
    ril_rt_enter();
    ril_rt_root(0, environment);
    let value = handle(|runtime| {
        let fields = runtime.sequence(Handle(environment))?;
        runtime.append(fields[0], fields[1])?;
        if runtime.truth(fields[2])? {
            return Err(RuntimeError::panic("cleanup failed"));
        }
        runtime.unit()
    });
    ril_rt_leave(value)
}
fn register(activation: u64, events: u64, index: i128, panics: bool) {
    let resource = handle(|runtime| {
        let index = runtime.int(index)?;
        let panics = runtime.boolean(panics)?;
        let environment = runtime.allocate(Object::Tuple(vec![Handle(events), index, panics]))?;
        let callback = runtime.allocate(Object::Closure {
            function: cleanup as *const () as usize as u64,
            environment,
        })?;
        runtime.allocate(Object::Record([("on_close".into(), callback)].into()))
    });
    ril_rt_cps_scope_register(activation, resource);
}
extern "C" fn after_body(environment: u64, arguments_handle: u64) -> u64 {
    ril_rt_enter();
    ril_rt_root(0, environment);
    ril_rt_root(1, arguments_handle);
    let fields = arguments(environment);
    let activation = fields[0].0;
    let outer = if with_runtime(|runtime| runtime.as_integer(fields[3]).unwrap()) == 6 {
        fields[4].0
    } else {
        fields[1].0
    };
    ril_rt_cps_activation_attach(activation);
    with_runtime(|runtime| runtime.collect().unwrap());
    let mode = with_runtime(|runtime| runtime.as_integer(fields[3]).unwrap());
    let value = if mode == 2 {
        handle(|_| Err(RuntimeError::panic("body failed")))
    } else {
        handle(|runtime| {
            let event = runtime.int(4)?;
            runtime.append(fields[2], event)?;
            runtime.int(7)
        })
    };
    if mode == 2 {
        return ril_rt_leave(0);
    }
    let step = ril_rt_cps_activation_return(activation, outer, value);
    ril_rt_leave(step)
}
extern "C" fn body(environment: u64, arguments_handle: u64) -> u64 {
    ril_rt_enter();
    ril_rt_root(0, environment);
    ril_rt_root(1, arguments_handle);
    let fields = arguments(environment);
    let activation = ril_rt_cps_activation_new();
    with_runtime(|runtime| {
        runtime
            .globals
            .insert("cleanup_fixture_body".into(), Handle(activation));
    });
    let outer = arguments(arguments_handle).last().unwrap().0;
    register(activation, fields[0].0, 1, false);
    let mode = with_runtime(|runtime| runtime.as_integer(fields[1]).unwrap());
    register(activation, fields[0].0, 2, mode == 3);
    let saved = handle(|runtime| {
        runtime.allocate(Object::Tuple(vec![
            Handle(activation),
            Handle(outer),
            fields[0],
            fields[1],
            fields[2],
        ]))
    });
    let continuation = ril_rt_cps_continuation(after_body as *const () as usize as u64, saved);
    let args = ril_rt_sequence(1);
    let step = ril_rt_cps_perform(77, args, continuation);
    ril_rt_leave(step)
}
extern "C" fn arm(environment: u64, arguments_handle: u64) -> u64 {
    ril_rt_enter();
    ril_rt_root(0, environment);
    ril_rt_root(1, arguments_handle);
    let fields = arguments(environment);
    let values = arguments(arguments_handle);
    let activation = ril_rt_cps_activation_new();
    register(activation, fields[0].0, 3, false);
    let mode = with_runtime(|runtime| runtime.as_integer(fields[1]).unwrap());
    let answer = ril_rt_int(9, 0, 64, 1);
    let step = if mode == 0 || mode == 3 || mode == 5 {
        ril_rt_cps_activation_return(
            activation,
            if mode == 5 {
                fields[2].0
            } else {
                values.last().unwrap().0
            },
            answer,
        )
    } else if mode == 4 {
        let environment = handle(|runtime| {
            runtime.allocate(Object::Tuple(vec![
                Handle(activation),
                *values.last().unwrap(),
                fields[0],
            ]))
        });
        let next = ril_rt_cps_continuation(after_arm as *const () as usize as u64, environment);
        ril_rt_cps_resume_then(values[0].0, answer, next)
    } else {
        ril_rt_cps_resume(values[0].0, answer)
    };
    ril_rt_leave(step)
}
extern "C" fn after_arm(environment: u64, arguments_handle: u64) -> u64 {
    ril_rt_enter();
    ril_rt_root(0, environment);
    ril_rt_root(1, arguments_handle);
    let fields = arguments(environment);
    let answer = handle(|runtime| {
        let event = runtime.int(5)?;
        runtime.append(fields[2], event)?;
        runtime.int(99)
    });
    let step = ril_rt_cps_activation_return(fields[0].0, fields[1].0, answer);
    ril_rt_leave(step)
}
fn run_case(mode: i128) -> (u64, Vec<i128>, Option<RuntimeError>) {
    run_case_shared(mode, false)
}
fn run_case_shared(mode: i128, shared: bool) -> (u64, Vec<i128>, Option<RuntimeError>) {
    ril_rt_init();
    if shared {
        with_runtime(crate::shared::activate);
    }
    ril_rt_enter();
    let events = ril_rt_sequence(0);
    ril_rt_root(0, events);
    let end = ril_rt_cps_end();
    let environment = handle(|runtime| {
        let mode = runtime.int(mode)?;
        runtime.allocate(Object::Tuple(vec![Handle(events), mode, Handle(end)]))
    });
    let body = ril_rt_cps_callable(body as *const () as usize as u64, environment);
    let arm = ril_rt_cps_callable(arm as *const () as usize as u64, environment);
    let table = ril_rt_cps_handlers();
    ril_rt_cps_handler_add(table, 77, arm);
    let step = ril_rt_cps_handle(body, table, end, 0);
    let result = ril_rt_cps_run(step);
    let (events, fault) = with_runtime(|runtime| {
        (
            runtime
                .sequence(Handle(events))
                .unwrap()
                .iter()
                .map(|value| runtime.as_integer(*value).unwrap())
                .collect(),
            runtime.fault.clone(),
        )
    });
    ril_rt_leave(result);
    (result, events, fault)
}
#[test]
fn abort_closes_arm_then_suspended_body_and_preserves_committed_writes() {
    let (result, events, fault) = run_case(0);
    assert_ne!(result, 0);
    assert!(fault.is_none(), "{fault:?}");
    assert_eq!(events, [3, 2, 1]);
}
#[test]
fn tail_resume_keeps_arm_resources_alive_until_the_body_finishes_even_through_gc() {
    let (result, events, fault) = run_case(1);
    assert_ne!(result, 0);
    assert!(fault.is_none(), "{fault:?}");
    assert_eq!(events, [4, 2, 1, 3]);
}
#[test]
fn panic_in_resumed_body_unwinds_body_before_the_suspended_arm() {
    let (result, events, fault) = run_case(2);
    assert_eq!(result, 0);
    assert_eq!(fault.unwrap().tag, OutcomeTag::LanguagePanic);
    assert_eq!(events, [2, 1, 3]);
}
#[test]
fn cleanup_failure_during_abort_records_both_causes_and_stops_the_remaining_actions() {
    let (result, events, fault) = run_case(3);
    assert_eq!(result, 0);
    let fault = fault.unwrap();
    assert_eq!(fault.tag, OutcomeTag::DoubleFault);
    assert_eq!(fault.primary.unwrap().tag, OutcomeTag::EffectAborted);
    assert_eq!(fault.cleanup.unwrap().tag, OutcomeTag::LanguagePanic);
    assert_eq!(events, [3, 2]);
}
#[test]
fn shared_heap_double_fault_abandons_the_remaining_logical_cleanup_stack() {
    let (result, events, fault) = run_case_shared(3, true);
    assert_eq!(result, 0);
    assert_eq!(fault.unwrap().tag, OutcomeTag::DoubleFault);
    assert_eq!(events, [3, 2]);
    with_runtime(|runtime| {
        let body = runtime.globals["cleanup_fixture_body"];
        let activation = runtime.activation(body).unwrap();
        assert!(activation.closed);
        assert!(
            activation.cleanups.is_empty(),
            "abandoned actions must not survive in the logical stack"
        );
    });
}
#[test]
fn an_explicit_resume_answer_reenters_the_live_arm_activation_before_its_cleanup() {
    let (result, events, fault) = run_case(4);
    assert_ne!(result, 0);
    assert!(fault.is_none(), "{fault:?}");
    assert_eq!(events, [4, 2, 1, 5, 3]);
}

#[test]
fn a_native_return_past_the_delimiter_still_closes_the_suspended_arm() {
    let (result, events, fault) = run_case(6);
    assert_ne!(result, 0);
    assert!(fault.is_none(), "{fault:?}");
    assert_eq!(events, [4, 2, 1, 3]);
}
#[test]
fn a_native_abort_return_past_the_delimiter_closes_the_abandoned_body() {
    let (result, events, fault) = run_case(5);
    assert_ne!(result, 0);
    assert!(fault.is_none(), "{fault:?}");
    assert_eq!(events, [3, 2, 1]);
}
