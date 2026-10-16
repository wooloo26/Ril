//! Low-level control regressions complement native source tests in
//! `ril-cli/tests/cleanup_handler_extents.rs` with internal exit-state checks.
use super::*;

fn values(value: u64) -> Vec<Handle> {
    with_runtime(|runtime| runtime.sequence(Handle(value)).unwrap())
}
extern "C" fn log_cleanup(environment: u64, _arguments: u64) -> u64 {
    ril_rt_enter();
    ril_rt_root(0, environment);
    let fields = values(environment);
    let result = handle(|runtime| {
        runtime.append(fields[0], fields[1])?;
        if runtime.as_integer(fields[1])? == 0 {
            return Err(RuntimeError::panic("body cleanup"));
        }
        runtime.unit()
    });
    ril_rt_leave(result)
}
fn register_log(activation: u64, events: Handle, index: i128) {
    let resource = handle(|runtime| {
        let index = runtime.int(index)?;
        let environment = runtime.allocate(Object::Tuple(vec![events, index]))?;
        let action = runtime.allocate(Object::Closure {
            function: log_cleanup as *const () as usize as u64,
            environment,
        })?;
        runtime.allocate(Object::Record([("on_close".into(), action)].into()))
    });
    ril_rt_cps_scope_register(activation, resource);
}
extern "C" fn abandoned(_environment: u64, _arguments: u64) -> u64 {
    handle(|_| Err(RuntimeError::internal("an abandoned continuation resumed")))
}
extern "C" fn after_cleanup_operation(environment: u64, arguments: u64) -> u64 {
    ril_rt_enter();
    ril_rt_root(0, environment);
    ril_rt_root(1, arguments);
    let saved = values(environment);
    ril_rt_cps_activation_attach(saved[0].0);
    let unit = ril_rt_unit();
    let step = ril_rt_cps_activation_return(saved[0].0, saved[1].0, unit);
    ril_rt_leave(step)
}
extern "C" fn cleanup_operation(environment: u64, arguments: u64) -> u64 {
    ril_rt_enter();
    ril_rt_root(0, environment);
    ril_rt_root(1, arguments);
    let activation = ril_rt_cps_activation_new();
    let fields = values(environment);
    handle(|runtime| {
        assert!(runtime.cancellation_mask > 0);
        let event = runtime.int(2)?;
        runtime.append(fields[0], event)?;
        runtime.collect()?;
        runtime.unit()
    });
    let continuation = if with_runtime(|runtime| runtime.as_integer(fields[1]).unwrap()) == 5 {
        let outer = values(arguments).last().unwrap().0;
        let saved = handle(|runtime| {
            runtime.allocate(Object::Tuple(vec![Handle(activation), Handle(outer)]))
        });
        ril_rt_cps_continuation(after_cleanup_operation as *const () as usize as u64, saved)
    } else {
        ril_rt_cps_continuation(abandoned as *const () as usize as u64, environment)
    };
    let args = ril_rt_sequence(1);
    let step = ril_rt_cps_perform(77, args, continuation);
    ril_rt_leave(step)
}
extern "C" fn after_first(environment: u64, arguments: u64) -> u64 {
    ril_rt_enter();
    ril_rt_root(0, environment);
    ril_rt_root(1, arguments);
    let saved = values(environment);
    let original = values(saved[2].0);
    ril_rt_cps_activation_attach(saved[0].0);
    let mode = with_runtime(|runtime| runtime.as_integer(original[1]).unwrap());
    let unit = ril_rt_unit();
    let step = match mode {
        0 => {
            let next = ril_rt_cps_continuation(abandoned as *const () as usize as u64, environment);
            let args = ril_rt_sequence(1);
            ril_rt_cps_perform(77, args, next)
        }
        1 | 3 | 5 => ril_rt_cps_activation_return(saved[0].0, saved[1].0, unit),
        // A native boundary may return to the delimiter while the resumed
        // activation still needs closing. Its cleanup fails after redirect.
        2 => ril_rt_cps_return(saved[1].0, unit),
        4 => handle(|_| Err(RuntimeError::panic("original body panic"))),
        _ => unreachable!(),
    };
    ril_rt_leave(step)
}
extern "C" fn body(environment: u64, arguments: u64) -> u64 {
    ril_rt_enter();
    ril_rt_root(0, environment);
    ril_rt_root(1, arguments);
    let original = values(environment);
    let outer = values(arguments).last().unwrap().0;
    let activation = ril_rt_cps_activation_new();
    let mode = with_runtime(|runtime| runtime.as_integer(original[1]).unwrap());
    register_log(
        activation,
        original[0],
        if matches!(mode, 3..=5) { 3 } else { 0 },
    );
    if matches!(mode, 1 | 3 | 4 | 5) {
        let resource = handle(|runtime| {
            let action = runtime.allocate(Object::CpsClosure {
                function: cleanup_operation as *const () as usize as u64,
                environment: Handle(environment),
            })?;
            runtime.allocate(Object::Record([("on_close".into(), action)].into()))
        });
        ril_rt_cps_scope_register(activation, resource);
    }
    let saved = handle(|runtime| {
        runtime.allocate(Object::Tuple(vec![
            Handle(activation),
            Handle(outer),
            Handle(environment),
        ]))
    });
    let next = ril_rt_cps_continuation(after_first as *const () as usize as u64, saved);
    let args = ril_rt_sequence(1);
    let step = ril_rt_cps_perform(77, args, next);
    ril_rt_leave(step)
}
extern "C" fn arm(environment: u64, arguments: u64) -> u64 {
    ril_rt_enter();
    ril_rt_root(0, environment);
    ril_rt_root(1, arguments);
    let original = values(environment);
    let args = values(arguments);
    let activation = ril_rt_cps_activation_new();
    let count = ril_rt_cell_get(original[2].0);
    let count = with_runtime(|runtime| runtime.as_integer(Handle(count)).unwrap());
    let incremented = handle(|runtime| runtime.int(count + 1));
    ril_rt_cell_set(original[2].0, incremented);
    let unit = ril_rt_unit();
    let step = if count == 0 {
        register_log(activation, original[0], 1);
        ril_rt_cps_resume(args[0].0, unit)
    } else if with_runtime(|runtime| runtime.as_integer(original[1]).unwrap()) == 5 {
        register_log(activation, original[0], 4);
        ril_rt_cps_resume(args[0].0, unit)
    } else {
        ril_rt_cps_activation_return(activation, args.last().unwrap().0, unit)
    };
    ril_rt_leave(step)
}
fn run(mode: i128) -> (u64, Vec<i128>, Option<RuntimeError>) {
    ril_rt_init();
    with_runtime(crate::shared::activate);
    ril_rt_enter();
    let events = ril_rt_sequence(0);
    ril_rt_root(0, events);
    let environment = handle(|runtime| {
        let mode = runtime.int(mode)?;
        let zero = runtime.int(0)?;
        let counter = runtime.allocate(Object::Cell(zero))?;
        runtime.allocate(Object::Tuple(vec![Handle(events), mode, counter]))
    });
    let body = ril_rt_cps_callable(body as *const () as usize as u64, environment);
    let arm = ril_rt_cps_callable(arm as *const () as usize as u64, environment);
    let table = ril_rt_cps_handlers();
    ril_rt_cps_handler_add(table, 77, arm);
    let end = ril_rt_cps_end();
    let step = ril_rt_cps_handle(body, table, end, 1);
    let result = ril_rt_cps_run(step);
    let outcome = with_runtime(|runtime| {
        assert!(
            runtime.cps_exits.is_empty(),
            "stale exit request after discarded cleanup"
        );
        assert_eq!(runtime.cancellation_mask, 0, "cleanup mask leaked");
        assert_eq!(runtime.budgets.depth(), 0, "cleanup allowance leaked");
        assert_eq!(runtime.cps_activation, Handle::INVALID);
        assert!(runtime.cps_delimiters.is_empty());
        assert!(runtime.cps_resume_returns.is_empty());
        (
            result,
            runtime
                .sequence(Handle(events))
                .unwrap()
                .iter()
                .map(|&value| runtime.as_integer(value).unwrap())
                .collect(),
            runtime.fault.clone(),
        )
    });
    ril_rt_leave(result);
    outcome
}

#[test]
fn a_later_abort_cleans_the_resumed_body_as_abandoned() {
    let (result, events, fault) = run(0);
    assert_eq!(result, 0);
    let fault = fault.unwrap();
    assert_eq!(fault.tag, OutcomeTag::DoubleFault);
    assert_eq!(fault.primary.unwrap().tag, OutcomeTag::EffectAborted);
    assert_eq!(fault.cleanup.unwrap().message, "body cleanup");
    assert_eq!(events, [0]);
}
#[test]
fn failure_while_redirecting_an_answer_still_closes_the_saved_arm() {
    let (result, events, fault) = run(2);
    assert_eq!(result, 0);
    let fault = fault.unwrap();
    assert_eq!(fault.tag, OutcomeTag::LanguagePanic);
    assert_eq!(fault.message, "body cleanup");
    assert_eq!(events, [0, 1]);
}
#[test]
fn an_abort_requested_by_cleanup_does_not_leak_exit_frames_or_masks() {
    let (result, events, fault) = run(1);
    assert_eq!(result, 0);
    let fault = fault.unwrap();
    assert_eq!(fault.tag, OutcomeTag::DoubleFault);
    assert_eq!(fault.primary.unwrap().tag, OutcomeTag::EffectAborted);
    assert_eq!(fault.cleanup.unwrap().message, "body cleanup");
    assert_eq!(events, [2, 0]);
}

#[test]
fn a_successful_cleanup_abort_retires_the_superseded_exit_before_the_arm_answer() {
    let (result, events, fault) = run(3);
    assert_ne!(result, 0, "{fault:?}");
    assert!(fault.is_none(), "{fault:?}");
    assert_eq!(events, [2, 3, 1]);
}

#[test]
fn cleanup_abort_does_not_replace_an_older_body_panic_with_a_normal_answer() {
    let (result, events, fault) = run(4);
    assert_eq!(result, 0);
    let fault = fault.unwrap();
    assert_eq!(fault.tag, OutcomeTag::LanguagePanic);
    assert_eq!(fault.message, "original body panic");
    assert_eq!(events, [2, 3, 1]);
}

#[test]
fn cleanup_keeps_a_caller_handlers_new_arm_alive_until_the_resumed_body_finishes() {
    let (result, events, fault) = run(5);
    assert_ne!(result, 0, "{fault:?}");
    assert!(fault.is_none(), "{fault:?}");
    assert_eq!(events, [2, 3, 4, 1]);
}
