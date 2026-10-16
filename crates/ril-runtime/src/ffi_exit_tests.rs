use super::*;
use std::cell::Cell;

thread_local! { static NATIVE_DEPTH: Cell<(usize,usize)> = const { Cell::new((0,0)) }; }
struct NativeEntry;
impl NativeEntry {
    fn enter() -> Self {
        NATIVE_DEPTH.with(|depth| {
            let (now, peak) = depth.get();
            depth.set((now + 1, peak.max(now + 1)));
        });
        Self
    }
}
impl Drop for NativeEntry {
    fn drop(&mut self) {
        NATIVE_DEPTH.with(|depth| {
            let (now, peak) = depth.get();
            depth.set((now - 1, peak));
        });
    }
}

fn values(handle: u64) -> Vec<Handle> {
    with_runtime(|runtime| runtime.sequence(Handle(handle)).unwrap())
}
fn install_fixture(runtime: &mut Runtime, activation: Handle, environment: Handle) -> Result<()> {
    let callable = runtime.allocate(Object::CpsClosure {
        function: cleanup as *const () as usize as u64,
        environment,
    })?;
    let resource = runtime.allocate(Object::Record([("on_close".into(), callable)].into()))?;
    runtime.register_activation_cleanup(activation, resource)?;
    Ok(())
}
extern "C" fn cleanup(environment: u64, arguments: u64) -> u64 {
    let _depth = NativeEntry::enter();
    ril_rt_enter();
    ril_rt_root(0, environment);
    ril_rt_root(1, arguments);
    let fields = values(environment);
    let continuation = values(arguments).last().unwrap().0;
    let activation = ril_rt_cps_activation_new();
    let setup = handle(|runtime| {
        assert!(runtime.cancellation_mask > 0);
        if runtime.truth(fields[3])? {
            runtime.cancellation.request();
            assert!(!runtime.host_cancellation().requested());
        }
        assert!(
            !runtime.budgets.is_active(),
            "outer allowance must remain suspended across native steps"
        );
        let depth = runtime.as_integer(fields[1])?;
        let event = runtime.int(depth)?;
        runtime.append(fields[0], event)?;
        // A budget created inside cleanup is independent of the paused owner.
        let boundary = runtime.unit()?;
        let budget = runtime.budgets.begin(1, boundary)?;
        assert_eq!(
            runtime
                .budgets
                .charge(ril_runtime_api::abi::BudgetEvent::FunctionEntry),
            crate::budget::Decision::Execute
        );
        // A failing callback abandons this local owner during its own unwind.
        if !runtime.truth(fields[2])? {
            runtime.budgets.finish(budget)?;
        }
        if depth > 0 {
            let child = runtime.int(depth - 1)?;
            let environment =
                runtime.allocate(Object::Tuple(vec![fields[0], child, fields[2], fields[3]]))?;
            install_fixture(runtime, Handle(activation), environment)?;
        }
        if depth % 128 == 0 {
            runtime.collect()?;
        }
        if runtime.truth(fields[2])? {
            return Err(RuntimeError::panic("cleanup"));
        }
        runtime.unit()
    });
    let next = if setup == 0 {
        0
    } else {
        ril_rt_cps_activation_return(activation, continuation, setup)
    };
    ril_rt_leave(next)
}
extern "C" fn body(environment: u64, arguments: u64) -> u64 {
    ril_rt_enter();
    ril_rt_root(0, environment);
    ril_rt_root(1, arguments);
    let fields = values(environment);
    let continuation = values(arguments).last().unwrap().0;
    let activation = ril_rt_cps_activation_new();
    let value = handle(|runtime| {
        // This older registration must run after the newest cleanup unless the
        // latter fatally fails while an earlier outcome is already unwinding.
        let index = runtime.int(99)?;
        let false_value = runtime.boolean(false)?;
        let older = runtime.allocate(Object::Tuple(vec![
            fields[0],
            index,
            false_value,
            fields[5],
        ]))?;
        if runtime.truth(fields[3])? {
            install_fixture(runtime, Handle(activation), older)?;
        }
        let selected = runtime.allocate(Object::Tuple(vec![
            fields[0], fields[1], fields[2], fields[5],
        ]))?;
        install_fixture(runtime, Handle(activation), selected)?;
        runtime.int(42)
    });
    if with_runtime(|runtime| runtime.truth(fields[4]).unwrap()) {
        with_runtime(|runtime| runtime.fault = Some(RuntimeError::panic("body")));
    }
    let step = ril_rt_cps_activation_return(activation, continuation, value);
    ril_rt_leave(step)
}
fn run(
    depth: i128,
    panics: bool,
    primary: bool,
    shared: bool,
    cancellation: bool,
) -> (u64, Vec<i128>, Option<RuntimeError>, usize) {
    NATIVE_DEPTH.with(|value| value.set((0, 0)));
    ril_rt_init();
    if shared {
        with_runtime(crate::shared::activate);
    }
    ril_rt_enter();
    let events = ril_rt_sequence(0);
    ril_rt_root(0, events);
    let environment = handle(|runtime| {
        let depth = runtime.int(depth)?;
        let panics = runtime.boolean(panics)?;
        let older = runtime.boolean(primary)?;
        let primary = runtime.boolean(primary)?;
        let cancellation = runtime.boolean(cancellation)?;
        runtime.allocate(Object::Tuple(vec![
            Handle(events),
            depth,
            panics,
            older,
            primary,
            cancellation,
        ]))
    });
    let callable = handle(|runtime| {
        runtime.allocate(Object::BudgetClosure {
            normal: body as *const () as usize as u64,
            metered: body as *const () as usize as u64,
            environment: Handle(environment),
            normal_is_cps: true,
            metered_entry_event: false,
        })
    });
    let end = ril_rt_cps_end();
    let arguments = ril_rt_sequence(1);
    with_runtime(|runtime| {
        let boundary = runtime.unit().unwrap();
        runtime.budgets.begin(2, boundary).unwrap();
    });
    let step = ril_rt_cps_call(callable, arguments, end);
    let result = ril_rt_cps_run(step);
    let (events, error) = with_runtime(|runtime| {
        assert!(runtime.cps_exits.is_empty());
        assert_eq!(runtime.cancellation_mask, 0);
        assert!(runtime.budgets.is_active());
        for _ in 0..2 {
            assert_eq!(
                runtime
                    .budgets
                    .charge(ril_runtime_api::abi::BudgetEvent::FunctionEntry),
                crate::budget::Decision::Execute
            );
        }
        assert!(matches!(
            runtime
                .budgets
                .charge(ril_runtime_api::abi::BudgetEvent::FunctionEntry),
            crate::budget::Decision::Exhaust(_)
        ));
        (
            runtime
                .sequence(Handle(events))
                .unwrap()
                .into_iter()
                .map(|value| runtime.as_integer(value).unwrap())
                .collect(),
            runtime.fault.clone(),
        )
    });
    let (now, peak) = NATIVE_DEPTH.with(Cell::get);
    assert_eq!(now, 0);
    ril_rt_leave(result);
    (result, events, error, peak)
}

#[test]
fn nested_cps_cleanup_uses_one_native_trampoline_and_roots_every_pending_exit() {
    let (result, events, error, peak) = run(2_000, false, false, false, false);
    assert_ne!(result, 0, "{error:?}");
    assert!(error.is_none(), "{error:?}");
    assert_eq!(
        peak, 1,
        "cleanup must not recursively enter a native callback"
    );
    assert_eq!(events, (0..=2_000).rev().collect::<Vec<_>>());
    with_runtime(|runtime| assert_eq!(runtime.as_integer(Handle(result)).unwrap(), 42));
}

#[test]
fn shared_gc_keeps_the_cleanup_resource_and_original_answer_alive() {
    let (result, events, error, peak) = run(256, false, false, true, false);
    assert_ne!(result, 0, "{error:?}");
    assert!(error.is_none());
    assert_eq!(peak, 1);
    assert_eq!(events.len(), 257);
}

#[test]
fn cps_cleanup_failure_preserves_primary_cause_and_abandons_remaining_actions() {
    let (result, events, error, peak) = run(0, true, true, false, false);
    assert_eq!(result, 0);
    let error = error.unwrap();
    assert_eq!(error.tag, OutcomeTag::DoubleFault);
    assert_eq!(error.primary.unwrap().message, "body");
    assert_eq!(error.cleanup.unwrap().message, "cleanup");
    assert_eq!(events, [0]);
    assert_eq!(peak, 1);
}

#[test]
fn cancellation_during_cps_cleanup_waits_for_all_mandatory_nested_actions() {
    let (result, events, error, peak) = run(32, false, false, false, true);
    assert_eq!(result, 0);
    assert_eq!(error.unwrap().tag, OutcomeTag::Cancelled);
    assert_eq!(events, (0..=32).rev().collect::<Vec<_>>());
    assert_eq!(peak, 1);
}
