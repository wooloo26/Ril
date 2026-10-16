use super::*;
const EXHAUSTED: u64 = 0x00b0_d6e7;
fn item(arguments: u64, index: usize) -> u64 {
    handle(|runtime| {
        let values = runtime.sequence(Handle(arguments))?;
        values
            .get(index)
            .copied()
            .ok_or_else(|| RuntimeError::internal("missing budget fixture argument"))
    })
}
fn continuation(arguments: u64) -> u64 {
    handle(|runtime| {
        runtime
            .sequence(Handle(arguments))?
            .last()
            .copied()
            .ok_or_else(|| RuntimeError::internal("missing budget fixture continuation"))
    })
}
extern "C" fn ordinary_one(_environment: u64, _arguments: u64) -> u64 {
    ril_rt_enter();
    let value = ril_rt_int(42, 0, 64, 1);
    ril_rt_leave(value)
}
extern "C" fn metered_one(_environment: u64, arguments: u64) -> u64 {
    with_runtime(|runtime| {
        let unit = runtime.unit().unwrap();
        runtime.globals.insert("entered".into(), unit);
    });
    ril_rt_enter();
    ril_rt_root(0, arguments);
    let next = continuation(arguments);
    let activation = ril_rt_cps_activation_new();
    let environment =
        handle(|runtime| runtime.allocate(Object::Tuple(vec![Handle(next), Handle(activation)])));
    let next = ril_rt_cps_continuation(one_after as *const () as usize as u64, environment);
    let step = ril_rt_cps_charge(BudgetEvent::FunctionEntry as u32, next);
    ril_rt_leave(step)
}
extern "C" fn one_after(environment: u64, _arguments: u64) -> u64 {
    ril_rt_enter();
    ril_rt_root(0, environment);
    let next = item(environment, 0);
    let activation = item(environment, 1);
    let value = ril_rt_int(42, 0, 64, 1);
    let step = ril_rt_cps_activation_return(activation, next, value);
    ril_rt_leave(step)
}
extern "C" fn body(environment: u64, arguments: u64) -> u64 {
    ril_rt_enter();
    ril_rt_root(0, environment);
    ril_rt_root(1, arguments);
    let limit = item(environment, 0);
    let action = item(environment, 1);
    let next = continuation(arguments);
    let step = ril_rt_cps_budget(limit, action, next, EXHAUSTED);
    ril_rt_leave(step)
}
extern "C" fn recovery(_environment: u64, arguments: u64) -> u64 {
    ril_rt_enter();
    ril_rt_root(0, arguments);
    with_runtime(|runtime| {
        let count = runtime.int(1).unwrap();
        runtime.globals.insert("recovered".into(), count);
    });
    let next = continuation(arguments);
    let value = ril_rt_int(99, 0, 64, 1);
    let step = ril_rt_cps_return(next, value);
    ril_rt_leave(step)
}
fn setup(
    limit: i128,
    normal: extern "C" fn(u64, u64) -> u64,
    metered: extern "C" fn(u64, u64) -> u64,
    handled: bool,
) -> u64 {
    setup_with_flags(limit, normal, metered, handled, 2)
}
fn setup_with_flags(
    limit: i128,
    normal: extern "C" fn(u64, u64) -> u64,
    metered: extern "C" fn(u64, u64) -> u64,
    handled: bool,
    flags: u32,
) -> u64 {
    ril_rt_init();
    ril_rt_enter();
    let unit = ril_rt_unit();
    let action = ril_rt_callable_with_budget(
        normal as *const () as usize as u64,
        metered as *const () as usize as u64,
        unit,
        flags,
    );
    with_runtime(|runtime| {
        runtime.globals.insert("action".into(), Handle(action));
    });
    let limit = handle(|runtime| runtime.int(limit));
    let environment =
        handle(|runtime| runtime.allocate(Object::Tuple(vec![Handle(limit), Handle(action)])));
    let body = ril_rt_cps_callable(body as *const () as usize as u64, environment);
    let end = ril_rt_cps_end();
    if handled {
        let arm = ril_rt_cps_callable(recovery as *const () as usize as u64, unit);
        let table = ril_rt_cps_handlers();
        ril_rt_cps_handler_add(table, EXHAUSTED, arm);
        ril_rt_cps_handle(body, table, end, 0)
    } else {
        let arguments = ril_rt_sequence(1);
        ril_rt_cps_call(body, arguments, end)
    }
}
#[test]
fn zero_one_and_negative_allowances_have_distinct_native_transitions() {
    let step = setup(0, ordinary_one, metered_one, true);
    let answer = ril_rt_cps_run(step);
    assert_eq!(ril_rt_status(), 0);
    with_runtime(|runtime| {
        assert_eq!(runtime.as_integer(Handle(answer)).unwrap(), 99);
        assert!(!runtime.globals.contains_key("entered"));
        assert!(!runtime.budgets.is_active());
    });
    let step = setup(1, ordinary_one, metered_one, true);
    let answer = ril_rt_cps_run(step);
    assert_eq!(ril_rt_status(), 0);
    with_runtime(|runtime| {
        assert_eq!(runtime.as_integer(Handle(answer)).unwrap(), 42);
        assert!(!runtime.globals.contains_key("recovered"));
        assert!(runtime.globals.contains_key("entered"));
        assert!(!runtime.budgets.is_active());
    });
    let step = setup(-1, ordinary_one, metered_one, true);
    assert_eq!(ril_rt_cps_run(step), 0);
    with_runtime(|runtime| {
        assert_eq!(
            runtime.fault.as_ref().unwrap().tag,
            OutcomeTag::LanguagePanic
        );
        assert!(!runtime.globals.contains_key("recovered"));
    });
}
#[test]
fn unhandled_exhaustion_is_a_language_panic_after_abandoning_the_action() {
    let step = setup(0, ordinary_one, metered_one, false);
    assert_eq!(ril_rt_cps_run(step), 0);
    with_runtime(|runtime| {
        assert_eq!(
            runtime.fault.as_ref().unwrap().tag,
            OutcomeTag::LanguagePanic
        );
        assert!(
            runtime
                .fault
                .as_ref()
                .unwrap()
                .message
                .contains("Div exhaustion")
        );
    });
}
extern "C" fn spin(_environment: u64, arguments: u64) -> u64 {
    ril_rt_enter();
    ril_rt_root(0, arguments);
    let next = continuation(arguments);
    let activation = ril_rt_cps_activation_new();
    let environment =
        handle(|runtime| runtime.allocate(Object::Tuple(vec![Handle(next), Handle(activation)])));
    let after = ril_rt_cps_continuation(spin_after as *const () as usize as u64, environment);
    let step = ril_rt_cps_charge(BudgetEvent::FunctionEntry as u32, after);
    ril_rt_leave(step)
}
extern "C" fn spin_after(environment: u64, _arguments: u64) -> u64 {
    ril_rt_enter();
    ril_rt_root(0, environment);
    let next = item(environment, 0);
    let action = with_runtime(|runtime| runtime.globals["action"].0);
    let arguments = ril_rt_sequence(1);
    let step = ril_rt_cps_call(action, arguments, next);
    ril_rt_leave(step)
}
#[test]
fn twenty_thousand_protected_recursive_entries_use_the_single_trampoline() {
    let step = setup(20_000, ordinary_one, spin, true);
    let answer = ril_rt_cps_run(step);
    assert_eq!(ril_rt_status(), 0);
    with_runtime(|runtime| {
        assert_eq!(runtime.as_integer(Handle(answer)).unwrap(), 99);
        assert!(!runtime.budgets.is_active());
        assert_eq!(runtime.cps_activation, Handle::INVALID);
    });
}

fn builtin_length(arguments: u64, callback: bool) -> u64 {
    ril_rt_enter();
    ril_rt_root(0, arguments);
    let next = continuation(arguments);
    let callable = handle(|runtime| runtime.allocate(Object::Builtin("len".into())));
    let data = handle(|runtime| runtime.allocate(Object::Bytes(b"abc".to_vec().into())));
    let args = handle(|runtime| runtime.allocate(Object::Tuple(vec![Handle(data)])));
    let step = if callback {
        ril_rt_cps_callback_call(callable, args, next)
    } else {
        ril_rt_cps_call(callable, args, next)
    };
    ril_rt_leave(step)
}
extern "C" fn ordinary_primitive(_environment: u64, arguments: u64) -> u64 {
    builtin_length(arguments, false)
}
extern "C" fn callback_primitive(_environment: u64, arguments: u64) -> u64 {
    builtin_length(arguments, true)
}
#[test]
fn finite_primitives_are_free_but_synthetic_and_builtin_callback_entries_are_charged() {
    // Internal C ABI fixture: a synthetic wrapper has no generated prologue,
    // so the protected invocation supplies its one abstract entry event.
    for (limit, action, expected) in [
        (1, ordinary_primitive as extern "C" fn(u64, u64) -> u64, 3),
        (1, callback_primitive, 99),
        (2, callback_primitive, 3),
    ] {
        let step = setup_with_flags(limit, ordinary_one, action, true, 0);
        let answer = ril_rt_cps_run(step);
        assert_eq!(ril_rt_status(), 0);
        with_runtime(|runtime| {
            assert_eq!(runtime.as_integer(Handle(answer)).unwrap(), expected);
            assert!(!runtime.budgets.is_active());
        });
    }
}
