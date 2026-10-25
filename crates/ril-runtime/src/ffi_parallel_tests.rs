use super::*;
use std::sync::{
    Condvar, Mutex,
    atomic::{AtomicUsize, Ordering},
};
use std::time::{Duration, Instant};

static ACTIVE: AtomicUsize = AtomicUsize::new(0);
static PEAK: AtomicUsize = AtomicUsize::new(0);
static ARRIVED: Mutex<usize> = Mutex::new(0);
static WAKE: Condvar = Condvar::new();

extern "C" fn overlapping_callback(_: u64, arguments: u64) -> u64 {
    let active = ACTIVE.fetch_add(1, Ordering::SeqCst) + 1;
    PEAK.fetch_max(active, Ordering::SeqCst);
    {
        let mut arrived = ARRIVED.lock().unwrap();
        *arrived += 1;
        WAKE.notify_all();
        let deadline = Instant::now() + Duration::from_secs(5);
        while *arrived < 2 && Instant::now() < deadline {
            arrived = WAKE
                .wait_timeout(arrived, Duration::from_millis(10))
                .unwrap()
                .0;
        }
    }
    // A callback does real native work without holding the shared heap gate.
    std::thread::sleep(Duration::from_millis(10));
    let result = handle(|runtime| {
        let argument = runtime.sequence(Handle(arguments))?[0];
        let nested = runtime.allocate(Object::Array(vec![argument]))?;
        runtime.allocate(Object::Array(vec![nested]))
    });
    ACTIVE.fetch_sub(1, Ordering::SeqCst);
    result
}

#[test]
fn bounded_native_workers_overlap_and_retired_results_survive_collection() {
    ril_rt_init();
    ACTIVE.store(0, Ordering::SeqCst);
    PEAK.store(0, Ordering::SeqCst);
    *ARRIVED.lock().unwrap() = 0;
    let callable = handle(|runtime| {
        let environment = runtime.allocate(Object::Unit)?;
        runtime.allocate(Object::Closure {
            function: overlapping_callback as *const () as usize as u64,
            environment,
        })
    });
    let jobs = with_runtime(|runtime| {
        (0..11)
            .map(|index| {
                Ok(Job {
                    callable: Handle(callable),
                    arguments: vec![runtime.int(index)?],
                })
            })
            .collect::<Result<Vec<_>>>()
    })
    .unwrap();
    RUNTIME.with_borrow_mut(crate::shared::activate);
    let values = run_jobs(jobs, 2)
        .unwrap()
        .into_iter()
        .collect::<Result<Vec<_>>>()
        .unwrap();
    assert_eq!(
        PEAK.load(Ordering::SeqCst),
        2,
        "callbacks must actually overlap and respect the bound"
    );
    assert_eq!(
        ACTIVE.load(Ordering::SeqCst),
        0,
        "all started callbacks must finish"
    );
    with_runtime(|runtime| {
        runtime.collect().unwrap();
        for (index, value) in values.into_iter().enumerate() {
            let nested = runtime.sequence(value).unwrap()[0];
            let item = runtime.sequence(nested).unwrap()[0];
            assert_eq!(runtime.as_integer(item).unwrap(), index as i128);
        }
    });
    ril_rt_init();
}

#[test]
fn batch_checks_its_bound_even_when_no_branches_exist() {
    ril_rt_init();
    let (empty, zero, one) = with_runtime(|runtime| {
        (
            runtime.allocate(Object::Array(vec![])).unwrap(),
            runtime.int(0).unwrap(),
            runtime.int(1).unwrap(),
        )
    });
    assert_eq!(
        await_test(execute_batch(&[empty, zero])).unwrap_err().tag,
        OutcomeTag::LanguagePanic
    );
    let output = await_test(execute_batch(&[empty, one])).unwrap();
    with_runtime(|runtime| assert!(runtime.sequence(output).unwrap().is_empty()));
    assert_eq!(
        run_jobs(vec![], 0).unwrap_err().tag,
        OutcomeTag::LanguagePanic
    );
    ril_rt_init();
}

extern "C" fn zero(_: u64, _: u64) -> u64 {
    handle(|runtime| runtime.int(0))
}

extern "C" fn mutating_callback(_: u64, arguments: u64) -> u64 {
    handle(|runtime| {
        let cell = runtime.sequence(Handle(arguments))?[0];
        let original = runtime.field(cell, "value")?;
        let original = runtime.as_integer(original)?;
        let written = runtime.int(original + 10)?;
        runtime.set_field(cell, "value".into(), written)?;
        match original {
            0 => Err(RuntimeError::panic("first")),
            1 => Err(RuntimeError::double_fault(
                RuntimeError::panic("second"),
                RuntimeError::panic("cleanup"),
            )),
            _ => runtime.allocate(Object::Unit),
        }
    })
}

#[test]
fn completed_branches_preserve_all_writes_and_faults_without_arbitration() {
    ril_rt_init();
    let (items, callback) = with_runtime(|runtime| {
        let cells = (0..7)
            .map(|index| {
                let value = runtime.int(index).unwrap();
                runtime
                    .allocate(Object::Record([("value".into(), value)].into()))
                    .unwrap()
            })
            .collect();
        let items = runtime.allocate(Object::Array(cells)).unwrap();
        let environment = runtime.allocate(Object::Unit).unwrap();
        let callback = runtime
            .allocate(Object::Closure {
                function: mutating_callback as *const () as usize as u64,
                environment,
            })
            .unwrap();
        (items, callback)
    });
    RUNTIME.with_borrow_mut(crate::shared::activate);
    let jobs = with_runtime(|runtime| runtime.sequence(items))
        .unwrap()
        .into_iter()
        .map(|item| Job {
            callable: callback,
            arguments: vec![item],
        })
        .collect();
    let outcomes = run_jobs(jobs, 2).unwrap();
    assert_eq!(
        outcomes[0].as_ref().unwrap_err().tag,
        OutcomeTag::LanguagePanic
    );
    assert_eq!(
        outcomes[1].as_ref().unwrap_err().tag,
        OutcomeTag::DoubleFault
    );
    assert_eq!(
        outcomes[1]
            .as_ref()
            .unwrap_err()
            .primary
            .as_ref()
            .unwrap()
            .message,
        "second"
    );
    assert!(outcomes[2..].iter().all(Result::is_ok));
    with_runtime(|runtime| {
        for (index, cell) in runtime.sequence(items).unwrap().into_iter().enumerate() {
            let value = runtime.field(cell, "value").unwrap();
            assert_eq!(runtime.as_integer(value).unwrap(), index as i128 + 10);
        }
    });
    ril_rt_init();
}

#[test]
fn parallel_work_called_by_mandatory_cleanup_inherits_cancellation_protection() {
    ril_rt_init();
    let callable = with_runtime(|runtime| {
        let environment = runtime.allocate(Object::Unit).unwrap();
        let callable = runtime
            .allocate(Object::Closure {
                function: zero as *const () as usize as u64,
                environment,
            })
            .unwrap();
        runtime.cancellation.request();
        runtime.cancellation_mask = 1;
        callable
    });
    RUNTIME.with_borrow_mut(crate::shared::activate);
    let protected = run_jobs(
        vec![Job {
            callable,
            arguments: vec![],
        }],
        1,
    )
    .unwrap();
    assert!(protected[0].is_ok());
    with_runtime(|runtime| runtime.cancellation_mask = 0);
    let cancelled = run_jobs(
        vec![Job {
            callable,
            arguments: vec![],
        }],
        1,
    )
    .unwrap();
    assert_eq!(
        cancelled[0].as_ref().unwrap_err().tag,
        OutcomeTag::Cancelled
    );
    ril_rt_init();
}

extern "C" fn host_fault_after_match(_: u64, arguments: u64) -> u64 {
    handle(|runtime| {
        let item = runtime.sequence(Handle(arguments))?[0];
        if runtime.as_integer(item)? == 0 {
            return runtime.boolean(true);
        }
        panic!("injected host failure inside guarded runtime work");
    })
}

#[test]
fn an_unexpected_host_failure_is_never_a_suppressible_branch_outcome() {
    ril_rt_init();
    let (items, callback) = with_runtime(|runtime| {
        let zero = runtime.int(0).unwrap();
        let one = runtime.int(1).unwrap();
        let items = runtime.allocate(Object::Array(vec![zero, one])).unwrap();
        let environment = runtime.allocate(Object::Unit).unwrap();
        let callback = runtime
            .allocate(Object::Closure {
                function: host_fault_after_match as *const () as usize as u64,
                environment,
            })
            .unwrap();
        (items, callback)
    });
    RUNTIME.with_borrow_mut(crate::shared::activate);
    let jobs = with_runtime(|runtime| runtime.sequence(items))
        .unwrap()
        .into_iter()
        .map(|item| Job {
            callable: callback,
            arguments: vec![item],
        })
        .collect();
    let error = run_jobs(jobs, 2).unwrap_err();
    assert_eq!(error.tag, OutcomeTag::InternalFault);
    ril_rt_init();
}
