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
                Ok(Job::Call {
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
fn independent_completion_ranks_faults_but_preserves_index_ties() {
    let panic = RuntimeError::panic("first");
    let double = RuntimeError::double_fault(
        RuntimeError::panic("second"),
        RuntimeError::panic("cleanup"),
    );
    let selected = complete_independent(vec![
        Err(panic),
        Err(double.clone()),
        Err(RuntimeError::double_fault(
            RuntimeError::panic("third"),
            RuntimeError::panic("later"),
        )),
    ])
    .unwrap_err();
    assert_eq!(selected.tag, OutcomeTag::DoubleFault);
    assert_eq!(selected.message, double.message);
}

extern "C" fn indexed_fold(_: u64, arguments: u64) -> u64 {
    handle(|runtime| {
        let arguments = runtime.sequence(Handle(arguments))?;
        if runtime.as_integer(arguments[1])? == 65 {
            return Err(RuntimeError::panic("fold-local"));
        }
        Ok(arguments[0])
    })
}
extern "C" fn zero(_: u64, _: u64) -> u64 {
    handle(|runtime| runtime.int(0))
}

#[test]
fn fold_local_fault_records_original_source_index() {
    ril_rt_init();
    let (init, local, items) = with_runtime(|runtime| {
        let environment = runtime.allocate(Object::Unit).unwrap();
        let init = runtime
            .allocate(Object::Closure {
                function: zero as *const () as usize as u64,
                environment,
            })
            .unwrap();
        let local = runtime
            .allocate(Object::Closure {
                function: indexed_fold as *const () as usize as u64,
                environment,
            })
            .unwrap();
        let items = (0..130).map(|index| runtime.int(index).unwrap()).collect();
        (init, local, items)
    });
    RUNTIME.with_borrow_mut(crate::shared::activate);
    let error = fold(items, init, local, local).unwrap_err();
    assert_eq!(error.message, "fold-local");
    assert_eq!(error.index, Some(65));
    ril_rt_init();
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
fn for_each_finishes_all_independent_writes_before_selecting_double_fault() {
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
    let error = execute("for_each", &[items, callback]).unwrap_err();
    assert_eq!(error.tag, OutcomeTag::DoubleFault);
    assert_eq!(error.primary.unwrap().message, "second");
    with_runtime(|runtime| {
        for (index, cell) in runtime.sequence(items).unwrap().into_iter().enumerate() {
            let value = runtime.field(cell, "value").unwrap();
            assert_eq!(runtime.as_integer(value).unwrap(), index as i128 + 10);
        }
    });
    ril_rt_init();
}

extern "C" fn indexed_failure(_: u64, _: u64) -> u64 {
    handle(|_| {
        let mut error = RuntimeError::panic("nested fold");
        error.index = Some(17);
        Err(error)
    })
}

#[test]
fn fold_initialization_and_merge_faults_have_no_source_index() {
    ril_rt_init();
    let (normal, failure, item) = with_runtime(|runtime| {
        let environment = runtime.allocate(Object::Unit).unwrap();
        let normal = runtime
            .allocate(Object::Closure {
                function: zero as *const () as usize as u64,
                environment,
            })
            .unwrap();
        let failure = runtime
            .allocate(Object::Closure {
                function: indexed_failure as *const () as usize as u64,
                environment,
            })
            .unwrap();
        let item = runtime.int(0).unwrap();
        (normal, failure, item)
    });
    RUNTIME.with_borrow_mut(crate::shared::activate);
    let init_error = fold(vec![], failure, normal, normal).unwrap_err();
    assert_eq!(init_error.index, None);
    let merge_error = fold(vec![item; 65], normal, normal, failure).unwrap_err();
    assert_eq!(merge_error.index, None);
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
        vec![Job::Call {
            callable,
            arguments: vec![],
        }],
        1,
    )
    .unwrap();
    assert!(protected[0].is_ok());
    with_runtime(|runtime| runtime.cancellation_mask = 0);
    let cancelled = run_jobs(
        vec![Job::Call {
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
fn a_decisive_match_never_suppresses_an_unexpected_host_failure() {
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
    let error = execute("find", &[items, callback]).unwrap_err();
    assert_eq!(error.tag, OutcomeTag::InternalFault);
    ril_rt_init();
}
