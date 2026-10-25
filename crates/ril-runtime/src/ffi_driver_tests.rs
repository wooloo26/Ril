use super::*;
use std::{num::NonZeroUsize, sync::Arc, task::Poll};

extern "C" fn next_step(environment: u64, _arguments: u64) -> u64 {
    environment
}

fn chain(length: usize) -> (u64, u64) {
    let value = ril_rt_int(37, 0, 64, 1);
    let mut next = handle(|runtime| {
        runtime.allocate(Object::CpsStep(Step::Complete {
            value: Handle(value),
        }))
    });
    for _ in 0..length {
        let continuation = ril_rt_cps_continuation(next_step as *const () as usize as u64, next);
        let unit = ril_rt_unit();
        next = return_step(Handle(continuation), unit);
    }
    // This private test heap has no collector before start_driver. Do not keep
    // the entire constructed chain alive in its caller's temporary-root list.
    ril_rt_statement_end();
    (next, value)
}

#[test]
fn suspended_driver_keeps_its_current_step_rooted_across_collection() {
    ril_rt_init();
    let (initial, expected) = chain(200);
    let mut driver = start_driver(initial);
    let mut slices = 0;
    let mut collected = 0;
    loop {
        match drive_slice(&mut driver, NonZeroUsize::new(1).unwrap()) {
            Poll::Pending => {
                slices += 1;
                collected += with_runtime(|runtime| runtime.collect().unwrap());
            }
            Poll::Ready(value) => {
                assert_eq!(value, expected);
                assert_eq!(
                    with_runtime(|runtime| runtime.as_integer(Handle(value)).unwrap()),
                    37
                );
                break;
            }
        }
    }
    // Continuation restoration may itself require a native exit step.
    assert!(slices >= 200);
    assert!(collected > 0, "completed steps must actually be reclaimed");
    assert_eq!(ril_rt_status(), 0);
}

#[test]
fn driver_and_logical_runtime_can_move_together_to_another_os_worker() {
    ril_rt_init();
    let (initial, _) = chain(100);
    let mut driver = start_driver(initial);
    assert!(drive_slice(&mut driver, NonZeroUsize::new(1).unwrap()).is_pending());
    let state = RUNTIME.with_borrow_mut(std::mem::take);
    let worker = std::thread::spawn(move || {
        RUNTIME.with_borrow_mut(|runtime| *runtime = state);
        let result = loop {
            with_runtime(|runtime| {
                runtime.collect().unwrap();
            });
            if let Poll::Ready(value) = drive_slice(&mut driver, NonZeroUsize::new(3).unwrap()) {
                break with_runtime(|runtime| runtime.as_integer(Handle(value)).unwrap());
            }
        };
        assert_eq!(ril_rt_status(), 0);
        RUNTIME.with_borrow_mut(|runtime| *runtime = Runtime::default());
        result
    });
    assert_eq!(worker.join().unwrap(), 37);
}

#[test]
fn another_runtime_cannot_resume_a_driver_with_same_numeric_handles() {
    ril_rt_init();
    let (initial, _) = chain(2);
    let mut driver = start_driver(initial);
    let original = RUNTIME.with_borrow_mut(std::mem::take);
    let _ = chain(2); // Different heap can reuse the same handle bits.
    assert_eq!(
        drive_slice(&mut driver, NonZeroUsize::new(1).unwrap()),
        Poll::Ready(0)
    );
    assert_eq!(
        with_runtime(|runtime| runtime.fault.as_ref().unwrap().tag),
        OutcomeTag::InternalFault
    );
    RUNTIME.with_borrow_mut(|runtime| *runtime = original);
    while drive_slice(&mut driver, NonZeroUsize::new(1).unwrap()).is_pending() {}
    assert_eq!(ril_rt_status(), 0);
}

#[test]
fn starting_with_a_fault_does_not_pop_the_callers_root_frame() {
    ril_rt_init();
    ril_rt_enter();
    let value = ril_rt_int(91, 0, 64, 1);
    ril_rt_root(77, value);
    ril_rt_statement_end();
    with_runtime(|runtime| runtime.fault = Some(RuntimeError::panic("initial fault")));
    assert_eq!(ril_rt_cps_run(0), 0);
    with_runtime(|runtime| {
        assert_eq!(
            runtime.fault.as_ref().unwrap().tag,
            OutcomeTag::LanguagePanic
        );
        runtime.fault = None;
        runtime.collect().unwrap();
        assert_eq!(runtime.as_integer(Handle(value)).unwrap(), 91);
    });
    ril_rt_leave(0);
}

#[test]
fn bounded_executor_polls_multiple_native_runtimes_without_mixing_their_heaps() {
    let executor = crate::scheduler::Executor::new(NonZeroUsize::new(2).unwrap()).unwrap();
    let mut pending = Vec::new();
    for index in 1..=12 {
        ril_rt_init();
        let (initial, _) = chain(index * 20);
        let runtime = RUNTIME.with_borrow_mut(std::mem::take);
        pending.push(
            executor
                .spawn(NativeComputation::new(runtime, initial))
                .unwrap(),
        );
    }
    for task in pending {
        let NativeCompletion { mut runtime, value } = task.wait().unwrap();
        assert!(runtime.fault.is_none(), "{:?}", runtime.fault);
        runtime.collect().unwrap();
        assert_eq!(runtime.as_integer(Handle(value)).unwrap(), 37);
    }
    executor.shutdown_idle().unwrap();
}

fn sleeping(
    nanos: i64,
) -> (
    NativeComputation,
    std::sync::Arc<crate::process_io::Cancellation>,
) {
    ril_rt_init();
    let duration = handle(|runtime| {
        let nanos = runtime.integer(i128::from(nanos), 64, true)?;
        runtime.allocate(Object::Nominal {
            tag: "Time::Duration".into(),
            payload: nanos,
        })
    });
    let callable = handle(|runtime| runtime.allocate(Object::Builtin("Time::sleep".into())));
    let arguments = handle(|runtime| runtime.allocate(Object::Tuple(vec![Handle(duration)])));
    let continuation = ril_rt_cps_end();
    let initial = ril_rt_cps_call(callable, arguments, continuation);
    ril_rt_statement_end();
    let runtime = RUNTIME.with_borrow_mut(std::mem::take);
    let cancellation = runtime.cancellation.clone();
    (NativeComputation::new(runtime, initial), cancellation)
}

#[test]
fn native_sleep_releases_the_cpu_worker_and_cancellation_completes_its_driver() {
    let executor = crate::scheduler::Executor::new(NonZeroUsize::new(1).unwrap()).unwrap();
    let (sleep, cancellation) = sleeping(60_000_000_000);
    let sleeping = executor.spawn(sleep).unwrap();
    ril_rt_init();
    let (initial, _) = chain(2);
    let runtime = RUNTIME.with_borrow_mut(std::mem::take);
    let (send, receive) = std::sync::mpsc::channel();
    let quick = executor
        .spawn(async move {
            let result = NativeComputation::new(runtime, initial).await;
            send.send(result.runtime.as_integer(Handle(result.value)).unwrap())
                .unwrap();
        })
        .unwrap();
    let progress = receive.recv_timeout(std::time::Duration::from_secs(2));
    // Cancel even on a failure, so the regression cannot leave a minute-long
    // host wait behind when reporting a worker-starvation failure.
    cancellation.request();
    assert_eq!(progress.unwrap(), 37);
    quick.wait().unwrap();
    let result = sleeping.wait().unwrap();
    assert_eq!(result.value, 0);
    assert_eq!(result.runtime.fault.unwrap().tag, OutcomeTag::Cancelled);
    executor.shutdown_idle().unwrap();
}

#[test]
fn pending_native_sleep_keeps_its_continuation_and_arguments_rooted() {
    let (mut sleep, cancellation) = sleeping(60_000_000_000);
    let mut context = std::task::Context::from_waker(std::task::Waker::noop());
    assert!(std::future::Future::poll(std::pin::Pin::new(&mut sleep), &mut context).is_pending());
    sleep.runtime.as_mut().unwrap().collect().unwrap();
    cancellation.request();
    let Poll::Ready(result) =
        std::future::Future::poll(std::pin::Pin::new(&mut sleep), &mut context)
    else {
        panic!("cancelled sleep did not finish its native driver");
    };
    assert_eq!(result.runtime.fault.unwrap().tag, OutcomeTag::Cancelled);
}

#[test]
fn native_join_parks_one_worker_until_a_queued_producer_publishes_a_rooted_result() {
    ril_rt_init();
    RUNTIME.with_borrow_mut(crate::shared::activate);
    let (scope, task, scope_handle, task_handle) = with_runtime(|runtime| {
        let scope = crate::concurrent::Scope::new(&runtime.cancellation).unwrap();
        let action = runtime.unit().unwrap();
        let task = scope.reserve(action, runtime.task_owner).unwrap();
        let scope_handle = runtime.allocate(Object::TaskScope(scope.clone())).unwrap();
        let task_handle = runtime.allocate(Object::Task(task.clone())).unwrap();
        runtime.root(8, scope_handle).unwrap();
        runtime.scope_lineage.push(scope.id());
        runtime.scope_registry.push(scope.clone());
        (scope, task, scope_handle, task_handle)
    });
    let mut child = RUNTIME
        .with_borrow(|runtime| {
            crate::shared::fork_runtime(runtime, &[scope_handle, task_handle], Arc::default())
        })
        .unwrap();
    let callable = handle(|runtime| runtime.allocate(Object::Builtin("Concurrent::join".into())));
    let arguments = handle(|runtime| runtime.allocate(Object::Tuple(vec![task_handle])));
    let end = ril_rt_cps_end();
    let initial = ril_rt_cps_call(callable, arguments, end);
    let runtime = RUNTIME.with_borrow_mut(std::mem::take);
    let cancellation = runtime.cancellation.clone();
    let executor = crate::scheduler::Executor::new(NonZeroUsize::new(1).unwrap()).unwrap();
    let waiter = executor
        .spawn(NativeComputation::new(runtime, initial))
        .unwrap();
    let (send, receive) = std::sync::mpsc::channel();
    let publisher = executor
        .spawn(async move {
            crate::shared::with_runtime(&mut child, |runtime| {
                let value = runtime.integer(29, 64, true).unwrap();
                task.complete(Ok(value)).unwrap();
                runtime.statement_end();
                runtime.collect().unwrap();
            });
            send.send(()).unwrap();
        })
        .unwrap();
    let progress = receive.recv_timeout(std::time::Duration::from_secs(2));
    if progress.is_err() {
        cancellation.request();
    }
    progress.unwrap();
    publisher.wait().unwrap();
    let NativeCompletion { mut runtime, value } = waiter.wait().unwrap();
    assert!(runtime.fault.is_none(), "{:?}", runtime.fault);
    crate::shared::with_runtime(&mut runtime, |runtime| {
        runtime.statement_end();
        runtime.root(9, Handle(value)).unwrap();
        runtime.collect().unwrap();
        let Object::Variant { tag, fields } = runtime.heap.get(Handle(value)).unwrap() else {
            panic!();
        };
        assert_eq!(tag, "Ok");
        assert_eq!(runtime.as_integer(fields[0]).unwrap(), 29);
    });
    assert!(scope.finish(false).unwrap().is_none());
    executor.shutdown_idle().unwrap();
}

#[test]
fn native_channel_waits_release_one_worker_and_keep_pending_values_rooted() {
    for full in [false, true] {
        ril_rt_init();
        RUNTIME.with_borrow_mut(crate::shared::activate);
        let (scope, scope_handle, sender, receiver, payload) = with_runtime(|runtime| {
            let scope = crate::concurrent::Scope::new(&runtime.cancellation).unwrap();
            let scope_handle = runtime.allocate(Object::TaskScope(scope.clone())).unwrap();
            runtime.root(8, scope_handle).unwrap();
            runtime.scope_lineage.push(scope.id());
            runtime.scope_registry.push(scope.clone());
            let pair = runtime.create_channel(1).unwrap();
            let pair = runtime.sequence(pair).unwrap();
            let payload = runtime.integer(41, 64, true).unwrap();
            (scope, scope_handle, pair[0], pair[1], payload)
        });
        if full {
            let tx = with_runtime(|runtime| match runtime.heap.get(sender).unwrap() {
                Object::ChannelSender(tx) => tx.clone(),
                _ => panic!(),
            });
            tx.send(
                crate::channel::Context {
                    owner: Default::default(),
                    lineage: &[scope.id()],
                },
                crate::channel::Message::new(payload, vec![]),
                &Default::default(),
            )
            .unwrap();
        }
        let child = RUNTIME
            .with_borrow(|runtime| {
                crate::shared::fork_runtime(
                    runtime,
                    &[scope_handle, sender, receiver, payload],
                    Arc::default(),
                )
            })
            .unwrap();
        let call = |send: bool| {
            let (callable, arguments) = with_runtime(|runtime| {
                let callable = runtime
                    .allocate(Object::Builtin(
                        if send {
                            "Channel::send"
                        } else {
                            "Channel::recv"
                        }
                        .into(),
                    ))
                    .unwrap();
                let args = if send {
                    vec![sender, payload]
                } else {
                    vec![receiver]
                };
                (callable, runtime.allocate(Object::Tuple(args)).unwrap())
            });
            let end = ril_rt_cps_end();
            ril_rt_cps_call(callable.0, arguments.0, end)
        };
        let waiting_step = call(full);
        let waiting_runtime = RUNTIME.with_borrow_mut(|runtime| std::mem::replace(runtime, child));
        let cancellation = waiting_runtime.cancellation.clone();
        let peer_step = call(!full);
        let mut peer_runtime = RUNTIME.with_borrow_mut(std::mem::take);
        let executor = crate::scheduler::Executor::new(NonZeroUsize::new(1).unwrap()).unwrap();
        let waiter = executor
            .spawn(NativeComputation::new(waiting_runtime, waiting_step))
            .unwrap();
        let (send, receive) = std::sync::mpsc::channel();
        let peer = executor
            .spawn(async move {
                crate::shared::with_runtime(&mut peer_runtime, |runtime| {
                    runtime.collect().unwrap();
                });
                let completed = NativeComputation::new(peer_runtime, peer_step).await;
                send.send(()).unwrap();
                completed
            })
            .unwrap();
        let progress = receive.recv_timeout(std::time::Duration::from_secs(2));
        if progress.is_err() {
            cancellation.request();
        }
        progress.unwrap();
        for (completed, sending) in [
            (waiter.wait().unwrap(), full),
            (peer.wait().unwrap(), !full),
        ] {
            let NativeCompletion { mut runtime, value } = completed;
            assert!(runtime.fault.is_none(), "{:?}", runtime.fault);
            crate::shared::with_runtime(&mut runtime, |runtime| {
                runtime.root(9, Handle(value)).unwrap();
                runtime.statement_end();
                runtime.collect().unwrap();
                let Object::Variant { tag, fields } = runtime.heap.get(Handle(value)).unwrap()
                else {
                    panic!();
                };
                assert_eq!(tag, "Ok");
                assert_eq!(fields.len(), 1);
                if sending {
                    assert!(matches!(runtime.heap.get(fields[0]).unwrap(), Object::Unit));
                } else {
                    assert_eq!(runtime.as_integer(fields[0]).unwrap(), 41);
                }
            });
        }
        assert!(scope.finish(false).unwrap().is_none());
        executor.shutdown_idle().unwrap();
    }
}

#[test]
fn native_scope_normal_and_fault_exits_park_until_queued_children_finish() {
    for mode in 0..3 {
        let fault = mode == 1;
        let recover_child = mode == 2;
        ril_rt_init();
        RUNTIME.with_borrow_mut(crate::shared::activate);
        let mut driver = start_driver(0);
        let end = Handle(ril_rt_cps_end());
        let (scope, task, scope_handle, body) = with_runtime(|runtime| {
            let parent_cancellation = runtime.cancellation.clone();
            let scope = crate::concurrent::Scope::new(&parent_cancellation).unwrap();
            let scope_handle = runtime.allocate(Object::TaskScope(scope.clone())).unwrap();
            let unit = runtime.unit().unwrap();
            let task = scope.reserve(unit, runtime.task_owner).unwrap();
            let parent_activation = runtime.cps_activation;
            let activation = runtime.new_activation().unwrap();
            let lineage_depth = runtime.scope_lineage.len();
            runtime.cps_activation = activation;
            runtime.cancellation = scope.body_cancellation.clone();
            runtime.scope_lineage.push(scope.id());
            runtime.scope_registry.push(scope.clone());
            runtime
                .concurrent_scopes
                .push(crate::concurrent::ActiveScope {
                    scope: scope.clone(),
                    value: scope_handle,
                    continuation: end,
                    handlers: runtime.cps_handlers,
                    activation,
                    parent_activation,
                    parent_cancellation,
                    lineage_depth,
                    delimiters: runtime.cps_delimiters.clone(),
                    budget_depth: runtime.budgets.depth(),
                });
            let body = runtime.integer(43, 64, true).unwrap();
            let body = runtime.variant("Ok", vec![body]).unwrap();
            (scope, task, scope_handle, body)
        });
        let mut child = RUNTIME
            .with_borrow(|runtime| {
                crate::shared::fork_runtime(runtime, &[scope_handle], Arc::default())
            })
            .unwrap();
        let initial = if recover_child {
            task.complete(Err(RuntimeError::panic("child"))).unwrap();
            with_runtime(|runtime| runtime.fault = Some(RuntimeError::cancelled()));
            let initial = concurrent::after_unwind(Some(scope_handle), 0);
            assert_ne!(
                initial, 0,
                "mandatory scope drain must survive the cancelled body token"
            );
            assert!(with_runtime(|runtime| runtime.fault.is_none()));
            initial
        } else if fault {
            with_runtime(|runtime| runtime.fault = Some(RuntimeError::panic("body")));
            0
        } else {
            concurrent::finish(scope_handle, Some(body))
        };
        driver.current = initial;
        let runtime = RUNTIME.with_borrow_mut(std::mem::take);
        let computation = NativeComputation {
            runtime: Some(runtime),
            driver: Some(driver),
            initial,
        };
        let executor = crate::scheduler::Executor::new(NonZeroUsize::new(1).unwrap()).unwrap();
        let waiter = executor.spawn(computation).unwrap();
        let completing = task.clone();
        let (send, receive) = std::sync::mpsc::channel();
        let producer = executor
            .spawn(async move {
                assert_eq!(completing.cancellation.requested(), fault || recover_child);
                crate::shared::with_runtime(&mut child, |runtime| {
                    runtime.statement_end();
                    runtime.collect().unwrap();
                    let result = if fault {
                        Err(RuntimeError::cancelled())
                    } else {
                        runtime.unit()
                    };
                    if !recover_child {
                        completing.complete(result).unwrap();
                    }
                });
                send.send(()).unwrap();
            })
            .unwrap();
        let progress = receive.recv_timeout(std::time::Duration::from_secs(2));
        if progress.is_err() {
            let _ = task.complete(Err(RuntimeError::cancelled()));
        }
        progress.unwrap();
        producer.wait().unwrap();
        let NativeCompletion { mut runtime, value } = waiter.wait().unwrap();
        assert!(runtime.concurrent_scopes.is_empty());
        if fault {
            assert_eq!(
                runtime.fault.as_ref().unwrap().tag,
                OutcomeTag::LanguagePanic
            );
            assert_eq!(runtime.fault.as_ref().unwrap().message, "body");
        } else {
            assert!(runtime.fault.is_none(), "{:?}", runtime.fault);
            crate::shared::with_runtime(&mut runtime, |runtime| {
                let Object::Variant { tag, fields } = runtime.heap.get(Handle(value)).unwrap()
                else {
                    panic!();
                };
                if recover_child {
                    assert_eq!(tag, "Err");
                    assert!(
                        matches!(runtime.heap.get(fields[0]).unwrap(), Object::Variant { tag, .. } if tag == "Concurrent::TaskFault::Panicked")
                    );
                } else {
                    assert_eq!(tag, "Ok");
                    assert_eq!(runtime.as_integer(fields[0]).unwrap(), 43);
                }
            });
        }
        assert!(
            task.join(&Default::default()).is_ok(),
            "scope drain must not observe the Result"
        );
        assert!(scope.reserve(Handle::INVALID, Default::default()).is_err());
        executor.shutdown_idle().unwrap();
    }
}

#[test]
fn native_process_wait_leaves_one_cpu_worker_free_and_reaps_before_completion() {
    use crate::native_string::NativeString;
    let directory = tempfile::tempdir().unwrap();
    let ready = directory.path().join("ready");
    ril_rt_init();
    RUNTIME.with_borrow_mut(crate::shared::activate);
    let (callable, arguments) = with_runtime(|runtime| {
        let program = runtime
            .allocate(Object::Path(NativeString::from_os(
                std::env::current_exe().unwrap().as_os_str(),
            )))
            .unwrap();
        let args = [
            "--exact",
            "process_io::tests::child_fixture",
            "--ignored",
            "--nocapture",
        ]
        .into_iter()
        .map(|value| {
            runtime
                .allocate(Object::NativeString(NativeString::from_text(value)))
                .unwrap()
        })
        .collect();
        let args = runtime.allocate(Object::Array(args)).unwrap();
        let command = runtime
            .process_builtin("Process::command", &[program, args])
            .unwrap();
        let mut env = Vec::new();
        for (key, value) in [
            (
                "RIL_PROCESS_IO_FIXTURE",
                NativeString::from_text("signal_sleep"),
            ),
            (
                "RIL_PROCESS_IO_READY",
                NativeString::from_os(ready.as_os_str()),
            ),
        ] {
            let key = runtime
                .allocate(Object::NativeString(NativeString::from_text(key)))
                .unwrap();
            let value = runtime.allocate(Object::NativeString(value)).unwrap();
            env.push(runtime.allocate(Object::Tuple(vec![key, value])).unwrap());
        }
        let env = runtime.allocate(Object::Array(env)).unwrap();
        let env = runtime.variant("Some", vec![env]).unwrap();
        runtime.set_field(command, "env".into(), env).unwrap();
        let null = runtime
            .variant("Process::OutputMode::Null", vec![])
            .unwrap();
        runtime.set_field(command, "stdout".into(), null).unwrap();
        runtime.set_field(command, "stderr".into(), null).unwrap();
        let null = runtime.variant("Process::Input::Null", vec![]).unwrap();
        runtime.set_field(command, "input".into(), null).unwrap();
        let callable = runtime
            .allocate(Object::Builtin("Process::run".into()))
            .unwrap();
        (
            callable,
            runtime.allocate(Object::Tuple(vec![command])).unwrap(),
        )
    });
    let end = ril_rt_cps_end();
    let initial = ril_rt_cps_call(callable.0, arguments.0, end);
    let mut peer_runtime = RUNTIME
        .with_borrow(|runtime| crate::shared::fork_runtime(runtime, &[], Arc::default()))
        .unwrap();
    let runtime = RUNTIME.with_borrow_mut(std::mem::take);
    let cancellation = runtime.cancellation.clone();
    let executor = crate::scheduler::Executor::new(NonZeroUsize::new(1).unwrap()).unwrap();
    let waiting = executor
        .spawn(NativeComputation::new(runtime, initial))
        .unwrap();
    let started = std::time::Instant::now();
    while !ready.exists() && started.elapsed() < std::time::Duration::from_secs(5) {
        std::thread::sleep(std::time::Duration::from_millis(5));
    }
    if !ready.exists() {
        cancellation.request();
    }
    assert!(
        ready.exists(),
        "isolated process must actually be running before cancelling"
    );
    let token = cancellation.clone();
    let (send, receive) = std::sync::mpsc::channel();
    let peer = executor
        .spawn(async move {
            crate::shared::with_runtime(&mut peer_runtime, |runtime| {
                runtime.collect().unwrap();
            });
            token.request();
            send.send(()).unwrap();
        })
        .unwrap();
    let progress = receive.recv_timeout(std::time::Duration::from_secs(2));
    cancellation.request();
    progress.unwrap();
    peer.wait().unwrap();
    let result = waiting.wait().unwrap();
    assert_eq!(result.value, 0);
    assert_eq!(result.runtime.fault.unwrap().tag, OutcomeTag::Cancelled);
    executor.shutdown_idle().unwrap();
}

extern "C" fn parallel_collecting_leaf(_: u64, arguments: u64) -> u64 {
    handle(|runtime| {
        runtime.collect()?;
        let item = runtime.sequence(Handle(arguments))?[0];
        runtime.int(runtime.as_integer(item)? + 1)
    })
}
extern "C" fn parallel_nested_map(environment: u64, arguments: u64) -> u64 {
    let prepared = guarded(|runtime| {
        let args = runtime.sequence(Handle(arguments))?;
        let items = runtime.allocate(Object::Array(vec![args[0]]))?;
        let callable = runtime.allocate(Object::Builtin("Parallel::map".into()))?;
        let arguments = runtime.allocate(Object::Tuple(vec![items, Handle(environment)]))?;
        Ok(Some((callable, arguments, *args.last().unwrap())))
    });
    let Some((callable, arguments, continuation)) = prepared else {
        return 0;
    };
    ril_rt_cps_call(callable.0, arguments.0, continuation.0)
}
#[test]
fn nested_parallel_groups_share_one_cpu_worker_without_blocking_their_children() {
    ril_rt_init();
    let executor = crate::scheduler::Executor::new(NonZeroUsize::new(1).unwrap()).unwrap();
    RUNTIME.with_borrow_mut(|runtime| runtime.executor = Some(executor.clone()));
    let (callable, arguments) = with_runtime(|runtime| {
        let environment = runtime.unit().unwrap();
        let leaf = runtime
            .allocate(Object::Closure {
                function: parallel_collecting_leaf as *const () as usize as u64,
                environment,
            })
            .unwrap();
        let nested = runtime
            .allocate(Object::CpsClosure {
                function: parallel_nested_map as *const () as usize as u64,
                environment: leaf,
            })
            .unwrap();
        let items = (0..96).map(|index| runtime.int(index).unwrap()).collect();
        let items = runtime.allocate(Object::Array(items)).unwrap();
        let callable = runtime
            .allocate(Object::Builtin("Parallel::map".into()))
            .unwrap();
        (
            callable,
            runtime
                .allocate(Object::Tuple(vec![items, nested]))
                .unwrap(),
        )
    });
    let end = ril_rt_cps_end();
    let initial = ril_rt_cps_call(callable.0, arguments.0, end);
    let runtime = RUNTIME.with_borrow_mut(std::mem::take);
    let cancellation = runtime.cancellation.clone();
    let (send, receive) = std::sync::mpsc::channel();
    let task = executor
        .spawn(async move {
            let NativeCompletion { mut runtime, value } =
                NativeComputation::new(runtime, initial).await;
            assert!(runtime.fault.is_none(), "{:?}", runtime.fault);
            let values = crate::shared::with_runtime(&mut runtime, |runtime| {
                runtime.root(9, Handle(value)).unwrap();
                runtime.statement_end();
                runtime.collect().unwrap();
                runtime
                    .sequence(Handle(value))
                    .unwrap()
                    .into_iter()
                    .map(|item| {
                        let leaf = runtime.sequence(item).unwrap();
                        runtime.as_integer(leaf[0]).unwrap()
                    })
                    .collect::<Vec<_>>()
            });
            send.send(values).unwrap();
        })
        .unwrap();
    let progress = receive.recv_timeout(std::time::Duration::from_secs(5));
    if progress.is_err() {
        cancellation.request();
    }
    assert_eq!(progress.unwrap(), (1..=96).collect::<Vec<i128>>());
    task.wait().unwrap();
    executor.shutdown_idle().unwrap();
}

#[test]
fn unhandled_fiber_yield_parks_immediately_and_roots_its_next_step() {
    ril_rt_init();
    let arguments = handle(|runtime| runtime.allocate(Object::Tuple(vec![])));
    let continuation = ril_rt_cps_end();
    let initial = ril_rt_cps_perform(u64::MAX, arguments, continuation);
    // No collector runs before the first poll installs the driver's root.
    // Clear fixture temporaries so they cannot hide a missing next-step root.
    ril_rt_statement_end();
    let runtime = RUNTIME.with_borrow_mut(std::mem::take);
    let mut computation = NativeComputation::new(runtime, initial);
    let mut context = std::task::Context::from_waker(std::task::Waker::noop());
    assert!(
        std::future::Future::poll(std::pin::Pin::new(&mut computation), &mut context).is_pending(),
        "Fiber::yield must park its logical task before running the continuation"
    );
    let runtime = computation.runtime.as_mut().unwrap();
    runtime.statement_end();
    assert!(runtime.collect().unwrap() > 0);
    let Poll::Ready(result) =
        std::future::Future::poll(std::pin::Pin::new(&mut computation), &mut context)
    else {
        panic!("the single yield must resume its saved continuation");
    };
    assert!(result.runtime.fault.is_none(), "{:?}", result.runtime.fault);
    assert!(matches!(
        result.runtime.heap.get(Handle(result.value)).unwrap(),
        Object::Unit
    ));
}

static TASK_LEAVES: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
extern "C" fn queued_task_leaf(_: u64, _: u64) -> u64 {
    handle(|runtime| {
        runtime.collect()?;
        TASK_LEAVES.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        runtime.unit()
    })
}
extern "C" fn fork_scope_children(environment: u64, arguments: u64) -> u64 {
    let prepared = guarded(|runtime| {
        let args = runtime.sequence(Handle(arguments))?;
        let environment = runtime.sequence(Handle(environment))?;
        let count = usize::try_from(runtime.as_integer(environment[1])?).unwrap();
        let fork = runtime.allocate(Object::Builtin("Concurrent::fork".into()))?;
        Ok(Some((
            args[0],
            *args.last().unwrap(),
            environment[0],
            count,
            fork,
        )))
    });
    let Some((scope, continuation, action, count, fork)) = prepared else {
        return 0;
    };
    for _ in 0..count {
        let arguments = handle(|runtime| runtime.allocate(Object::Tuple(vec![scope, action])));
        if arguments == 0 {
            return 0;
        }
        let next =
            concurrent::dispatch(fork, Handle(arguments), continuation, Handle::INVALID).unwrap();
        if next == 0 {
            return 0;
        }
    }
    let body = handle(|runtime| runtime.variant("Ok", vec![]));
    return_step(continuation, body)
}
extern "C" fn nested_task_scope(environment: u64, arguments: u64) -> u64 {
    let prepared = guarded(|runtime| {
        let args = runtime.sequence(Handle(arguments))?;
        let callable = runtime.allocate(Object::Builtin("Concurrent::scope".into()))?;
        let arguments = runtime.allocate(Object::Tuple(vec![Handle(environment)]))?;
        Ok(Some((callable, arguments, *args.last().unwrap())))
    });
    let Some((callable, arguments, continuation)) = prepared else {
        return 0;
    };
    ril_rt_cps_call(callable.0, arguments.0, continuation.0)
}
#[test]
fn structured_tasks_and_nested_scope_drains_share_one_cpu_worker() {
    ril_rt_init();
    TASK_LEAVES.store(0, std::sync::atomic::Ordering::Relaxed);
    let executor = crate::scheduler::Executor::new(NonZeroUsize::new(1).unwrap()).unwrap();
    RUNTIME.with_borrow_mut(|runtime| runtime.executor = Some(executor.clone()));
    let (callable, arguments) = with_runtime(|runtime| {
        let unit = runtime.unit().unwrap();
        let leaf = runtime
            .allocate(Object::Closure {
                function: queued_task_leaf as *const () as usize as u64,
                environment: unit,
            })
            .unwrap();
        let one = runtime.int(1).unwrap();
        let leaf_env = runtime.allocate(Object::Tuple(vec![leaf, one])).unwrap();
        let body = runtime
            .allocate(Object::CpsClosure {
                function: fork_scope_children as *const () as usize as u64,
                environment: leaf_env,
            })
            .unwrap();
        let nested = runtime
            .allocate(Object::CpsClosure {
                function: nested_task_scope as *const () as usize as u64,
                environment: body,
            })
            .unwrap();
        let count = runtime.int(64).unwrap();
        let outer_env = runtime
            .allocate(Object::Tuple(vec![nested, count]))
            .unwrap();
        let outer = runtime
            .allocate(Object::CpsClosure {
                function: fork_scope_children as *const () as usize as u64,
                environment: outer_env,
            })
            .unwrap();
        let callable = runtime
            .allocate(Object::Builtin("Concurrent::scope".into()))
            .unwrap();
        (
            callable,
            runtime.allocate(Object::Tuple(vec![outer])).unwrap(),
        )
    });
    let end = ril_rt_cps_end();
    let initial = ril_rt_cps_call(callable.0, arguments.0, end);
    let runtime = RUNTIME.with_borrow_mut(std::mem::take);
    let cancellation = runtime.cancellation.clone();
    let (send, receive) = std::sync::mpsc::channel();
    let task = executor.spawn(async move {
        let NativeCompletion { mut runtime, value } = NativeComputation::new(runtime, initial).await;
        assert!(runtime.fault.is_none(), "{:?}", runtime.fault);
        crate::shared::with_runtime(&mut runtime, |runtime| {
            runtime.root(9, Handle(value)).unwrap();
            runtime.statement_end();
            runtime.collect().unwrap();
            assert!(matches!(runtime.heap.get(Handle(value)).unwrap(), Object::Variant { tag, .. } if tag == "Ok"));
            assert!(runtime.concurrent_scopes.is_empty());
        });
        send.send(()).unwrap();
    }).unwrap();
    let progress = receive.recv_timeout(std::time::Duration::from_secs(5));
    if progress.is_err() {
        cancellation.request();
    }
    progress.unwrap();
    task.wait().unwrap();
    assert_eq!(TASK_LEAVES.load(std::sync::atomic::Ordering::Relaxed), 64);
    executor.shutdown_idle().unwrap();
}
