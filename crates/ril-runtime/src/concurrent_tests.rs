use super::*;
use crate::{
    heap::{HeapError, Object},
    shared::Worker,
    value::Runtime,
};

#[test]
fn task_outcomes_stay_rooted_after_the_producing_worker_retires() {
    let mut parent = Worker::new(Runtime::default());
    let (scope, task, scope_handle) = parent.with(|runtime| {
        let scope = Scope::new(&runtime.cancellation).unwrap();
        let action = runtime.unit().unwrap();
        let task = scope.reserve(action, TaskOwner::default()).unwrap();
        let scope_handle = runtime.allocate(Object::TaskScope(scope.clone())).unwrap();
        runtime.root(0, scope_handle).unwrap();
        (scope, task, scope_handle)
    });
    let mut child = parent.fork(&[scope_handle]).unwrap();
    let result = child.with(|runtime| {
        let value = runtime
            .allocate(Object::Record(Default::default()))
            .unwrap();
        runtime.set_field(value, "cycle".into(), value).unwrap();
        task.complete(Ok(value)).unwrap();
        runtime.statement_end();
        runtime.collect().unwrap();
        value
    });
    drop(child);
    parent.with(|runtime| {
        runtime.statement_end();
        for _ in 0..3 {
            runtime.collect().unwrap();
            assert_eq!(runtime.field(result, "cycle").unwrap(), result);
        }
        assert_eq!(
            runtime.heap.deep_clone(scope_handle),
            Err(HeapError::NonClonable)
        );
    });
    assert!(scope.finish(false).unwrap().is_none());
    assert_eq!(
        task.join(&Cancellation::default()).unwrap().unwrap(),
        result
    );
    assert_eq!(
        task.join(&Cancellation::default()).unwrap_err().tag,
        OutcomeTag::LanguagePanic
    );
}

#[test]
fn failure_is_permanent_and_ordering_uses_priority_then_creation_order() {
    let scope = Scope::new(&Arc::default()).unwrap();
    let first = scope
        .reserve(Handle::INVALID, TaskOwner::default())
        .unwrap();
    let second = scope
        .reserve(Handle::INVALID, TaskOwner::default())
        .unwrap();
    second.complete(Err(RuntimeError::panic("second"))).unwrap();
    first.complete(Err(RuntimeError::panic("first"))).unwrap();
    let fault = first.join(&Cancellation::default()).unwrap().unwrap_err();
    assert_eq!(fault.message, "first");
    assert!(scope.failed());
    assert_eq!(
        scope
            .reserve(Handle::INVALID, TaskOwner::default())
            .unwrap_err()
            .tag,
        OutcomeTag::Cancelled
    );
    assert_eq!(scope.finish(false).unwrap().unwrap().message, "first");
    let higher = RuntimeError::double_fault(
        RuntimeError::panic("primary"),
        RuntimeError::panic("cleanup"),
    );
    assert_eq!(
        choose_fault(Some(fault), Some(higher)).unwrap().tag,
        OutcomeTag::DoubleFault
    );
    assert_eq!(
        choose_fault(
            Some(RuntimeError::panic("body")),
            Some(RuntimeError::panic("child"))
        )
        .unwrap()
        .message,
        "body"
    );
}

#[test]
fn an_interrupted_join_does_not_observe_or_fabricate_a_task_result() {
    let scope = Scope::new(&Arc::default()).unwrap();
    let task = scope
        .reserve(Handle::INVALID, TaskOwner::default())
        .unwrap();
    let cancellation = Arc::new(Cancellation::default());
    let waiter = task.clone();
    let token = cancellation.clone();
    let (send, receive) = std::sync::mpsc::channel();
    let worker =
        std::thread::spawn(move || send.send(waiter.join(&token).unwrap_err().tag).unwrap());
    cancellation.request();
    assert_eq!(
        receive.recv_timeout(Duration::from_secs(3)).unwrap(),
        OutcomeTag::Cancelled
    );
    worker.join().unwrap();
    task.complete(Ok(Handle(17))).unwrap();
    assert_eq!(
        task.join(&Cancellation::default()).unwrap().unwrap(),
        Handle(17)
    );
    assert!(scope.finish(false).unwrap().is_none());
}
