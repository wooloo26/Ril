use super::*;
use crate::heap::Object;
#[test]
fn another_workers_precise_roots_keep_shared_cycles_alive_and_slots_observable() {
    let mut parent = Worker::new(Runtime::default());
    let cycle = parent.with(|runtime| {
        let value = runtime
            .allocate(Object::Record(Default::default()))
            .unwrap();
        runtime.set_field(value, "self".into(), value).unwrap();
        value
    });
    let mut child = parent.fork(&[cycle]).unwrap();
    parent.with(|runtime| {
        runtime.statement_end();
        runtime.collect().unwrap();
    });
    let replacement = child.with(|runtime| {
        assert_eq!(runtime.field(cycle, "self").unwrap(), cycle);
        let replacement = runtime.int(8).unwrap();
        runtime
            .set_field(cycle, "value".into(), replacement)
            .unwrap();
        replacement
    });
    parent.with(|runtime| {
        runtime.collect().unwrap();
        assert_eq!(runtime.field(cycle, "value").unwrap(), replacement);
        runtime.root(0, cycle).unwrap();
    });
    drop(child);
    parent.with(|runtime| {
        runtime.collect().unwrap();
        assert_eq!(runtime.field(cycle, "self").unwrap(), cycle);
    });
}
#[test]
fn multiple_native_threads_allocate_and_collect_at_shared_heap_safepoints() {
    let mut parent = Worker::new(Runtime::default());
    let shared = parent.with(|runtime| {
        runtime
            .allocate(Object::Record(Default::default()))
            .unwrap()
    });
    let children: Vec<_> = (0..4)
        .map(|index| {
            let mut child = parent.fork(&[shared]).unwrap();
            std::thread::spawn(move || {
                for iteration in 0..200 {
                    child.with(|runtime| {
                        let value = runtime.int(iteration).unwrap();
                        runtime.set_field(shared, index.to_string(), value).unwrap();
                        runtime.statement_end();
                        runtime.collect().unwrap();
                    });
                }
            })
        })
        .collect();
    parent.with(|runtime| {
        runtime.root(0, shared).unwrap();
        runtime.statement_end();
    });
    for child in children {
        child.join().unwrap();
    }
    parent.with(|runtime| {
        runtime.collect().unwrap();
        for index in 0..4 {
            let value = runtime.field(shared, &index.to_string()).unwrap();
            assert_eq!(runtime.as_integer(value).unwrap(), 199);
        }
    });
}
#[test]
fn unwinding_restores_the_heap_gate_without_poisoning_or_losing_existing_roots() {
    let mut parent = Worker::new(Runtime::default());
    let value = parent.with(|runtime| {
        let value = runtime.int(7).unwrap();
        runtime.root(0, value).unwrap();
        value
    });
    let outcome = catch_unwind(AssertUnwindSafe(|| {
        parent.with(|runtime| {
            runtime.int(8).unwrap();
            panic!("unexpected host failure")
        })
    }));
    assert!(outcome.is_err());
    parent.with(|runtime| {
        runtime.collect().unwrap();
        assert_eq!(runtime.as_integer(value).unwrap(), 7);
    });
}
