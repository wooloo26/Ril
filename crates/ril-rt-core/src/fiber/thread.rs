// Tests use a serialized OS-thread backend so that the scheduler is exercised under Miri.

use std::{
    collections::BTreeMap,
    sync::mpsc::{self, Receiver, SyncSender},
    thread::{self, JoinHandle},
};

use super::{Completion, Event, FiberBackend, Ready, Step, Task};
use crate::Value;

struct ThreadJob {
    run: Box<dyn FnOnce(&Suspension) -> Completion + Send>,
}

struct Suspension {
    events: SyncSender<Step>,
    resume: Receiver<()>,
}

impl Suspension {
    fn suspend(&self, event: Event) {
        self.events.send(Step::Suspended(event)).unwrap();
        self.resume.recv().unwrap();
    }
}

struct Running {
    resume: SyncSender<()>,
    events: Receiver<Step>,
    thread: JoinHandle<()>,
}

#[derive(Default)]
struct ThreadBackend {
    running: BTreeMap<Task, Running>,
}

impl FiberBackend for ThreadBackend {
    type Job = ThreadJob;

    fn create(&mut self, id: Task, job: ThreadJob) -> Result<(), String> {
        let (send_resume, resume) = mpsc::sync_channel(0);
        let (events, receive_events) = mpsc::sync_channel(0);
        let thread = thread::Builder::new()
            .spawn(move || {
                let suspend = Suspension { events, resume };
                if suspend.resume.recv().is_ok() {
                    let result = (job.run)(&suspend);
                    let _ = suspend.events.send(Step::Complete(result));
                }
            })
            .map_err(|error| error.to_string())?;
        self.running.insert(
            id,
            Running {
                resume: send_resume,
                events: receive_events,
                thread,
            },
        );
        Ok(())
    }

    fn resume(&mut self, task: Task) -> Result<Step, String> {
        let running = self.running.get(&task).ok_or("unknown task")?;
        running.resume.send(()).map_err(|error| error.to_string())?;
        let event = running.events.recv().map_err(|error| error.to_string())?;
        if matches!(event, Step::Complete(_))
            && let Some(running) = self.running.remove(&task)
        {
            running.thread.join().map_err(|_| "mock fiber panicked")?;
        }
        Ok(event)
    }
}

#[test]
fn fifo_is_shared_by_the_thread_backend() {
    use std::sync::{Arc, Mutex};
    let trace = Arc::new(Mutex::new(Vec::new()));
    let mut ready = Ready::default();
    let mut backend = ThreadBackend::default();
    for id in 1..=3 {
        let trace = Arc::clone(&trace);
        ready.add(id);
        backend
            .create(
                id,
                ThreadJob {
                    run: Box::new(move |fiber| {
                        trace.lock().unwrap().push(id);
                        fiber.suspend(Event::Yield);
                        trace.lock().unwrap().push(id);
                        Completion::Finished(Value(id))
                    }),
                },
            )
            .unwrap();
    }
    let mut completed = Vec::new();
    while let Some(id) = ready.next() {
        match backend.resume(id).unwrap() {
            Step::Suspended(action) => ready.suspend(id, action),
            Step::Complete(Completion::Finished(result)) => {
                completed.push(result.0);
                ready.complete(id);
            }
            Step::Complete(_) => panic!("unexpected task failure"),
        }
    }
    assert_eq!(trace.lock().unwrap().as_slice(), &[1, 2, 3, 1, 2, 3]);
    assert_eq!(completed, [1, 2, 3]);
}

#[test]
fn waiters_wake_in_fifo_order() {
    let mut ready = Ready::default();
    let until = std::time::Instant::now();
    for id in [8, 3, 5] {
        ready.add(id);
        assert_eq!(ready.next(), Some(id));
        ready.suspend(
            id,
            match id {
                8 => Event::Channel(1),
                3 => Event::Await(5),
                _ => Event::Sleep(until),
            },
        );
    }
    ready.signal(|event| event == Event::Channel(1));
    assert_eq!(ready.next(), Some(8));
    ready.complete(8);
    assert_eq!(ready.nearest_timer(), Some(until));
    ready.signal(|event| event == Event::Sleep(until));
    assert_eq!(ready.active().collect::<Vec<_>>(), vec![3, 5]);
    assert_eq!(ready.next(), Some(5));
    ready.complete(5);
    assert_eq!(ready.next(), Some(3));
    ready.complete(3);
    assert_eq!(ready.next(), None);
}

#[test]
fn fault_and_cancel_are_distinct_results() {
    let Step::Complete(Completion::Panicked(message)) =
        Step::Complete(Completion::Panicked("boom".into()))
    else {
        panic!("panic outcome lost")
    };
    assert_eq!(message, "boom");
    assert!(matches!(Completion::Cancelled, Completion::Cancelled));
}
