use std::collections::{BTreeMap, BTreeSet, VecDeque};

use crate::Value;

pub(crate) type Task = u64;
#[cfg(not(miri))]
pub(crate) type Scope = u64;
pub(crate) type Channel = u64;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Event {
    Yield,
    Await(Task),
    Channel(Channel),
    Sleep(std::time::Instant),
    Change(Option<std::time::Instant>),
}

pub(crate) enum Completion {
    Finished(Value),
    Panicked(String),
    Cancelled,
}

pub(crate) enum Step {
    Suspended(Event),
    Complete(Completion),
}

pub(crate) trait FiberBackend {
    type Job;

    fn create(&mut self, task: Task, job: Self::Job) -> Result<(), String>;
    fn resume(&mut self, task: Task) -> Result<Step, String>;
}

#[derive(Default)]
pub(crate) struct Ready {
    queue: VecDeque<Task>,
    queued: BTreeSet<Task>,
    tasks: BTreeSet<Task>,
    parked: BTreeMap<Task, Event>,
    order: VecDeque<Task>,
}

impl Ready {
    pub(crate) fn add(&mut self, task: Task) {
        self.tasks.insert(task);
        self.wake(task);
    }

    pub(crate) fn wake(&mut self, task: Task) {
        self.parked.remove(&task);
        self.order.retain(|id| *id != task);
        if self.tasks.contains(&task) && self.queued.insert(task) {
            self.queue.push_back(task);
        }
    }

    pub(crate) fn next(&mut self) -> Option<Task> {
        let task = self.queue.pop_front()?;
        self.queued.remove(&task);
        Some(task)
    }

    pub(crate) fn suspend(&mut self, task: Task, event: Event) {
        if event == Event::Yield {
            self.wake(task);
        } else {
            self.parked.insert(task, event);
            self.order.push_back(task);
        }
    }

    pub(crate) fn signal(&mut self, accepts: impl Fn(Event) -> bool) {
        let tasks: Vec<_> = self
            .order
            .iter()
            .copied()
            .filter(|task| self.parked.get(task).is_some_and(|&event| accepts(event)))
            .collect();
        for task in tasks {
            self.wake(task);
        }
    }

    pub(crate) fn complete(&mut self, task: Task) {
        self.tasks.remove(&task);
        self.signal(|event| event == Event::Await(task) || matches!(event, Event::Change(_)));
    }

    pub(crate) fn active(&self) -> impl Iterator<Item = Task> + '_ {
        self.tasks.iter().copied()
    }

    pub(crate) fn nearest_timer(&self) -> Option<std::time::Instant> {
        self.parked
            .values()
            .filter_map(|event| match event {
                Event::Sleep(when) | Event::Change(Some(when)) => Some(*when),
                _ => None,
            })
            .min()
    }
}

#[cfg(not(miri))]
#[allow(
    unsafe_code,
    reason = "native stacks call generated functions and suspend across their C ABI"
)]
pub(crate) mod native;

#[cfg(test)]
mod thread;
