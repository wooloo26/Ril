//! One host timer service wakes logical tasks without occupying CPU workers.
use crate::{
    process_io::{Cancellation, CancellationWake},
    value::{Result, RuntimeError},
};
use std::{
    collections::BTreeMap,
    future::Future,
    pin::Pin,
    sync::{Arc, Condvar, Mutex, OnceLock, Weak},
    task::{Context, Poll, Waker},
    time::{Duration, Instant},
};

struct AlarmState {
    ready: bool,
    waiter: Option<Waker>,
}
struct Alarm {
    state: Mutex<AlarmState>,
}
struct Pending {
    next: u64,
    alarms: BTreeMap<(Instant, u64), Weak<Alarm>>,
}
struct Service {
    pending: Mutex<Pending>,
    wake: Condvar,
}
struct Registration {
    service: Arc<Service>,
    key: (Instant, u64),
}
impl Drop for Registration {
    fn drop(&mut self) {
        self.service
            .pending
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .alarms
            .remove(&self.key);
        self.service.wake.notify_one();
    }
}

fn service() -> Result<Arc<Service>> {
    static SERVICE: OnceLock<std::result::Result<Arc<Service>, String>> = OnceLock::new();
    SERVICE
        .get_or_init(|| {
            let service = Arc::new(Service {
                pending: Mutex::new(Pending {
                    next: 0,
                    alarms: BTreeMap::new(),
                }),
                wake: Condvar::new(),
            });
            let worker = service.clone();
            std::thread::Builder::new()
                .name("ril-timer".into())
                .spawn(move || run(worker))
                .map(|_| service)
                .map_err(|error| error.to_string())
        })
        .clone()
        .map_err(|error| RuntimeError::internal(format!("timer service unavailable: {error}")))
}
fn run(service: Arc<Service>) {
    loop {
        let due = {
            let mut pending = service.pending.lock().unwrap_or_else(|e| e.into_inner());
            loop {
                let Some((&(deadline, _), _)) = pending.alarms.first_key_value() else {
                    pending = service
                        .wake
                        .wait(pending)
                        .unwrap_or_else(|e| e.into_inner());
                    continue;
                };
                let now = Instant::now();
                if deadline > now {
                    (pending, _) = service
                        .wake
                        .wait_timeout(pending, deadline.duration_since(now))
                        .unwrap_or_else(|e| e.into_inner());
                    continue;
                }
                break pending.alarms.pop_first().map(|(_, alarm)| alarm);
            }
        };
        if let Some(alarm) = due.and_then(|alarm| alarm.upgrade()) {
            let waiter = {
                let mut state = alarm.state.lock().unwrap_or_else(|e| e.into_inner());
                state.ready = true;
                state.waiter.take()
            };
            if let Some(waiter) = waiter {
                waiter.wake();
            }
        }
    }
}

pub(crate) struct Sleep {
    deadline: Instant,
    cancellation: Arc<Cancellation>,
    cancel_wake: Option<CancellationWake>,
    alarm: Arc<Alarm>,
    registration: Option<Registration>,
}
impl Sleep {
    pub(crate) fn new(duration: Duration, cancellation: Arc<Cancellation>) -> Result<Self> {
        let deadline = Instant::now()
            .checked_add(duration)
            .ok_or_else(|| RuntimeError::panic("sleep duration exceeds the host clock range"))?;
        Ok(Self {
            deadline,
            cancellation,
            cancel_wake: None,
            alarm: Arc::new(Alarm {
                state: Mutex::new(AlarmState {
                    ready: false,
                    waiter: None,
                }),
            }),
            registration: None,
        })
    }
    fn finish(&mut self) {
        self.alarm
            .state
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .waiter = None;
        self.registration = None;
        self.cancel_wake = None;
    }
}
impl Drop for Sleep {
    fn drop(&mut self) {
        self.finish();
    }
}
impl Future for Sleep {
    type Output = Result<()>;
    fn poll(self: Pin<&mut Self>, context: &mut Context<'_>) -> Poll<Self::Output> {
        let this = self.get_mut();
        if this.cancellation.requested() {
            this.finish();
            return Poll::Ready(Err(RuntimeError::cancelled()));
        }
        if Instant::now() >= this.deadline {
            this.finish();
            return Poll::Ready(Ok(()));
        }
        if let Some(wake) = &mut this.cancel_wake {
            wake.refresh(context.waker());
        } else {
            match this.cancellation.subscribe(context.waker()) {
                Ok(wake) => this.cancel_wake = Some(wake),
                Err(error) => return Poll::Ready(Err(RuntimeError::internal(error.to_string()))),
            }
        }
        let mut state = this.alarm.state.lock().unwrap_or_else(|e| e.into_inner());
        if state.ready || this.cancellation.requested() {
            drop(state);
            let cancelled = this.cancellation.requested();
            this.finish();
            return Poll::Ready(if cancelled {
                Err(RuntimeError::cancelled())
            } else {
                Ok(())
            });
        }
        state.waiter = Some(context.waker().clone());
        drop(state);
        if this.registration.is_none() {
            let service = match service() {
                Ok(service) => service,
                Err(error) => return Poll::Ready(Err(error)),
            };
            let mut pending = service.pending.lock().unwrap_or_else(|e| e.into_inner());
            let Some(id) = pending.next.checked_add(1) else {
                return Poll::Ready(Err(RuntimeError::internal("timer identity exhausted")));
            };
            pending.next = id;
            let key = (this.deadline, id);
            pending.alarms.insert(key, Arc::downgrade(&this.alarm));
            drop(pending);
            service.wake.notify_one();
            this.registration = Some(Registration { service, key });
        }
        Poll::Pending
    }
}

#[cfg(test)]
mod tests;
