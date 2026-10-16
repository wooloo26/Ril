//! A joinable filesystem worker owns a temporary, non-restarting wake signal.
//! The handler performs no work. Only direct syscalls that return EINTR can use
//! this to stop a wait; callers must check cancellation before retrying them.
#![allow(unsafe_code)]

use crate::{
    process_io::Cancellation,
    value::{Result, RuntimeError},
};
use std::{
    io,
    mem::MaybeUninit,
    os::unix::thread::JoinHandleExt,
    sync::{Arc, Mutex},
    thread,
    time::Duration,
};

struct Registration {
    signal: i32,
    previous: libc::sigaction,
    users: usize,
}
static REGISTRATION: Mutex<Option<Registration>> = Mutex::new(None);

extern "C" fn wake(_: i32) {}

/// The process disposition stays installed until all workers have been joined.
/// A directed signal cannot remain queued on another thread after that join.
pub(crate) struct Wait {
    signal: i32,
}
impl Wait {
    pub(crate) fn new() -> io::Result<Self> {
        let mut registration = REGISTRATION
            .lock()
            .unwrap_or_else(|error| error.into_inner());
        if let Some(current) = registration.as_mut() {
            current.users = current
                .users
                .checked_add(1)
                .ok_or_else(|| io::Error::other("too many filesystem waiters"))?;
            return Ok(Self {
                signal: current.signal,
            });
        }
        for signal in (libc::SIGRTMIN()..=libc::SIGRTMAX()).rev() {
            let mut previous = MaybeUninit::<libc::sigaction>::uninit();
            // SAFETY: signal is in libc's usable realtime range, excluding its
            // internal threading signals. previous is a live output record.
            if unsafe { libc::sigaction(signal, std::ptr::null(), previous.as_mut_ptr()) } != 0 {
                return Err(io::Error::last_os_error());
            }
            // SAFETY: the successful query initialized the entire record.
            let previous = unsafe { previous.assume_init() };
            if previous.sa_sigaction != libc::SIG_DFL {
                continue;
            }
            // SAFETY: zero initializes this Linux C record; sigemptyset then
            // initializes its signal mask. No SA_RESTART flag is installed.
            let mut action: libc::sigaction = unsafe { std::mem::zeroed() };
            action.sa_sigaction = wake as *const () as usize;
            action.sa_flags = 0;
            if unsafe { libc::sigemptyset(&mut action.sa_mask) } != 0 {
                return Err(io::Error::last_os_error());
            }
            // SAFETY: both initialized action records remain live. A runtime
            // lease serializes our disposition changes; other installed host
            // handlers are never deliberately replaced.
            if unsafe { libc::sigaction(signal, &action, std::ptr::null_mut()) } != 0 {
                return Err(io::Error::last_os_error());
            }
            *registration = Some(Registration {
                signal,
                previous,
                users: 1,
            });
            return Ok(Self { signal });
        }
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "no unclaimed realtime signal for filesystem cancellation",
        ))
    }

    pub(crate) fn run<T: Send + 'static>(
        self,
        cancellation: Arc<Cancellation>,
        operation: impl FnOnce() -> Result<T> + Send + 'static,
    ) -> Result<T> {
        let signal = self.signal;
        let _lease = self;
        if cancellation.requested() {
            return Err(RuntimeError::cancelled());
        }
        let worker = thread::Builder::new()
            .name("ril-filesystem".into())
            .spawn(move || {
                let _mask = WakeMask::new(signal)?;
                operation()
            })
            .map_err(|error| {
                RuntimeError::internal(format!("cannot start filesystem worker: {error}"))
            })?;
        let mut wake_error = None;
        while !worker.is_finished() {
            if cancellation.requested() {
                // SAFETY: a joinable thread's ID remains valid until join. The
                // worker unblocks this signal, whose no-op handler stays leased
                // until after join. Repetition covers cancellation just before
                // the blocking syscall begins. No thread is detached or killed.
                let error = unsafe { libc::pthread_kill(worker.as_pthread_t(), signal) };
                if error != 0 && error != libc::ESRCH {
                    wake_error = Some(RuntimeError::internal(format!(
                        "cannot wake filesystem worker: {}",
                        io::Error::from_raw_os_error(error)
                    )));
                }
            }
            thread::sleep(Duration::from_millis(1));
        }
        let result = worker
            .join()
            .map_err(|_| RuntimeError::internal("unexpected Rust panic in filesystem worker"))?;
        if matches!(&result, Err(error) if error.tag == ril_runtime_api::abi::OutcomeTag::InternalFault)
        {
            result
        } else if let Some(error) = wake_error {
            Err(error)
        } else if cancellation.requested() {
            Err(RuntimeError::cancelled())
        } else {
            result
        }
    }
}
impl Drop for Wait {
    fn drop(&mut self) {
        let mut registration = REGISTRATION
            .lock()
            .unwrap_or_else(|error| error.into_inner());
        let current = registration.as_mut().expect("live filesystem signal lease");
        assert_eq!(current.signal, self.signal);
        current.users -= 1;
        if current.users == 0 {
            // SAFETY: all workers using this disposition have been joined. The
            // original action came from a successful query for the same signal.
            let result =
                unsafe { libc::sigaction(current.signal, &current.previous, std::ptr::null_mut()) };
            assert_eq!(result, 0, "restoring filesystem wake signal disposition");
            *registration = None;
        }
    }
}

struct WakeMask(libc::sigset_t);
impl WakeMask {
    fn new(signal: i32) -> Result<Self> {
        let mut selected = MaybeUninit::<libc::sigset_t>::uninit();
        let mut previous = MaybeUninit::<libc::sigset_t>::uninit();
        // SAFETY: sigemptyset initializes selected; sigaddset uses a valid
        // realtime signal. pthread_sigmask initializes previous on success.
        let error = unsafe {
            if libc::sigemptyset(selected.as_mut_ptr()) != 0
                || libc::sigaddset(selected.as_mut_ptr(), signal) != 0
            {
                return Err(RuntimeError::internal(
                    "cannot initialize filesystem wake mask",
                ));
            }
            libc::pthread_sigmask(libc::SIG_UNBLOCK, selected.as_ptr(), previous.as_mut_ptr())
        };
        if error != 0 {
            return Err(RuntimeError::internal(format!(
                "cannot unblock filesystem wake signal: {}",
                io::Error::from_raw_os_error(error)
            )));
        }
        // SAFETY: the successful mask change initialized previous.
        Ok(Self(unsafe { previous.assume_init() }))
    }
}
impl Drop for WakeMask {
    fn drop(&mut self) {
        // SAFETY: this initialized mask belongs to the current worker. The
        // handler is still installed until the owner observes exit and joins.
        let result =
            unsafe { libc::pthread_sigmask(libc::SIG_SETMASK, &self.0, std::ptr::null_mut()) };
        assert_eq!(result, 0, "restoring filesystem worker signal mask");
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn action(signal: i32) -> libc::sigaction {
        let mut value = MaybeUninit::uninit();
        // SAFETY: this valid signal is queried into live output storage.
        assert_eq!(
            unsafe { libc::sigaction(signal, std::ptr::null(), value.as_mut_ptr()) },
            0
        );
        // SAFETY: the successful query initialized the record.
        unsafe { value.assume_init() }
    }
    fn fixture() {
        let occupied = libc::SIGRTMAX();
        let original = action(occupied);
        let mut ignored = original;
        ignored.sa_sigaction = libc::SIG_IGN;
        // SAFETY: only this isolated fixture owns its signal dispositions.
        assert_eq!(
            unsafe { libc::sigaction(occupied, &ignored, std::ptr::null_mut()) },
            0
        );
        let first = Wait::new().unwrap();
        assert_ne!(first.signal, occupied);
        let signal = first.signal;
        let second = Wait::new().unwrap();
        assert_eq!(second.signal, signal);
        let installed = action(signal);
        assert_eq!(installed.sa_sigaction, wake as *const () as usize);
        assert_eq!(installed.sa_flags & libc::SA_RESTART, 0);
        drop(first);
        assert_eq!(action(signal).sa_sigaction, wake as *const () as usize);
        // Block the signal in the creator. The worker must actively unblock it
        // without modifying the creator's mask, and restoration waits for join.
        let mut blocked: libc::sigset_t = unsafe { std::mem::zeroed() };
        let mut previous = MaybeUninit::uninit();
        // SAFETY: valid masks and signal; previous is live output storage.
        unsafe {
            assert_eq!(libc::sigemptyset(&mut blocked), 0);
            assert_eq!(libc::sigaddset(&mut blocked, signal), 0);
            assert_eq!(
                libc::pthread_sigmask(libc::SIG_BLOCK, &blocked, previous.as_mut_ptr()),
                0
            );
        }
        second
            .run(Arc::default(), move || {
                let mut current = MaybeUninit::uninit();
                // SAFETY: null input queries this worker's current initialized mask.
                unsafe {
                    assert_eq!(
                        libc::pthread_sigmask(
                            libc::SIG_SETMASK,
                            std::ptr::null(),
                            current.as_mut_ptr()
                        ),
                        0
                    );
                    assert_eq!(libc::sigismember(&current.assume_init(), signal), 0);
                }
                Ok(())
            })
            .unwrap();
        assert_eq!(action(signal).sa_sigaction, libc::SIG_DFL);
        assert_eq!(action(occupied).sa_sigaction, libc::SIG_IGN);
        // SAFETY: restore this fixture's initialized mask and original action.
        unsafe {
            assert_eq!(
                libc::pthread_sigmask(libc::SIG_SETMASK, previous.as_ptr(), std::ptr::null_mut()),
                0
            );
            assert_eq!(
                libc::sigaction(occupied, &original, std::ptr::null_mut()),
                0
            );
        }
        let cancellation = Arc::new(Cancellation::default());
        let token = cancellation.clone();
        let wait = Wait::new().unwrap();
        let panic_signal = wait.signal;
        let error = wait
            .run::<()>(cancellation, move || {
                token.request();
                panic!("host worker panic")
            })
            .unwrap_err();
        assert_eq!(error.tag, ril_runtime_api::abi::OutcomeTag::InternalFault);
        assert_eq!(action(panic_signal).sa_sigaction, libc::SIG_DFL);
    }
    #[test]
    fn signal_leases_preserve_other_handlers_masks_and_internal_faults() {
        const FIXTURE: &str = "RIL_FILESYSTEM_SIGNAL_FIXTURE";
        if std::env::var_os(FIXTURE).is_some() {
            fixture();
            return;
        }
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact", "platform_file::wait_linux::tests::signal_leases_preserve_other_handlers_masks_and_internal_faults", "--nocapture"])
            .env(FIXTURE, "1").output().unwrap();
        assert!(
            output.status.success(),
            "{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
}
