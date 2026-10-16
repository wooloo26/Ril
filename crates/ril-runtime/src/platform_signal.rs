//! Turn this thread's pipe-write SIGPIPE into a normal BrokenPipe IO result.
//! The embedding process's disposition and pre-existing pending signals survive.
#![allow(unsafe_code)]
use std::io;

struct Mask {
    old: Option<libc::sigset_t>,
    pipe: libc::sigset_t,
    already_pending: bool,
}
impl Mask {
    fn block() -> io::Result<Self> {
        let mut pipe = std::mem::MaybeUninit::<libc::sigset_t>::uninit();
        let mut old = std::mem::MaybeUninit::<libc::sigset_t>::uninit();
        let mut pending = std::mem::MaybeUninit::<libc::sigset_t>::uninit();
        // SAFETY: each output points to correctly sized, aligned storage. Only
        // SIGPIPE is added; libc's reserved signals are never masked. The old
        // mask is initialized exactly when pthread_sigmask reports success.
        unsafe {
            if libc::sigemptyset(pipe.as_mut_ptr()) != 0
                || libc::sigaddset(pipe.as_mut_ptr(), libc::SIGPIPE) != 0
            {
                return Err(io::Error::last_os_error());
            }
            let pipe = pipe.assume_init();
            let error = libc::pthread_sigmask(libc::SIG_BLOCK, &pipe, old.as_mut_ptr());
            if error != 0 {
                return Err(io::Error::from_raw_os_error(error));
            }
            let mut mask = Self {
                old: Some(old.assume_init()),
                pipe,
                already_pending: true,
            };
            if libc::sigpending(pending.as_mut_ptr()) != 0 {
                return Err(io::Error::last_os_error());
            }
            mask.already_pending = libc::sigismember(&pending.assume_init(), libc::SIGPIPE) == 1;
            Ok(mask)
        }
    }
    fn consume_new_pipe(&self) {
        if self.already_pending {
            return;
        }
        let timeout = libc::timespec {
            tv_sec: 0,
            tv_nsec: 0,
        };
        // SAFETY: this thread blocks SIGPIPE throughout the wait; the set holds
        // only SIGPIPE, and both input records remain live. Zero timeout never
        // waits for a later signal. A signal that was pending on entry is kept.
        loop {
            let signal = unsafe { libc::sigtimedwait(&self.pipe, std::ptr::null_mut(), &timeout) };
            if signal >= 0 || io::Error::last_os_error().kind() != io::ErrorKind::Interrupted {
                break;
            }
        }
    }
    fn restore(&mut self) -> io::Result<()> {
        if let Some(old) = self.old.take() {
            // SAFETY: old is the initialized mask obtained from this thread.
            let error =
                unsafe { libc::pthread_sigmask(libc::SIG_SETMASK, &old, std::ptr::null_mut()) };
            if error != 0 {
                return Err(io::Error::from_raw_os_error(error));
            }
        }
        Ok(())
    }
}
impl Drop for Mask {
    fn drop(&mut self) {
        let _ = self.restore();
    }
}
pub(crate) fn write<T>(operation: impl FnOnce() -> io::Result<T>) -> io::Result<T> {
    let mut mask = Mask::block()?;
    let result = operation();
    if result
        .as_ref()
        .is_err_and(|error| error.raw_os_error() == Some(libc::EPIPE))
    {
        mask.consume_new_pipe();
    }
    // Failure with this initialized mask and constant SIG_SETMASK is a runtime
    // invariant failure. Do not turn a committed prefix into an IO Err with no
    // progress. ABI/worker containment classifies this as InternalFault.
    mask.restore()
        .expect("restoring the same thread's valid signal mask");
    result
}
