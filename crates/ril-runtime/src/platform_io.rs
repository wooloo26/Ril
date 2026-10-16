//! Cancellable process-pipe workers use nonblocking FDs on Linux and cancellation
//! of the owning synchronous IO thread on Windows. No descriptor is closed from
//! another thread and no canceled request is reported as successful progress.
#![cfg_attr(windows, allow(unsafe_code))]
pub(crate) trait Pipe: Send + 'static {
    fn prepare(&self) -> std::io::Result<()>;
}
macro_rules! pipe {
    ($($ty:ty),*) => { $(impl Pipe for $ty {
        fn prepare(&self) -> std::io::Result<()> {
            #[cfg(target_os = "linux")]
            {
                let flags = rustix::fs::fcntl_getfl(self)?;
                rustix::fs::fcntl_setfl(self, flags | rustix::fs::OFlags::NONBLOCK)?;
            }
            Ok(())
        }
    })* };
}
pipe!(
    std::process::ChildStdin,
    std::process::ChildStdout,
    std::process::ChildStderr
);

/// Only use while the file authority's mutex is held. All Ril aliases then see
/// one serialized transfer, and the original descriptor flags are restored.
pub(crate) struct FileMode<'a> {
    _file: &'a std::fs::File,
    #[cfg(target_os = "linux")]
    restore: Option<rustix::fs::OFlags>,
}
impl<'a> FileMode<'a> {
    pub(crate) fn nonblocking(file: &'a std::fs::File) -> std::io::Result<Self> {
        #[cfg(target_os = "linux")]
        {
            let flags = rustix::fs::fcntl_getfl(file)?;
            let restore = if flags.contains(rustix::fs::OFlags::NONBLOCK) {
                None
            } else {
                rustix::fs::fcntl_setfl(file, flags | rustix::fs::OFlags::NONBLOCK)?;
                Some(flags)
            };
            Ok(Self {
                _file: file,
                restore,
            })
        }
        #[cfg(not(target_os = "linux"))]
        {
            Ok(Self { _file: file })
        }
    }
}
impl Drop for FileMode<'_> {
    fn drop(&mut self) {
        #[cfg(target_os = "linux")]
        if let Some(flags) = self.restore {
            // The borrowed file stays owned and locked until this guard drops.
            // A host failure here must not erase already committed IO progress.
            let _ = rustix::fs::fcntl_setfl(self._file, flags);
        }
    }
}

pub(crate) fn cancel<T>(thread: &std::thread::JoinHandle<T>) {
    #[cfg(windows)]
    {
        use std::os::windows::io::AsRawHandle;
        // SAFETY: the live JoinHandle owns a Windows thread handle with the
        // required access. CancelSynchronousIo only requests cancellation; the
        // caller still joins and inspects completion before releasing the worker.
        // ERROR_NOT_FOUND is a normal race with an idle/finished worker. Repeated
        // requests close the check-to-ReadFile/WriteFile race after token cancel.
        unsafe {
            windows_sys::Win32::System::IO::CancelSynchronousIo(thread.as_raw_handle());
        }
    }
    #[cfg(not(windows))]
    let _ = thread;
}
