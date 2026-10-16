//! Minimal platform boundary for atomic no-replacement rename. Checking then
//! calling an overwriting rename would authorize an observable data-loss race.
#![allow(unsafe_code)]

#[cfg(target_os = "linux")]
#[path = "platform_file/wait_linux.rs"]
mod wait_linux;
#[cfg(target_os = "linux")]
pub(crate) use wait_linux::Wait;

#[cfg(windows)]
pub(crate) struct Wait;
#[cfg(windows)]
impl Wait {
    pub(crate) fn new() -> std::io::Result<Self> {
        Ok(Self)
    }
    pub(crate) fn run<T: Send + 'static>(
        self,
        cancellation: std::sync::Arc<crate::process_io::Cancellation>,
        operation: impl FnOnce() -> crate::value::Result<T> + Send + 'static,
    ) -> crate::value::Result<T> {
        crate::host_transfer::run(cancellation, operation)
    }
}

pub(crate) fn open(path: &std::path::Path, mode: &str) -> std::io::Result<std::fs::File> {
    let mode = mode.rsplit("::").next().unwrap_or(mode);
    #[cfg(target_os = "linux")]
    {
        use rustix::fs::{Mode, OFlags};
        let flags = match mode {
            "Read" => OFlags::RDONLY,
            "WriteNew" => OFlags::WRONLY | OFlags::CREATE | OFlags::EXCL,
            "WriteTruncate" => OFlags::WRONLY | OFlags::CREATE | OFlags::TRUNC,
            "ReadWrite" => OFlags::RDWR,
            "Append" => OFlags::WRONLY | OFlags::CREATE | OFlags::APPEND,
            _ => {
                return Err(std::io::Error::new(
                    std::io::ErrorKind::InvalidInput,
                    "unknown file mode",
                ));
            }
        };
        // rustix invokes one open/openat syscall without retrying EINTR. Keep
        // blocking-open semantics: O_NONBLOCK would change FIFO peer rendezvous.
        rustix::fs::open(path, flags | OFlags::CLOEXEC, Mode::from_raw_mode(0o666))
            .map(std::fs::File::from)
            .map_err(std::io::Error::from)
    }
    #[cfg(windows)]
    {
        let mut options = std::fs::OpenOptions::new();
        match mode {
            "Read" => {
                options.read(true);
            }
            "WriteNew" => {
                options.write(true).create_new(true);
            }
            "WriteTruncate" => {
                options.write(true).create(true).truncate(true);
            }
            "ReadWrite" => {
                options.read(true).write(true);
            }
            "Append" => {
                options.append(true).create(true);
            }
            _ => {
                return Err(std::io::Error::new(
                    std::io::ErrorKind::InvalidInput,
                    "unknown file mode",
                ));
            }
        }
        options.open(path)
    }
}

pub(crate) fn read(file: &std::fs::File, data: &mut [u8]) -> std::io::Result<usize> {
    #[cfg(target_os = "linux")]
    {
        rustix::io::read(file, data).map_err(std::io::Error::from)
    }
    #[cfg(windows)]
    {
        let mut file = file;
        std::io::Read::read(&mut file, data)
    }
}
pub(crate) fn write(file: &std::fs::File, data: &[u8]) -> std::io::Result<usize> {
    #[cfg(target_os = "linux")]
    {
        crate::platform_signal::write(|| {
            rustix::io::write(file, data).map_err(std::io::Error::from)
        })
    }
    #[cfg(windows)]
    {
        let mut file = file;
        std::io::Write::write(&mut file, data)
    }
}

pub(crate) fn close(file: std::fs::File) -> std::io::Result<()> {
    #[cfg(target_os = "linux")]
    {
        use std::os::fd::IntoRawFd;
        let fd = file.into_raw_fd();
        // SAFETY: ownership was consumed, so fd is valid and no File destructor
        // will close it again. Linux closes it even on error; never retry close.
        unsafe { rustix::io::try_close(fd) }.map_err(std::io::Error::from)
    }
    #[cfg(windows)]
    {
        use std::os::windows::io::IntoRawHandle;
        let handle = file.into_raw_handle();
        // SAFETY: the consumed File uniquely owns a valid OS file handle.
        let result = unsafe { windows_sys::Win32::Foundation::CloseHandle(handle) };
        if result == 0 {
            Err(std::io::Error::last_os_error())
        } else {
            Ok(())
        }
    }
}

pub(crate) fn rename(
    source: &std::path::Path,
    destination: &std::path::Path,
) -> std::io::Result<()> {
    #[cfg(target_os = "linux")]
    {
        rustix::fs::renameat_with(
            rustix::fs::CWD,
            source,
            rustix::fs::CWD,
            destination,
            rustix::fs::RenameFlags::NOREPLACE,
        )
        .map_err(std::io::Error::from)
    }
    #[cfg(windows)]
    {
        use std::os::windows::ffi::OsStrExt;
        let source: Vec<_> = source.as_os_str().encode_wide().chain([0]).collect();
        let destination: Vec<_> = destination.as_os_str().encode_wide().chain([0]).collect();
        // SAFETY: both buffers are alive, NUL-terminated UTF-16. Callers rejected
        // interior NUL. Zero flags prohibit replacement and cross-volume copy.
        let result = unsafe {
            windows_sys::Win32::Storage::FileSystem::MoveFileExW(
                source.as_ptr(),
                destination.as_ptr(),
                0,
            )
        };
        if result == 0 {
            Err(std::io::Error::last_os_error())
        } else {
            Ok(())
        }
    }
}
