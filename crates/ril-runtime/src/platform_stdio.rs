//! Unbuffered byte streams. No Rust line buffering or console text transcoding
//! sits between a reported successful transfer and the host stream.
#![cfg_attr(windows, allow(unsafe_code))]
use std::io;

/// Concurrent standard streams may alias one host file description. Restore
/// flags only after the final request leaves, using a snapshot taken before
/// any stream in the batch was changed.
pub(crate) struct Mode;
impl Mode {
    pub(crate) fn nonblocking(stream: usize) -> io::Result<Self> {
        #[cfg(target_os = "linux")]
        modes::acquire(stream)?;
        #[cfg(not(target_os = "linux"))]
        let _ = stream;
        Ok(Self)
    }
}
impl Drop for Mode {
    fn drop(&mut self) {
        #[cfg(target_os = "linux")]
        modes::release();
    }
}
#[cfg(target_os = "linux")]
mod modes {
    use super::io;
    use rustix::{
        fd::BorrowedFd,
        fs::{OFlags, fcntl_getfl, fcntl_setfl},
    };
    use std::sync::Mutex;

    #[derive(Default)]
    struct Batch {
        active: usize,
        original: [Option<OFlags>; 3],
        changed: [bool; 3],
    }
    static MODES: Mutex<Batch> = Mutex::new(Batch {
        active: 0,
        original: [None; 3],
        changed: [false; 3],
    });
    fn fd(stream: usize) -> BorrowedFd<'static> {
        match stream {
            0 => rustix::stdio::stdin(),
            1 => rustix::stdio::stdout(),
            2 => rustix::stdio::stderr(),
            _ => unreachable!("standard stream identity"),
        }
    }
    pub(super) fn acquire(stream: usize) -> io::Result<()> {
        let mut batch = MODES.lock().unwrap_or_else(|error| error.into_inner());
        if batch.active == 0 {
            batch.original = std::array::from_fn(|stream| fcntl_getfl(fd(stream)).ok());
            batch.changed = [false; 3];
        }
        let flags = fcntl_getfl(fd(stream))?;
        if !flags.contains(OFlags::NONBLOCK) {
            fcntl_setfl(fd(stream), flags | OFlags::NONBLOCK)?;
            batch.changed[stream] = true;
        }
        batch.active += 1;
        Ok(())
    }
    pub(super) fn release() {
        let mut batch = MODES.lock().unwrap_or_else(|error| error.into_inner());
        batch.active -= 1;
        if batch.active == 0 {
            for stream in 0..3 {
                if batch.changed[stream]
                    && let Some(flags) = batch.original[stream]
                {
                    let _ = fcntl_setfl(fd(stream), flags);
                }
            }
        }
    }
}

pub(crate) fn write_all(data: &[u8], stderr: bool) -> io::Result<()> {
    let mut offset = 0;
    loop {
        match write(&data[offset..], stderr) {
            Ok(count) if offset + count == data.len() => return Ok(()),
            Ok(0) => return Err(io::Error::from(io::ErrorKind::WriteZero)),
            Ok(count) => offset += count,
            Err(error) if error.kind() == io::ErrorKind::Interrupted => {}
            Err(error) => return Err(error),
        }
    }
}

pub(crate) fn read(data: &mut [u8]) -> io::Result<usize> {
    #[cfg(target_os = "linux")]
    {
        rustix::io::read(rustix::stdio::stdin(), data).map_err(io::Error::from)
    }
    #[cfg(windows)]
    {
        windows::read(data)
    }
}

pub(crate) fn write(data: &[u8], stderr: bool) -> io::Result<usize> {
    #[cfg(target_os = "linux")]
    {
        let fd = if stderr {
            rustix::stdio::stderr()
        } else {
            rustix::stdio::stdout()
        };
        crate::platform_signal::write(|| rustix::io::write(fd, data).map_err(io::Error::from))
    }
    #[cfg(windows)]
    {
        windows::write(data, stderr)
    }
}

#[cfg(windows)]
mod windows {
    use super::io;
    use windows_sys::{
        Wdk::Foundation::{NtQueryObject, ObjectBasicInformation},
        Win32::{
            Foundation::{HANDLE, INVALID_HANDLE_VALUE, RtlNtStatusToDosError},
            Storage::FileSystem::{
                FILE_APPEND_DATA, FILE_READ_DATA, FILE_TYPE_PIPE, FILE_TYPE_UNKNOWN,
                FILE_WRITE_DATA, GetFileType, ReadFile, WriteFile,
            },
            System::{
                Console::{GetStdHandle, STD_ERROR_HANDLE, STD_INPUT_HANDLE, STD_OUTPUT_HANDLE},
                WindowsProgramming::PUBLIC_OBJECT_BASIC_INFORMATION,
            },
        },
    };

    fn stream(kind: u32, read: bool) -> io::Result<HANDLE> {
        // SAFETY: GetStdHandle has no pointer arguments; the returned borrowed
        // process handle is never closed or stored by this module.
        let handle = unsafe { GetStdHandle(kind) };
        if handle.is_null() || handle == INVALID_HANDLE_VALUE {
            return Err(io::Error::from_raw_os_error(6));
        }
        // SAFETY: GetFileType validates the borrowed handle. No ownership or
        // asynchronous access to any Rust allocation is transferred.
        if unsafe { GetFileType(handle) } == FILE_TYPE_UNKNOWN {
            return Err(io::Error::last_os_error());
        }
        // A zero-byte pipe read can wait, so validate access without issuing IO.
        // Query only the documented fixed-size public basic-information record:
        // https://learn.microsoft.com/windows/win32/api/winternl/nf-winternl-ntqueryobject
        let mut information = PUBLIC_OBJECT_BASIC_INFORMATION::default();
        // SAFETY: the output points to a live, correctly aligned POD record of
        // exactly the supplied size. The call completes before it is inspected.
        let status = unsafe {
            NtQueryObject(
                handle,
                ObjectBasicInformation,
                (&mut information as *mut PUBLIC_OBJECT_BASIC_INFORMATION).cast(),
                size_of::<PUBLIC_OBJECT_BASIC_INFORMATION>() as u32,
                std::ptr::null_mut(),
            )
        };
        if status < 0 {
            // SAFETY: conversion of a returned NTSTATUS has no pointer inputs.
            return Err(io::Error::from_raw_os_error(
                unsafe { RtlNtStatusToDosError(status) } as i32,
            ));
        }
        let access = if read {
            FILE_READ_DATA
        } else {
            FILE_WRITE_DATA | FILE_APPEND_DATA
        };
        if information.GrantedAccess & access == 0 {
            return Err(io::Error::from_raw_os_error(5));
        }
        Ok(handle)
    }

    pub(super) fn read(data: &mut [u8]) -> io::Result<usize> {
        let handle = stream(STD_INPUT_HANDLE, true)?;
        if data.is_empty() {
            return Ok(0);
        }
        let count = data.len().min(u32::MAX as usize) as u32;
        let mut transferred = 0;
        // SAFETY: the synchronous call writes at most count bytes within the
        // exclusive slice. Both output locations live until it completes.
        {
            let success = unsafe {
                ReadFile(
                    handle,
                    data.as_mut_ptr(),
                    count,
                    &mut transferred,
                    std::ptr::null_mut(),
                )
            };
            if success != 0 {
                // A zero-byte pipe message is not EOF. Ignore it and continue the
                // same positive request; a closed pipe reports ERROR_BROKEN_PIPE.
                // SAFETY: the already validated borrowed handle remains unchanged.
                if transferred == 0 && unsafe { GetFileType(handle) } == FILE_TYPE_PIPE {
                    return Err(io::Error::from(io::ErrorKind::Interrupted));
                }
                return Ok(transferred as usize);
            }
            let error = io::Error::last_os_error();
            // A closed pipe writer and a file read beyond EOF both mean stream EOF.
            // ERROR_MORE_DATA can accompany an already transferred message prefix.
            match error.raw_os_error() {
                Some(109 | 38) => Ok(0),
                Some(234) if transferred > 0 => Ok(transferred as usize),
                _ => Err(error),
            }
        }
    }

    pub(super) fn write(data: &[u8], stderr: bool) -> io::Result<usize> {
        let handle = stream(
            if stderr {
                STD_ERROR_HANDLE
            } else {
                STD_OUTPUT_HANDLE
            },
            false,
        )?;
        if data.is_empty() {
            return Ok(0);
        }
        let count = data.len().min(u32::MAX as usize) as u32;
        let mut transferred = 0;
        // SAFETY: the synchronous call reads at most count bytes within the
        // shared slice. The progress output remains live until completion.
        let success = unsafe {
            WriteFile(
                handle,
                data.as_ptr(),
                count,
                &mut transferred,
                std::ptr::null_mut(),
            )
        };
        if success != 0 {
            Ok(transferred as usize)
        } else {
            Err(io::Error::last_os_error())
        }
    }
}
