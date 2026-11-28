//! Single-threaded nonblocking TCP + monotonic timer reactor for `ril/async`.
//!
//! All handles are owned by the single `Runtime` thread; no locks or background
//! threads are required. On Unix targets, readiness waiting uses POSIX `poll(2)`.

use std::{
    collections::BTreeMap,
    io::{ErrorKind, Read as _, Write as _},
    net::{TcpListener, TcpStream},
    time::{Duration, Instant},
};

use num_traits::ToPrimitive as _;

use crate::{Object, RilStr, Runtime, Value};

#[derive(Default)]
pub(crate) struct State {
    origin: Option<Instant>,
    next_handle: i64,
    listeners: BTreeMap<i64, TcpListener>,
    streams: BTreeMap<i64, TcpStream>,
}

impl State {
    fn alloc_handle(&mut self) -> i64 {
        self.next_handle += 1;
        self.next_handle
    }

    pub(crate) fn now_ms(&mut self) -> i64 {
        let origin = *self.origin.get_or_insert_with(Instant::now);
        i64::try_from(origin.elapsed().as_millis()).unwrap_or(i64::MAX)
    }

    pub(crate) fn close_nowait(&mut self, handle: i64) {
        let _ = self.listeners.remove(&handle);
        let _ = self.streams.remove(&handle);
    }
}

#[cfg(all(unix, not(miri)))]
#[allow(
    unsafe_code,
    reason = "POSIX poll(2) FFI for single-threaded nonblocking readiness multiplexing"
)]
mod sys_poll {
    use std::os::fd::RawFd;

    pub(super) const POLLIN: i16 = 0x0001;
    pub(super) const POLLOUT: i16 = 0x0004;
    pub(super) const POLLERR: i16 = 0x0008;
    pub(super) const POLLHUP: i16 = 0x0010;
    pub(super) const POLLNVAL: i16 = 0x0020;

    #[repr(C)]
    #[derive(Clone, Copy)]
    pub(super) struct PollFd {
        pub(super) fd: RawFd,
        pub(super) events: i16,
        pub(super) revents: i16,
    }

    unsafe extern "C" {
        fn poll(fds: *mut PollFd, nfds: usize, timeout: i32) -> i32;
    }

    pub(super) fn wait(fds: &mut [PollFd], timeout_ms: i32) -> i32 {
        // SAFETY: `fds` is a valid mutable slice of `PollFd` with length `fds.len()`.
        unsafe { poll(fds.as_mut_ptr(), fds.len(), timeout_ms) }
    }
}

fn ok_val(rt: &mut Runtime, payload: Value) -> Value {
    rt.gc.pin(payload);
    let out = rt.gc.alloc(Object::Tag("Ok".into(), vec![payload]));
    rt.gc.unpin(payload);
    out
}

fn err_str(rt: &mut Runtime, msg: impl Into<String>) -> Value {
    let text = rt.gc.alloc(Object::Str(RilStr::new(msg.into())));
    rt.gc.pin(text);
    let out = rt.gc.alloc(Object::Tag("Err".into(), vec![text]));
    rt.gc.unpin(text);
    out
}

fn read_str(rt: &Runtime, value: Value) -> Result<String, &'static str> {
    match rt.gc.object(value) {
        Some(Object::Str(s)) => Ok(s.as_str().to_owned()),
        _ => Err("expected str"),
    }
}

pub(crate) fn now_ms(rt: &mut Runtime) -> Value {
    let ms = rt.reactor.now_ms();
    rt.gc.int_i64(ms)
}

pub(crate) fn tcp_listen(rt: &mut Runtime, addr: Value) -> Value {
    let addr = match read_str(rt, addr) {
        Ok(s) => s,
        Err(msg) => return err_str(rt, msg),
    };
    let listener = match TcpListener::bind(&addr) {
        Ok(l) => l,
        Err(err) => return err_str(rt, err.to_string()),
    };
    if let Err(err) = listener.set_nonblocking(true) {
        return err_str(rt, err.to_string());
    }
    let port = match listener.local_addr() {
        Ok(sa) => i64::from(sa.port()),
        Err(err) => return err_str(rt, err.to_string()),
    };
    let handle = rt.reactor.alloc_handle();
    rt.reactor.listeners.insert(handle, listener);
    let h_val = rt.gc.int_i64(handle);
    let p_val = rt.gc.int_i64(port);
    let pair = rt.gc.alloc(Object::Tuple(vec![h_val, p_val]));
    ok_val(rt, pair)
}

pub(crate) fn tcp_connect(rt: &mut Runtime, addr: Value) -> Value {
    let addr = match read_str(rt, addr) {
        Ok(s) => s,
        Err(msg) => return err_str(rt, msg),
    };
    let stream = match TcpStream::connect(&addr) {
        Ok(s) => s,
        Err(err) => return err_str(rt, err.to_string()),
    };
    if let Err(err) = stream.set_nonblocking(true) {
        return err_str(rt, err.to_string());
    }
    let handle = rt.reactor.alloc_handle();
    rt.reactor.streams.insert(handle, stream);
    let h_val = rt.gc.int_i64(handle);
    ok_val(rt, h_val)
}

pub(crate) fn tcp_try_accept(rt: &mut Runtime, listener_id: Value) -> Value {
    let Some(handle) = rt.gc.integer(listener_id).and_then(|n| n.to_i64()) else {
        return err_str(rt, "invalid listener handle");
    };
    let Some(listener) = rt.reactor.listeners.get(&handle) else {
        return err_str(rt, "tcp listener is closed");
    };
    match listener.accept() {
        Ok((stream, _)) => {
            if let Err(err) = stream.set_nonblocking(true) {
                return err_str(rt, err.to_string());
            }
            let stream_id = rt.reactor.alloc_handle();
            rt.reactor.streams.insert(stream_id, stream);
            let s_val = rt.gc.int_i64(stream_id);
            ok_val(rt, s_val)
        }
        Err(err) if err.kind() == ErrorKind::WouldBlock => {
            let zero = rt.gc.int_i64(0);
            ok_val(rt, zero)
        }
        Err(err) => err_str(rt, err.to_string()),
    }
}

pub(crate) fn tcp_try_read(rt: &mut Runtime, stream_id: Value, max_bytes: Value) -> Value {
    let Some(handle) = rt.gc.integer(stream_id).and_then(|n| n.to_i64()) else {
        return err_str(rt, "invalid stream handle");
    };
    let Some(max_len) = rt.gc.integer(max_bytes).and_then(|n| n.to_usize()) else {
        return err_str(rt, "invalid read length");
    };
    let cap = max_len.min(1024 * 1024);
    let Some(stream) = rt.reactor.streams.get_mut(&handle) else {
        return err_str(rt, "tcp stream is closed");
    };
    let mut buf = vec![0u8; cap];
    match stream.read(&mut buf) {
        Ok(n) => {
            buf.truncate(n);
            let bytes = rt.gc.alloc(Object::Bytes(buf));
            rt.gc.pin(bytes);
            let some = rt.gc.alloc(Object::Tag("Some".into(), vec![bytes]));
            rt.gc.unpin(bytes);
            ok_val(rt, some)
        }
        Err(err) if err.kind() == ErrorKind::WouldBlock => {
            let none = rt.gc.alloc(Object::Tag("None".into(), Vec::new()));
            ok_val(rt, none)
        }
        Err(err) => err_str(rt, err.to_string()),
    }
}

pub(crate) fn tcp_try_write(rt: &mut Runtime, stream_id: Value, data: Value) -> Value {
    let Some(handle) = rt.gc.integer(stream_id).and_then(|n| n.to_i64()) else {
        return err_str(rt, "invalid stream handle");
    };
    let bytes = match rt.gc.object(data) {
        Some(Object::Bytes(b)) => b.clone(),
        _ => return err_str(rt, "expected bytes"),
    };
    let Some(stream) = rt.reactor.streams.get_mut(&handle) else {
        return err_str(rt, "tcp stream is closed");
    };
    match stream.write(&bytes) {
        Ok(n) => {
            let written = i64::try_from(n).unwrap_or(i64::MAX);
            let val = rt.gc.int_i64(written);
            ok_val(rt, val)
        }
        Err(err) if err.kind() == ErrorKind::WouldBlock => {
            let neg = rt.gc.int_i64(-1);
            ok_val(rt, neg)
        }
        Err(err) => err_str(rt, err.to_string()),
    }
}

pub(crate) fn tcp_close(rt: &mut Runtime, handle_id: Value) -> Value {
    if let Some(handle) = rt.gc.integer(handle_id).and_then(|n| n.to_i64()) {
        rt.reactor.close_nowait(handle);
    }
    Value::UNIT
}

pub(crate) fn poll_wait(
    rt: &mut Runtime,
    wait_fds: Value,
    wait_kinds: Value,
    timeout_ms: Value,
) -> Value {
    let timeout = rt
        .gc
        .integer(timeout_ms)
        .and_then(|n| n.to_i64())
        .unwrap_or(0);
    let mut handles = Vec::new();
    let mut kinds = Vec::new();
    if let Some(Object::Array(items)) = rt.gc.object(wait_fds) {
        for &item in items {
            if let Some(h) = rt.gc.integer(item).and_then(|n| n.to_i64()) {
                handles.push(h);
            }
        }
    }
    if let Some(Object::Array(items)) = rt.gc.object(wait_kinds) {
        for &item in items {
            if let Some(k) = rt.gc.integer(item).and_then(|n| n.to_i64()) {
                kinds.push(k);
            }
        }
    }

    if handles.is_empty() {
        if timeout > 0 {
            let dur = Duration::from_millis(u64::try_from(timeout).unwrap_or(0));
            std::thread::sleep(dur);
        }
        return rt.gc.alloc(Object::Array(Vec::new()));
    }

    #[cfg(all(unix, not(miri)))]
    let ready = {
        use std::os::fd::AsRawFd;

        let mut poll_fds = Vec::with_capacity(handles.len());
        let mut mapped_handles = Vec::with_capacity(handles.len());
        let mut ready = Vec::new();
        for (idx, &handle) in handles.iter().enumerate() {
            let kind = kinds.get(idx).copied().unwrap_or(0);
            let raw_fd = rt
                .reactor
                .streams
                .get(&handle)
                .map(AsRawFd::as_raw_fd)
                .or_else(|| rt.reactor.listeners.get(&handle).map(AsRawFd::as_raw_fd));
            let Some(fd) = raw_fd else {
                // Closed handle: wake immediately so caller sees the closed error.
                ready.push(handle);
                continue;
            };
            let events = if kind == 1 {
                sys_poll::POLLOUT
            } else {
                sys_poll::POLLIN
            };
            poll_fds.push(sys_poll::PollFd {
                fd,
                events,
                revents: 0,
            });
            mapped_handles.push(handle);
        }
        if ready.is_empty() && !poll_fds.is_empty() {
            let clamped = if timeout < 0 {
                -1
            } else {
                i32::try_from(timeout).unwrap_or(i32::MAX)
            };
            let res = sys_poll::wait(&mut poll_fds, clamped);
            if res > 0 {
                for (pfd, &handle) in poll_fds.iter().zip(&mapped_handles) {
                    if pfd.revents
                        & (sys_poll::POLLIN
                            | sys_poll::POLLOUT
                            | sys_poll::POLLERR
                            | sys_poll::POLLHUP
                            | sys_poll::POLLNVAL)
                        != 0
                    {
                        ready.push(handle);
                    }
                }
            }
        }
        ready
    };

    #[cfg(not(all(unix, not(miri))))]
    let ready = {
        let wait_ms = if timeout < 0 { 1 } else { timeout.min(1) };
        if wait_ms > 0 {
            std::thread::sleep(Duration::from_millis(u64::try_from(wait_ms).unwrap_or(1)));
        }
        handles
    };

    let mut out = Vec::with_capacity(ready.len());
    for h in ready {
        out.push(rt.gc.int_i64(h));
    }
    rt.gc.alloc(Object::Array(out))
}
