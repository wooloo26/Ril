# Native filesystem cancellation

Filesystem requests copy native paths and immutable bytes out of the managed
heap before starting host work. Each request uses the task's host cancellation
token, which is shielded during mandatory cleanup. Completion waits for the host
worker to exit and joins it; cancellation never detaches a thread that still
owns an open operation, file handle, or transfer buffer. An unexpected worker
panic stays an internal fault even when cancellation arrives concurrently.

Whole-file operations open the requested file and transfer bounded chunks.
They check cancellation before each syscall and before retrying an interrupted
call. A canceled whole-file read does not return its accumulated prefix or a
fabricated EOF. A canceled write leaves any prefix already committed to the host;
it does not retry that prefix or report a successful empty write. Empty writes
still open with WriteTruncate, so ordinary files are created or truncated under
the same mode contract.

## Linux

The audited open/read/write path uses rustix's single-syscall wrappers. In
particular, it does not use a standard-library open loop that silently retries
EINTR. Blocking FIFO open retains the peer rendezvous; an O_NONBLOCK read-open
would otherwise succeed before any writer exists.

Dedicated filesystem workers temporarily lease an otherwise default realtime
signal from libc's usable range. The process handler is empty and omits
SA_RESTART. Only the worker unblocks that signal. The owner directs repeated
wakes to its still-joinable worker after cancellation, closing the race where a
request precedes entry to the blocking syscall. The previous disposition is
restored only after every worker sharing the lease has been joined. An existing
non-default handler is not selected; if no free signal exists, setup reports an
Unsupported I/O error. An embedding host must not replace a leased disposition
while these workers are active.

Linux documents that blocked FIFO open and read/write on slow devices return
EINTR without SA_RESTART; an interrupted transfer that already made progress
can instead return its committed byte count. Local disk waits are not in that
interruptible class. See [signal(7)](https://man7.org/linux/man-pages/man7/signal.7.html)
and [open(2)](https://man7.org/linux/man-pages/man2/open.2.html).

The implementation verifies no-peer read and write opens, waiting after a real
read prefix, cancellation after a committed write prefix, normal FIFO EOF, and
signal-disposition and mask restoration. It does not claim that signals cancel
every device, network-filesystem operation, or kernel uninterruptible wait.
Other filesystem helpers currently observe cancellation at their host-call and
directory-iteration boundaries; their underlying library/kernel calls can still
delay completion. The worker remains owned and is joined even on those paths.

## Windows

The existing host-transfer supervisor repeatedly requests CancelSynchronousIo
on its dedicated worker until that worker has completed, then joins it. This
covers supported synchronous CreateFile/ReadFile/WriteFile waits, with checks
between whole-file transfer calls. The named-pipe read regression keeps a real
writer alive after a prefix while the Ril task cancels its remaining wait.

Cancellation depends on the underlying driver and operation. Microsoft's
documentation specifically excludes MoveFileEx from these cancellation APIs;
the current no-replacement rename implementation therefore observes cancellation
after that host operation completes. No claim of arbitrary-driver cancellation
or a fixed completion deadline is made. See
[Canceling Pending I/O Operations](https://learn.microsoft.com/en-us/windows/win32/fileio/canceling-pending-i-o-operations).
