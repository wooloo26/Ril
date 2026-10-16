# Native task scheduling integration

## Existing implementation

Structured tasks and Parallel workers now submit task-owned native computations
to a shared bounded CPU executor. Each poll installs its logical Runtime in TLS
and restores the worker's previous state afterward. Completion publishes a task
result under the shared heap gate before retiring its roots; scope exit also
awaits the scheduled worker's retirement. Native waits park their computation.
Host requests run separately and own only host data and cancellation state.
This latest integration is undergoing validation; earlier checkpoints below
describe the preceding thread-per-task stages. Host execution still uses one
thread per outstanding request, so bounded readiness-based I/O remains work.

## Contracts for the implementation

1. A logical task owns its Runtime, native step, driver extent, cancellation,
   handlers, cleanup state and root registration. An OS worker temporarily
   installs that state only while polling the task. The registration lives
   across migration and suspension; it is not a physical-thread identity.
2. The existing C ABI remains synchronous at its outer entry. Internally the
   native driver needs a bounded `drive_slice` operation returning completed,
   yielded, or pending work. Yielding happens only after a native step returns;
   no live native stack address or Runtime borrow can escape the poll.
3. A pending operation retains its continuation, arguments, resource state and
   every managed in-flight value in explicitly traced task state. Host requests
   contain owned host data and cancellation handles. Completion publishes the
   reply before waking its task; a wake arriving during a poll is not lost.
4. Scope finish, join, channel send/receive, host IO and foreign callback waits
   must park logical tasks. They cannot block every CPU worker while the work
   needed to wake them remains queued. Installing a thread pool alone does not
   satisfy this boundary.
5. Cancellation requests wake pending work. A task outcome is not complete until
   its in-flight host operation has terminated/reaped and mandatory cleanup has
   finished. Dropping a future or abandoning a receiver is not cancellation
   completion. Unexpected Rust panics remain InternalFault, including host work.
6. Scheduling and wakeups add no language budget events. Resumed handlers,
   callbacks, native entries and loops keep their existing metering. The source
   ordering and fault-selection rules for Parallel are unchanged.

## Concrete integration order

- Add a safe cooperative executor with a bounded number of CPU workers and a
  per-task poll/wake state machine. Test wake-before-park, simultaneous wakes,
  completion races, worker reuse and shutdown independently of Ril syntax.
- Extract the current native trampoline extent into resumable task-owned state.
  Keep the synchronous ABI as a driver for that state, before moving ordinary
  task execution onto the executor. Retained continuations and cleanup must
  continue to pass their existing native regressions at this checkpoint.
- Replace each blocking internal wait with an owned pending operation and a
  completion subscription. Adapt host operations through a distinct IO service;
  bounded IO execution must not starve a queued operation needed to unblock its
  readers. Platform readiness/cancellation and process reaping remain explicit.
- Switch structured tasks only after all admitted wait paths can release CPU
  workers. Stress a small worker count with nested joins, more channel waiters
  than workers, queued cancellation, forced collection during suspension,
  cleanup suspension, and provider callbacks. Count actual worker concurrency
  and verify the task result stays rooted across retirement.

## Executor foundation checkpoint

`ril-runtime::scheduler` now implements the first layer using safe Rust Future
and Wake APIs. A fixed worker set polls ready tasks; parked tasks remain owned by
an active registry. Wakes during a poll set a pending notification, and duplicate
wakes enqueue at most one subsequent poll. Join is an awaitable completion;
its blocking form is reserved for an outer synchronous driver. Shutdown rejects
active work instead of discarding it. Dropping executor owners closes submission
while existing tasks drain. Poll/destructor panics are reported as host failures.

Six tests pass on Windows and Linux: duplicate wakes, a one-worker nested-join
tree, external wake races and busy shutdown, bounded/reused workers, host panic
classification, and dropping owners with parked work. Both platforms pass runtime
all-target Clippy with warnings denied and have freshly rebuilt runtime libraries.
Logs are `target/native-scheduler-*.log` (Windows tests use the `v2` suffix).

This checkpoint was execution infrastructure, before switching the Ril scheduler.
Ordinary Ril tasks still used their existing threads. The native driver, pending host/channel
operations, task-specific roots and cancellation/cleanup must be integrated
before this executor can claim language-level scheduling coverage.

## Resumable native driver checkpoint

The synchronous C entry now drives a task-owned `NativeComputation` future.
Its native-step extent can yield after a bounded number of steps, retains its
root frame and fault-unwind checkpoints, and moves together with its Runtime.
A private stable Runtime identity prevents resuming it against another heap,
even when two heaps contain equal numeric handle bits. The previous TLS Runtime
is restored after every poll. Completion carries the owning Runtime with its
result until the caller publishes or consumes that result.

Driver tests force collection between slices, reclaim completed steps, move a
paused computation to another OS worker, reject a mismatched Runtime, and run
multiple native computations on two executor workers. The extraction also fixed
an existing fault-entry issue: guarded frame entry could skip the driver's frame
push, after which exit popped its caller's root frame. A pre-existing fault now
still gets the driver's own frame.

Before pending timer integration, the complete runtime unit suites passed
173 tests on Windows and 176 on Linux (one/two ignored subprocess fixtures).
Both hosts also passed 62 targeted CLI groups covering effects, cleanup,
retained handlers, budgets, concurrency, Parallel and task-result GC.
Evidence is in `target/native-driver-future-*.log`; the stronger root-only
collection check is in `target/native-driver-roots-windows.log`.

Pending timer work now adapts native `Time::sleep` to a single host timer service
and cancellation wake registrations. Its driver retains the original call step
as a root while waiting. A synchronous outer entry parks on a wake predicate;
an executor worker can poll another task. Scope/join/channel and the remaining
host operations still require their own adapters before ordinary tasks switch
to the pool. Timer integration is a separate checkpoint from the results above.

The timer checkpoint passes the full runtime unit suite on both hosts: Windows
180 passed with one ignored subprocess fixture, Linux 183 passed with two.
The targeted CLI suites pass 87 groups on Windows and 88 on Linux, including
the platform-specific standard-library cases. Both runtime Clippy checks and
fresh runtime builds succeed. Logs are `target/native-timer-*.log`; Windows
runtime/Clippy validation uses the `v2` suffix.

These tests include more sleepers than CPU workers, a native sleeper yielding
the only worker to another native computation, cancellation registration races,
updating a task's waker, dropping completed registrations, and collection during
a native wait. A regression caught an early cancellation check in the new
builtin classifier: submitted channel sends must still consume transferred
authority before cancellation. The classifier now uses the control-only guard,
and the existing submitted-send test passes through the full trampoline.

## Join and channel completion checkpoints

Native task join now registers an awaitable completion under the task lock.
Publishing an outcome wakes every waiter, but only the first actual join can
observe the Result. Cancelling or dropping a pending join removes its wake
registration without observing a result. Collection after the producer retires
still traces the published outcome through the scope. Runtime suites pass
183 Windows / 186 Linux tests, with the same ignored fixtures; both Clippy
checks, fresh runtime builds, and 14 related CLI groups per host pass.
Evidence: `target/native-async-join-*.log`.

Native channel send/receive now park against queue predicates and cancellation
wake registrations. Queue mutation and registration share a lock; waking runs
after releasing that lock. Submission still consumes detached authority before
checking cancellation. Failed/dropped prepared sends close transferred authority;
received messages remain in the traced receipt set until publication or discard.
Tests cover a one-worker queue with 128 senders, replacing wake targets, dropping
registrations, both native wait directions, and forced collection while waiting.
Runtime suites pass 187 Windows / 190 Linux tests; Clippy, fresh builds, and
29 related CLI groups per host pass. Evidence: `target/native-async-channel-*.log`.

## Scope draining integration

Scope draining uses non-observing completion subscriptions, retains creation
order for fault selection, and waits for worker retirement before releasing
scope channels. The transitional OS-thread path checks `JoinHandle::is_finished`
before joining, parking on the timer service while it is false. This uses the
[standard library's non-blocking join contract](https://doc.rust-lang.org/std/thread/struct.JoinHandle.html#method.is_finished).
Each poll retires at most 64 tasks before yielding. Normal finish and nonlocal
exit carry explicit GC-traced drain/close steps; primary faults remain in the
exit frame throughout suspension.

The first native regression run found an infinite recovery loop: child failure
leaves the scope body's cancellation token requested, so creating or executing
its mandatory drain as an ordinary cancellation point restarted recovery. Drain
control steps now bypass that check, and ordinary cancellation points resume
after restoring the parent token. The original failed/hung CLI logs remain at
`target/native-async-scope-cli-{windows,linux}.log`, with the reproducer in
`target/native-async-scope-recovery-before.ril`. Post-fix runtime suites pass
190 Windows / 193 Linux tests (one/two ignored subprocess fixtures), and both
Clippy checks pass (`target/native-async-scope-{runtime,clippy}-*-v3.log`).
Fresh runtime builds are the `build-*-v2` logs; all 62 targeted CLI groups pass
on each host in `target/native-async-scope-cli-*-v2.log`. The direct driver test
covers normal return, body panic and child-failure recovery; it also forces GC
while a queued child can only run after the parent parks. At that checkpoint,
ordinary tasks still used OS threads pending host, foreign and Parallel adapters.

## Owned host jobs and pending native I/O

`host_job::Job` runs an owned host request outside CPU execution and the managed
heap gate, publishes a reply before waking its task, and waits for worker
retirement before returning that reply. Cancellation uses a child token of the
logical task, so abandoning one operation cannot cancel its parent token.
The native adapters now cover standard streams, file stream operations,
filesystem requests and process operations. Logical host cleanup is an explicit
traced step as well; child termination/reaping can therefore suspend an exit.
Unexpected Rust panics remain InternalFault. If a driver is unexpectedly dropped,
its job requests cancellation, joins its host worker and discards any unpublished
reply as an emergency containment path; this is not normal task cancellation.

The cancellation/publication audit found a separate process leak: cancellation
after the host's last spawn check could drop an unpublished `Child` without
termination or reaping. Synchronous publication now explicitly discards such a
reply outside the heap gate. Native pending publication schedules mandatory
discard as another host job and does not complete its fault until it finishes.
Failure to start that discard worker retains the owned operation and runs its
cancelled containment path, instead of losing child authority in a dropped
thread closure. Discard failures override cancellation with an InternalFault
that preserves the previous outcome as its primary cause.

Tests cover 32 blocked host requests with one CPU worker, panic classification,
job abandonment, synchronous and pending unpublished-spawn cleanup, and an
actual signalled sleeping child while a queued CPU task collects the shared
heap and requests cancellation. Runtime suites currently pass 197 Windows /
200 Linux tests (one/two subprocess fixtures ignored), recorded in
`target/native-host-pending-runtime-*-v3.log`. Native CLI validation and the
remaining routing work are separate gates.

This stage uses one host thread per outstanding request. It establishes owned
requests and completion/cancellation boundaries; it is not a bounded readiness
service. Entropy, foreign provider/callback/abort waits, Parallel dispatch and
remaining direct-call paths still need integration. Selective CPS must classify
actual host suspension and its transitive callers before ordinary Ril tasks can
switch to the CPU executor. Source effects alone do not establish that property.

## Shared CPU executor integration

Parallel coordinates awaitable worker futures on the shared executor, including
nested Parallel calls and the fixed fold/merge order. Callback results remain in
the traced Group until arbitration; retirement is awaited even after a callback
fault. The seven previous Parallel runtime tests pass after this conversion,
including actual overlap, explicit bounds, stable fault/index selection and
cleanup cancellation protection. A new test runs 96 nested groups on one CPU
worker while every leaf collects the shared heap. The full runtime checkpoint
passes 205 Windows / 208 Linux tests (one/two ignored fixtures) in
`target/native-parallel-pool-runtime-*.log`. Later task/yield changes are separate.

Default Fiber::yield now saves its Return step and complete driver checkpoint,
then returns Pending immediately. The driver roots the next step before yielding;
the NativeComputation wake queues the logical task again. A user handler still
receives the operation before this default behavior. Scheduling adds no Div
events. The root-only forced-GC regression passes in
`target/native-fiber-yield-windows-v2.log` (the first fixture retained construction
temporaries and therefore did not establish reclamation).

Ordinary fork now submits a NativeComputation future to the same executor.
Captured channel authority belongs to a guard constructed before submission,
so rejected or never-polled work closes it and publishes an InternalFault rather
than leaving a reserved task incomplete. Scope draining waits for the scheduled
future as well as its published outcome. Windows tests exercise 64 tasks with
nested scope children on a single worker, forced collection, and rejected
submission after authority transfer (`target/native-task-pool-*.log`). The
post-switch native CLI checkpoint passes 77 groups on each host, covering
budgets, effects, cleanup continuations/handler extents/faults, structured tasks,
task-result GC, blocked streams/filesystem operations, buffered I/O, host CPS,
Parallel and historical-recency cases. Logs are
`target/native-task-pool-cli-windows-v2.log` and
`target/native-task-pool-cli-linux.log`. The first Windows run exposed a static
resource-scan regression for the standard TaskFault representation; the finite
scanner now visits registered builtin constructor payloads and the original
scope-cancellation source passes. The earlier failed log remains unchanged.
These are component integration results; a new frozen full-corpus/workspace
snapshot remains a separate acceptance gate.
