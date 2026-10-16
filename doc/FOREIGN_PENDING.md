# Pending foreign provider transport

Foreign calls now use the native driver's pending host-job path. Entering a call
registers its managed invocation and queues a host-only request. It does not wait
for process creation, the Ready handshake or the first protocol reply on a CPU
worker. A callback return similarly queues sending the reply and receiving the
next event. A final provider return remains provisional until a separate host
request has observed successful process exit and retired the transport workers.

## Ownership and roots

`Invocation` holds the binding, evaluated arguments, callback handles, caller
continuation, handler chain and activation. It remains in `Runtime.foreign_calls`
through every pending wait, preserving the existing precise GC root traversal.
Only provider configuration, protocol values, cancellation state and the native
`Session` enter a host job; no Runtime borrow or managed callback runs there.

The transport has explicit Ready, Waiting, Callback, Closing and Closed states.
Each queued operation and close receives a checked monotonically increasing
per-call ticket. Starting an already waiting operation, publishing a stale reply,
or closing while a request still owns the session is an internal failure. Reply
validation and graph decoding occur on the original logical task. Callback token
and request sequencing remain affine and independent of wait tickets.

A successful reply containing a live Session is restored to the invocation
before managed callback validation. If validation fails, normal fault unwinding
owns the subsequent asynchronous close. A reply that loses its owning invocation
is discarded through another host job. An unstarted abandoned request is discarded
without spawning its provider. Host admission failure and unexpected driver Drop
retain emergency cancellation/drain containment, rather than reporting success.

## Exits and cancellation

The invocation's cancellation child is shared with its host requests. Cancellation
of a pending wait wakes the provider transport and finishes terminate/reap before
the host reply becomes ready. During callback execution the invocation continues
to own the idle Session; aborting that callback queues a mandatory foreign-close
job. Provider panic, malformed protocol, codec failure and callback language panic
likewise retain native transport ownership until close.

The exit machine drains child scopes first, waits for foreign close, then continues
the activation cleanup stack. The original exit or fault stays in its ExitFrame
through this wait. Internal close failures are recorded alongside that primary
outcome. The managed invocation is removed only after close has completed.

## Validation and remaining scope

Four runtime groups use real provider subprocesses and barriers to cover pending
handshake/final-exit waits, callback ownership and forced collection, cancellation
after the provider has entered a wait, abort close, replayed waits and discarding
an unstarted request. The CLI foreign suite exercises real callbacks, defaults,
generic instances, retained handlers, live handler abort, mixed normal/abort
callbacks, malformed providers, cancellation, and a callback with a transitive
`Time::sleep` call. Log names use `target/foreign-pending-*`.

This adapts foreign transport to the resumable native driver. It does not replace
the general Concurrent task implementation with a bounded logical-task scheduler,
nor does it grant external bodies finite language-budget coverage.
