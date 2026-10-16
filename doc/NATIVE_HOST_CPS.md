# Native host suspension and calling conventions

This is an implementation contract, not a change to language effect permissions
or the native ABI. `@Fiber` alone is not a scheduling proof. Classification follows
the actual operations and callable edges in verified Core.

## Observed routing gap

The read-only source audit is saved in
`target/specialization-audit/src/bin/host_classification.rs` and
`target/host-cps-classification-current.log`. Before this change, legal host-only
functions calling stdio, whole-file reads, process execution, entropy, or sleep
and their named callers all selected `Body::Managed`. A callable interface that
invoked one of these functions was also Managed. A Concurrent parent or foreign
adapter could select CPS while its host callback and transitive helper remained
Managed.

The runtime correctly invokes a Managed target directly, even from a CPS
`Step::Call`. Therefore that callback executed the synchronous `ril_rt_builtin`
host bridge; it never reached the CPS host pending adapter. Releasing the shared
heap gate during a host wait does not release the CPU executor worker.

The audit also checks that a Parallel callback with residual `@Fiber` effects is
rejected by the existing E0605/finite-computation rules. Classification does not
authorize that callback. A pure callback may legally call another Parallel
operation, and its continuation still has to use CPS.

## Classification contract

The explicit control-operation set includes structured tasks, channels,
Parallel, buffered I/O, foreign invocation, sleep, stdio/print, file streams and
filesystem operations, process operations, and entropy. It describes operations
that need a continuation; it does not assert that every runtime host wait has
already acquired a pending adapter.

HOF expansion precedes classification. Named callers inherit their callees'
suspension classification to a fixed point. Parameter, local, and computed
callees are potentially suspending even if the module contains no other direct
suspension seed. Lifted named functions, closures, and their defaults use the
same rule. A pure leaf with no suspending or unresolved call remains Managed.
The synthetic global initializer is CPS for bootstrap purposes and does not
itself classify unrelated user functions as suspending.

`ril-codegen` and `ril-runtime-api` cannot depend on one another under the
architecture policy. Their explicit builtin tables are checked together in
the Cranelift backend, which already depends on both. The managed direct-call
guard remains in place; this change routes valid calls before reaching it.

## ABI and event preservation

ABI version 3 is unchanged. Managed entries take `(environment, arguments)` and
return a language value. CPS entries take the same machine parameters, with the
continuation appended to the managed argument tuple, and return a native step.
`CpsClosure` and `BudgetClosure.normal_is_cps` distinguish those contracts. A CPS
caller can still invoke a Managed pure value: the trampoline wraps its returned
value in the saved continuation.

The normal entry is classified before code emission. Its metered sibling remains
CPS and preserves the existing function, call, callback, loop, and resume event
sites. Classification adds no budget event and does not reorder explicit
arguments, defaults, callbacks, or cleanup. Native nonlocal exits continue to
use the task-owned cleanup state machine.

Compiler source tests inspect the actual native body choice for direct,
transitive, dynamic, Concurrent, and foreign edges. CLI regressions exercise
host callbacks, aliases, defaults, HOFs, pure Managed targets reached through
CPS interfaces, filesystem helpers, and nested Parallel. Existing budget and
cleanup suites remain necessary integration checks.

The combined audit that put `Io::stdin_read`/entropy Result inspection inside
an `Array::map` callback still reaches an existing frontend repeated-heap
fixed-point NI, before native classification. Its source is retained at
`target/host-cps-repeated-result.ril`; it is not counted as native support. The
accepted HOF regression uses a sleep callback, while the Result-producing host
leaf is exercised through named, dynamic, default, and immediate-lambda calls.
