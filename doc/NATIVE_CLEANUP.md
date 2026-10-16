# Native cleanup continuations

This documents the native cleanup continuation boundary and its migration audit.
It does not change the scoped-resource or budget rules in `SPEC.md`. Logical
scoped bindings use the owner trampoline in ABI version 3. The synchronous
compatibility path remains restricted to callbacks it can execute directly.

## Backend boundary

CPS scope exit uses `Terminator::ScopeLeave { marker, value, next }`. The emitter evaluates the saved
scope result, creates the native continuation for `next`, and returns the step
from `ril_rt_cps_scope_leave_then(activation, marker, value, next)`. The old
three-argument scope-leave symbol remains a synchronous compatibility entry.
The runtime saves
the actual current handlers together with the cleanup request. Resumption after
cleanup preserves the original result and lexical cells.

`ril_rt_cps_activation_return(activation, continuation, value)` keeps its existing
signature and returns a step requesting activation closure. Closing an
activation, its resources, and its parent transition can then suspend in the
owner trampoline. Neither entry calls a nested `ril_rt_cps_run`.

The concrete migration points are:

- `ril-ir/src/cps.rs`: new terminator, replacing the synchronous instruction.
- `ril-codegen/src/cps.rs`: `scoped_block`, `unwind_scopes`, and transparent
  scope-leave handling in `tail_answer`; normal completion, explicit return,
  loop break and next must all retain the same ordering.
- `ril-codegen-cranelift/src/cps.rs`: free-name collection for the new terminator,
  continuation construction, and immediate native step return.
- `ril-codegen-cranelift/src/managed.rs`: four-argument scope-leave ABI signature.
- CPS selection: every callable that can register a scoped binding needs an
  owner continuation, including anonymous functions, parameter defaults, and
  synthetic global initializers. Merely recognizing a direct effect call does
  not cover a scoped value whose current `on_close` is selected at exit.
- `managed/cleanup.rs`: remove the current pure-callback availability gate only
  after these paths and the runtime abnormal exits are implemented and tested.

The backend gate now applies only to managed compatibility bodies. Source
cleanup still requires the actual selected callback and handlers to be finite,
to discharge its effects, and to satisfy its authority contract. Protected-body
cleanup uses that body's still-live handler extent, including when an existing
named callback performs an operation. A handler arm's own cleanup instead uses
the arm's outer handler mask. Keep a delimiter alive until protected cleanup and
the arms it creates finish; aborting its body does not retire the handler before
those mandatory actions. Native source tests cover these rules independently of
the low-level embedding fixtures.

## Runtime continuation state

One task-owned cleanup driver retains the target activation and marker, saved
normal result or primary control outcome, remaining exit work, current resource,
handler/continuation state, and saved budget/cancellation masks. All managed
handles remain GC roots while a callback or host wait is pending. Rust stack
guards alone cannot retain the masks across separate native steps.

Pop a registration before invoking its cleanup, and fetch the current `on_close`
at that point. Each callback executes as an ordinary owner-trampoline call with
its own activation and return continuation. Host resource cleanup continues to
run outside the shared heap gate. Required child completion precedes cleanup of
resources reachable by those children.

The driver must also cover failures, cancellation, handler abort, budget
exhaustion, retained handler completion, and a resumption crossing delimiters.
Existing `unwind_activations`, `close_crossed_delimiters`, budget recovery, and
deferred handler-arm completion therefore need resumable exit work. The pending
destination must not execute before every required cleanup finishes. A callback
fault must return to this driver instead of starting a second independent
unwind that loses the original outcome.

On normal exit, a cleanup panic becomes the primary panic and remaining cleanup
continues. A cleanup panic during panic, cancellation, or effect abort records
both causes and abandons remaining cleanup in the failed frame. Internal runtime
faults remain internal faults. Already-active allowances stay suspended during
mandatory cleanup, while a budget created inside that cleanup is active; restore
surviving outer allowances before recovery. Cancellation remains masked for the
full dynamic cleanup invocation, including callbacks and host operations it calls.

## Required source evidence

Use actual native executables on Windows and Linux to verify:

- A finite cleanup with a locally handled operation on normal scope exit,
  explicit return, break, and next; exact LIFO order and original result survive.
- Current callback replacement, failed initialization, and repeated loop
  registration invoke exactly the eligible callbacks once each.
- Panic and cancellation during the body run finite cleanup; a secondary panic
  preserves both causes and skips remaining registrations in that failed frame.
- Handler abort and budget exhaustion finish cleanup before their outer answer
  or recovery handler; abandoned body continuations cannot run.
- Cleanup with its own nested handler and budget obeys the independent allowance
  and restores surviving outer allowances afterward.
- A retained handler's arm and body cleanup retain their specified ordering on
  resume and abort; nested scoped resources inside cleanup work through the same
  trampoline.
- Allocation pressure inside suspended cleanup triggers collection while the
  resource, saved result, handler environment, and exit continuation remain live.

Keep the existing pure-cleanup, host-resource, double-fault, structured-concurrency,
and budget tests as regression coverage. No source availability gate should be
removed merely because the normal-exit case passes.

## Implementation audit appendix

The following synchronous call sites were checked against the current runtime.
Line numbers are navigation aids for this pre-migration version.

| File | Sites requiring resumable exit work |
| --- | --- |
| `ffi_cps.rs` | `scope_leave` at 73; `close_activation` at 96; exported activation return at 154 |
| `ffi_cps.rs` | Crossed-delimiter closure at 479, 481 and 482, including its suspended arm list |
| `ffi_cps.rs` | Resumption-answer redirect at 710; End return at 734/741; Native continuation at 751/761; Delimiter answer at 791/803; FinishArm at 826 |
| `ffi_cps.rs` | Empty-arm resume optimization at 980; final fault cleanup of deferred arms at 1075/1076 and remaining activations at 1079 |
| `ffi_budget.rs` | `close_action` at 160/168, shared by normal budget finish and exhaustion |
| `ffi_concurrent.rs` | Scope finish at 301; parent-cancellation and child-failure recovery at 375/381 |
| `ffi_io_buffered.rs` | Successful helper completion in `publish(Action::Done)` at 222 |
| `ffi_foreign.rs` | Successful invocation completion at 405 |
| `ffi.rs` | Physical frame leave at 130 and lexical scope leave at 161, both reaching synchronous `run_cleanup_stack` at 196 |

Keep the physical-frame fallback restricted to callbacks it can execute
synchronously. Native CPS blocks currently put scoped registrations in logical
activations, so their physical `ril_rt_leave` must not acquire a second copy of
those registrations. Native helper completion must retain its outer continuation,
handlers and result in the exit action; Rust locals and temporary roots that
survive a synchronous call are insufficient across subsequent steps.

The affine flags are another migration boundary. `Step::Return` marks the
continuation used before its synchronous unwind, and `Step::Resume` marks the
resumption used before closing an empty arm. After asynchronous cleanup, do not
re-submit those original steps: that would consume an already-used control
object. Store a post-unwind action such as invoking the selected native entry,
returning to the saved outer continuation, or entering the saved resumed body.
Likewise, preserve a crossed delimiter's checkpoint and deferred arm list until
their cleanup completes; only then remove its delimiter and answer redirects.

### Fault and recovery ordering

Each cleanup frame needs the concurrent-scope depth and activation checkpoint
at callback entry. A scope created inside that callback must finish its own
required child barrier and local recovery before the callback's failure is
combined with the saved primary outcome. Do not give cleanup recovery blanket
priority over all nested scopes.

Once the callback has unwound to its cleanup checkpoint, process its outcome
before any *enclosing* structured-scope recovery. Otherwise a child cancellation
can be cleared or translated to an `Err` before a cleanup secondary fault has
been combined with the original panic, cancellation or effect abort. Re-check
that the resulting fault is still recoverable cancellation and that the parent
token is not canceled before clearing it. Double faults and internal faults must
not become successful scope recovery.

Budget exhaustion similarly waits for all required exit actions before restoring
the selected handlers/delimiters and invoking `Div::exhausted`. A cleanup fault
prevents that recovery. Suspend only the allowances that existed when cleanup
began, preserve their identities across suspension, and leave cleanup-local
budgets active. Host scope completion and provider termination still happen
outside the heap gate even when an internal fault suppresses further Ril cleanup.

### CPS selection and global initialization

The existing expression visitors do not observe the `scoped` bit on a binding:
`walk_block` visits only its initializer. Add explicit scoped-binding discovery
to named-function selection and `callable_suspends`, which is also used for
anonymous functions and lifted lexical functions. Include defaults and nested
blocks, not only direct operation calls. The early `marked.is_empty()` exit in
`suspending_functions` must run after this new seed is considered.

Global initialization has four connected assumptions that cannot be changed
individually:

1. `ril-codegen/src/lower.rs` constructs `__ril_globals` as `Body::Managed`.
2. `managed::prepare` collects published global names only from that managed body.
3. `emit_cps` currently initializes its emitter with `global_init: false`.
4. `emit_entry` invokes the initializer by a direct two-argument machine call.

A CPS global initializer therefore needs preserved global-binding metadata,
global cell publication in the CPS emitter, and proper hidden continuation/entry
dispatch. Flipping its body tag alone loses global publication or violates its
calling convention. Preserve the synthetic role so this change introduces no
extra language function-entry budget event.

The initializer's synthetic CPS protocol is not itself evidence that a user
callable suspends and must not exclude ordinary higher-order builtins. Feeding
that synthetic name into the user-callable suspension
set caused pure dynamic callees to be lifted as CPS while their callers remained
managed. Actual operations, scoped registrations and budgets inside globals
still contribute their real callable dependencies, including nested declarations.
The frontend selection and backend lifting must agree on each ordinary entry's
calling convention. As an additional invariant, the runtime's direct callable
address API now rejects suspending/metered entries rather than letting a native
step be interpreted as an ordinary language value.

Bound `Scope.fork` and `Task.join` values use generated forwarding callables.
Their `NonRetainingAdapter` certificates identify the lexical creator, source
site and checker-selected system builtin. The backend checks the exact body,
arity and receiver capture before using this empty handler selection; a source
callable or mismatched owner/builtin cannot borrow it. These callables preserve
the captured receiver and all of its existing permission, loan, lifetime and
Result obligations. The certificate is neither an environment-free claim nor
copy eligibility. Ordinary callables with no complete handler-selection evidence
remain unavailable when retaining handlers would be required.
