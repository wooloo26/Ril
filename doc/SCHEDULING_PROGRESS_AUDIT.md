# Pure computation, cancellation and logical yielding

This audit separates cancellation already requested from whether its source can
obtain a CPU worker. It does not infer a fairness guarantee from an effect row.

## Language requirements

- SPEC 3449–3454 permits ordinary pure `MayDiverge` functions. Even proven finite
  local computation promises no wall-clock bound or external scheduling progress.
- STD 1363–1374 requires cancellation of channel/I/O, join and nested-scope waits,
  but explicitly allows a diverging body or child to prevent scope exit after
  cancellation. There is no finite completion bound.
- SPEC 4863 and 4890 and STD 1319 make unhandled `Fiber::yield` an actual cooperative
  yield. A matching user handler may discharge the request instead. This is a
  distinct contract from time slicing arbitrary pure computation.
- STD 1460–1471 requires finite Parallel callbacks, including callees, handlers
  and cleanup. An infinite pure callback is not an admitted Parallel workload.

## Current native paths

Managed `loop {}` invokes the ordinary block prologue on every iteration. Its
`ril_rt_scope_enter` and `ril_rt_unit` calls enter `guarded`, which observes an
already requested cancellation unless cleanup has masked it. While/for bodies and
named recursive entries also reach guarded operations. The emitted Managed call
still owns a native stack until it returns: `Target::Native(..., false, ...)`
cannot return Pending merely because the outer driver has a 64-step allowance.
These cancellation checks are not logical scheduler yield points.

When every worker is occupied by pure divergence, a cancellation source queued on
that same pool can starve. This is a progress limitation rather than evidence that
the compiler must reject ordinary pure loops or convert every loop to CPS. A new
preemption guarantee would require its own continuation/safepoint design; it must
not be implemented by inventing language Div charges.

The audit identified that default Fiber yield used OS `thread::yield_now` while
continuing the same native-driver poll. The driver now retains its Return step and
checkpoint and immediately returns Pending. `NativeComputation` requeues that
logical task. User-handler dispatch precedes this fallback and is unchanged.

## Callback and synchronous-entry boundaries

Order's sort/search and the collection/variant HOF adapters expand to Core calls,
so a local-handler or Parallel callback preserves its native continuation. The
remaining synchronous callback ABI explicitly rejects CPS callback handles.
Heap now also expands to Core callback calls. A private traced transaction owns
the opaque heap's sift state, and commits only after all comparator calls return
successfully. The synchronous ABI guard remains in place. Heap operations inside
`Div::budget` now carry actual retained-comparator coverage for a complete,
unambiguous receiver. Unknown or uncertain comparator provenance retains an NI;
construction and passive reads do not invoke the comparator. See
[HEAP_CONTINUATIONS.md](HEAP_CONTINUATIONS.md).

Global initialization is always lowered to CPS. Its synchronous driver bridge is
at the outer native main entry, before the selected language entry; it is not a
pool task waiting on another task of the same pool. Ordinary scoped bodies are
selected for CPS by `has_scoped`; compatibility Managed cleanup admits only
certified synchronous callbacks. Required cleanup remains finite and cancellation
masked. A cleanup using nested Parallel takes the CPS exit path.

## Reproductions

Scratch sources and reports are preserved under `target/scheduling-audit`:

- `pure-loop.ril`: `spin` is Managed; the scope forks it and a panicking sibling.
  Native execution returned unit after checking Err, confirming cancellation is
  observed when the source runs in the existing task implementation.
- `selected-conventions.ril`: pure scalar and finite recursive helpers are
  Managed, Fiber yielding and its caller are CPS. Native assertions pass.
- `unproved-recursion.ril`: the no-normal-return recursive summary remains an
  explicit provenance NI, not an accepted finite proof.
- `parallel-spin.ril`: a pure infinite Parallel callback is rejected with E0820.
- `order-handled.ril` and `order-parallel.ril`: local-handler and Parallel
  comparators execute natively through structured Order lowering.
- `heap-handled.ril`: the same admissible local-handler comparator originally
  reported a Heap structured-lowering NI, preserved in `heap-handled-native.json`.
  The unchanged source returns unit after continuation lowering on Windows and
  Linux in `heap-handled-native-after-{windows,linux}.json`. The
  `heap_continuations` source and Core regressions cover this accepted path and
  the actual retained-comparator source-budget certificate.
- `heap-budget-before.ril`: its original finite-callback provenance NI report
  remains in `heap-budget-before.json`. The unchanged source is accepted in
  `heap-budget-after-{windows,linux}.json`. Native budget threshold probes preserve the
  exact sift comparison schedule without adding generated loop events.
- `global-cleanup.ril`: a global initializer and ordinary function both run a
  scoped finite cleanup containing Parallel; native execution returns unit.

`conventions.log` records Session → Core → native calling-convention selection.
These probes do not claim bounded-pool fairness or replace native task-pool stress
tests after that implementation is enabled.
