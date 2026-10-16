# Observable storage across repeated callbacks

Repeated collection, iterator, stream, and foreign callbacks widen changing
scalar inputs before checking an arbitrary invocation. Existing reference
storage must keep a stable graph until an explicit heap transfer fixed point is
available. Result production and inspection remain obligations of each actual
invocation.

The repeated-call snapshot compares observable bindings rather than every
historical binding allocated by declaration probes. A finished probe can retain
an inaccessible local Result whose allocation-site recency changes during the
real call. Comparing that bookkeeping value incorrectly rejects an otherwise
checked callback even when no live storage reaches it.

An `alive` filter alone is insufficient. A returned anonymous or named callable
can retain a formal, local variable, or scalar storage cell after its creating
lexical frame ends. Handler recipes and cleanup callbacks can reach the same
ended frames. `repeated_observable_bindings` therefore closes its binding and
heap roots over:

- Entry bindings with `alive`, and captures of all known anonymous and named
  callable recipes, conservatively including potential escapes.
- Active or callable-retained handler declaration environments, their outer
  handlers, and pending handler answers. Cleanup callable captures follow the
  ordinary callable and heap-field paths.
- Actual arguments, current-frame returned values, pending abort answers and
  loop-break values, and retained concurrent values.
- Binding forwarding, source/scoped/callback-parameter bindings, storage cells,
  loan/root participants, callable-contract lexical environments, nested
  payload witnesses, and reachable heap fields.

Saved budget, foreign-return, foreign-abort, cancellation, resumption, and
deferred or suspended cleanup states retain additional control-flow snapshots.
While those states lack a common root visitor, their presence conservatively
retains all historical bindings. This can preserve an incompleteness boundary;
it cannot justify dropping a potentially observable binding.

The change only selects the binding snapshot and its reachable heap roots. The
existing graph comparison still checks reference identities, callable and
Result memberships, payloads, permissions and publication, live fields, node
kinds and causes, and array lengths. Scalar widening remains unchanged. A
captured reference replaced by fresh storage still requires a fixed point.

No Result duty is cleared by root selection. Every normal callback exit must
inspect its actual producers. Wildcards, one input-dependent branch, an earlier
call's inspection, and an outer Result tag do not discharge independent inner
or later producers. Returning Results from a traversal, or storing them into
retained state, still requires its existing multiplicity or escape proof.

`crates/ril-compiler/tests/repeated_host_results.rs` checks accepted sources through
verification and Core lowering, and checks negative inspection and retained
graph transitions. `crates/ril-cli/tests/repeated_host_results.rs` executes the original
host callback source unchanged and exercises ended formal, local, named,
handler, and cleanup captures through repeated native calls. The original
source fixture is `crates/ril-compiler/tests/fixtures/repeated_host_results.ril`.
