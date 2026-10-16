# Static constant graph native fixtures

These source regressions are executed by `ril-cli/tests/static_constant_graphs.rs`
and pass on Windows and Linux. They exercise the implementation described in
`doc/STATIC_CONSTANT_GRAPHS.md`; they do not change the frozen corpus snapshots.

- `shared_and_distinct.ril`: preserve shared children and keep equal allocations distinct.
- `later_projection.ril`: a later meta projection reuses an earlier arena node.
- `map_and_variant.ril`: tuple, ordered map and variant edges refer to one child.
- `worker_allocation_pressure.ril`: a shared worker keeps constant roots while
  1200 array allocations cross the runtime's initial 1024-object GC threshold.

Each fixture can also run with entry `test_native`. The Rust suite adds distinct
outer shells with shared children, empty/None-first containers, scalar widths,
fixed arrays, normal/metered entry aliasing, and 400 distinct constant nodes that
force collection during pool initialization. Additional qualifier and malformed
private-reference tests remain at the frontend verification boundary.
