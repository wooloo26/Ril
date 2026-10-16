# Finite resource and copy capability scans

Resource discovery returns `Present`, `Absent`, or `Incomplete`. Only a complete
`Absent` result proves resource freedom. Unknown types, unresolved rows, missing
instance identity, and exhausted scan budgets retain their obligations.

The capability readers expand one current alias layer and visit structural
children separately. They identify an instance by its canonical declaration
name and complete normalized `TypeArgument` identity, including static values,
array dimensions, and callable qualifications. A backedge closes only the same
instance; a growing generic family does not close merely because its constructor
name repeats. Each reader admits at most 128 distinct alias instances and 4096
structural nodes, charging before alias syntax is converted or substituted.
These are implementation proof budgets, not language restrictions: exceeding
one returns `Incomplete` and retains the obligation instead of declaring a
program invalid or inventing an absence proof.

`ty_substituted_shallow` preserves descendant `Named` and `Applied` identities.
The existing `ty_substituted` entry keeps its expanding behavior. Ordinary-loop
eligibility and clone qualification use finite shape reads instead of recursively
materializing the complete representation graph. Missing clone constituents keep
a shared scan budget and remain explicit when their evidence is incomplete.

Value resource scans additionally use actual selected sum payloads and complete
closed storage witnesses. An inactive Ok/Err/None inference hole does not create
a reachable resource. This requires actual witnesses; unknown members and open
rows still cannot prove absence. Standard constructors are checked even when they
have no user `TypeDeclaration`: TaskFault and UnwindCause have complete registered
payloads, and PanicInfo uses its existing standard representation. Foreign opaque
resources and nominal constructor payloads retain their resource restrictions.

## Regression coverage

The original binary recursive clone source now completes both Session checking
and Core lowering. A native regression covers two self-edges, repeated cloning,
two-node cycles, a shared child reached through both fields, and immutable
snapshot isolation. A resource sibling branch remains rejected by `E0530` and
is checked without executing the negative program. Existing Result carrier,
generic copy, ordinary-loop, and source visibility regressions remain covered.

The independent execution oracle assigns concrete object IDs that never recycle.
It implements concrete reachability, copying, branch selection, and projections
without consulting analyzer authorization. The production clone batch mapping is
treated as a witness and checked against concrete edges, aliases, cycles,
read-only paths, and asserted equality or separation. Allocation recency events
only transport the representation witness; they do not recycle concrete objects.

Its finite domain has two initial objects and two fields per object. Each field
is absent or is a read/write reference to either object, giving `5^4 = 625` graphs
with permissions. Distinct and recycled initial allocation sites produce 1250
cases. Every case executes branch selection, repeated shell allocation at one
site, three further mutable copies, and an immutable copy. Paths of length zero,
one, and two are checked after the transitions.

All 1250 full traces passed in ten disjoint contiguous shards of 125 cases on
Linux. The case-ID coverage union is exactly `[0,1250)`, with no omitted or
double-counted case. Every process had a 512 MiB virtual-memory hard limit and a 20 second
timeout. The longest shard took 7.48 seconds; maximum RSS was 23528 KiB. The
combined execution time was 67.03 seconds. Normal tests retain a representative
full trace; the complete audit is an explicitly ignored test because the entire
matrix exceeds a single 20 second probe. Windows also passed the representative
trace and 16 distributed full-trace samples under a verified 512 MiB job limit.

To reproduce a contiguous shard, set `RIL_ORACLE_CASE_START` and
`RIL_ORACLE_CASES`, then invoke the compiler test executable with:

```text
--ignored --exact sema::checker::execution_oracle::every_two_object_graph_executes_against_the_concrete_model --test-threads=2 --nocapture
```

Use external memory and time limits. `RIL_ORACLE_SAMPLE` selects evenly distributed
samples instead of a contiguous shard. `RIL_ORACLE_INITIAL_ONLY` reduces the audit
to the first copy; such a run is not a full-trace audit. The complete result above
used neither option. The model excludes resources, Results, callable environments,
arbitrary writes, and graphs with more than two initial objects. It is a finite
validation of the stated graph behavior, not a proof of all language semantics.
