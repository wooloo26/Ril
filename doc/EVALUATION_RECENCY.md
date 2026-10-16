# Temporary values during semantic evaluation

Allocation-site recency moves an earlier object from the recent node to its
older summary when the site is evaluated again. The heap and stored bindings
already follow that move. A `Value` held in a Rust local must follow it too;
otherwise two references to the same object can appear disjoint at a later
borrow check.

`EvaluatedValue` records the cursor *after* its value was evaluated. Before the
value is consumed it replays only subsequent moves through
`copy::remap_value_origins`, including correlated origins and nested payloads.
Loan/root participants, binding IDs, Result producers, condition evidence and
numeric-use IDs remain stable. A wrapper belongs to the same Checker's
monotonically growing history; this protocol cannot be reused with a truncated
branch log or another checker.

The written-order call preparation keeps the callee, explicit arguments and
omitted defaults at their own epochs. Tuple, array, map and record members are
kept until the receiving object has been allocated, then published with current
origins. Pipeline prefixes, indexing receivers, assignment values across target
evaluation, derive drafts and multi-argument constructor payloads use the same
transport. Named invocation inputs are also refreshed before returned-sharing
checks; otherwise an allocation in the body could hide legitimate retention.
Possible callable alternatives keep their input and output temporaries current
as later alternatives are checked.

Ordinary `if` already uses `FlowSnapshot` and checked graph transport for its
left result and saved branch. Its pre-join type reception now uses a current
temporary view without applying the move twice to the final join. The older
`PatternState` protocol has not gained graph transport: recycling during any
match arm, including preview and exiting arms, retains the explicit
allocation-version `NotImplemented` boundary. Map lookup still conservatively
joins all possible values; two different map keys do not independently prove
their child graphs disjoint.

`evaluation_recency` compiler tests compare alias rejection with independent
object controls for calls, pipelines, defaults, aggregate members, indexing,
assignment and branches. The CLI counterpart executes the independent cases
and checks mutation results. Unsafe alias examples are checked, never run.

The capturing-callee audit additionally exposed a missing exclusivity check
inside an actual closure invocation. It must run before local loans are
normalized into caller roots, preserving independent captured paths. Latent and
signature probes require conditional obligations and exact actual-creation
coverage; merely omitting their checks is not a completed proof. That separate
coverage migration and escaping shared-loan normalization are tracked
independently and must not be counted as closed by the temporary-value tests.
