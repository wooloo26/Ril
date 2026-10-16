# Boolean inspection evidence

A nested `is` predicate can inspect an inner Result only after its outer tag
matches. A successful assertion or conditional successor may therefore know
more inspections than the unconditional state following evaluation of the test.
The checker preserves that distinction without evaluating the pattern again.

Each actual boolean predicate creates a `ConditionEvaluationId` with its dynamic
named/default/closure invocation context, lexical owner, source location, and
CauseId. `ConditionInspections` belongs to the resulting boolean Value. It records
producer IDs inspected on every path yielding true and on every path yielding
false. These IDs come from the existing inspection judgment, which checks must
membership, Result families, conditional copies, and iteration eligibility.
An arbitrary set of possibly reachable producers is never an inspection proof.

Pattern components compose these sets in actual short-circuit order. Expected
expressions execute once. Negation swaps outcomes; conjunction and disjunction
meet all viable ways to obtain each result. Ordinary Value joins account for
constant outcomes and intersect evidence from every viable alternative.
Assertions consume their evaluated argument Value. They neither look up the
last expression with a matching source span nor rerun the subject or pattern.

Evidence follows the same boolean through storage or a return. Wrapping that
boolean in Some, Result, a user variant, or an aggregate does not make the
wrapper's tag test equivalent to the payload's truth. Wrapper construction clears
outer boolean evidence and preserves the real payload's evidence. Comparisons
and collection summary predicates create their own boolean results. Cancellation
widening drops completed-body boolean evidence because an earlier scalar state
may be selected instead.

An inspection records the original producer IDs; copying a Result creates its
own obligations. Historical boolean evidence does not remap onto those copies
or acquire subsequently added family members. Closed loop families strip their
boolean evidence from surviving state. Trace evaluation IDs do not participate
in semantic equality. Valid repeated production creates fresh producer IDs; the
already unsupported recovery case that reuses an ID also advances a checked
generation so stale evidence cannot discharge it. Generation overflow fails
closed rather than wrapping.

Core provenance keeps all condition events and Value evidence, including causes,
invocation context, producer sets, and generations. Diagnostic spans remain
diagnostic data: distinct owned-AST predicates at the same span retain distinct
events and do not borrow one another's inspections.

`nested_result_conditions` covers the original two-channel nested Result source,
successful and failed nested tests, short-circuit paths, wrapper truth, exact
expected-expression evaluation, copied Results, loop freshness, budget recovery,
and equal diagnostic spans. Windows and Linux native regressions also exercise
the original channel source, stored boolean assertions, and a side-effecting
expected expression that must execute exactly once. Unmatched outer tags and
wrapper-only assertions retain E0720 for an independent uninspected producer.
