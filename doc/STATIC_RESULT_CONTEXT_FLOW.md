# Result identity under complete static receiving contexts

A written result type selects missing Type arguments without contributing any
object, producer, inspection, freshness, sharing or escape fact. The independent
Result-flow proof carries the same frozen context through its source-schema
query and invocation. Input and explicit selections retain priority.

Each named invocation reserves one real activation before evaluating arguments.
Its selected formal schemas constrain those arguments, and the actual body uses
that same selection. Return contexts belong to the callable's formal namespace;
all formal names mask outer values before the declared types are bound. Local
annotations use the current lexical types. No actual argument tag or scalar
payload proves the universal definition.

Array, tuple, record, Map, Optional and Result constructors project complete
source contexts. Branches, block tails and match arms inherit only their own
result context. `??` lifts the receiving context for its Optional left operand
and uses the genuine payload schema for its fallback. A loop's `last` operand
uses that loop's context; nested calls suspend the caller's loop targets and
restore its return context on both successful and failed analysis.

Finite abstract arrays and Maps also provide the scalar value of a `len` query.
This preserves every member's producer and inspection duty. It neither changes
the array's type nor constructs a fixed-dimension source witness. An unknown
formal collection supplies no backing count and cannot borrow its actual call's
empty input as a universal proof.

The three positive fixtures cover nested return/Optional/loop inference,
Array/record/Map/match transport, and an inner local dimension shadowing an
outer local. Negative cases retain the original Result obligation after an
outer presence check and reject a wrong shadowed dimension. Edited sessions
produce the same diagnostics as fresh sessions.

Both v21 integration gates pass 637 Rust tests, with one explicit ignored test,
across 21 targets. The 288-case independent finite Map model is included per
host. Reports are
`target/static-result-context-and-structural-guards-integration-windows-v21.log`
and `target/static-result-context-and-structural-guards-integration-linux-v21.log`.

Frozen Windows MSVC and Linux GNU native gates each pass all 14 executables
(19 Rust tests): 44 distinct positive Ril sources and 48 entry executions,
including these three fixtures and the three generic-result-context fixtures.
All 16 compiler/runtime/test artifacts have identical before/after SHA-256
hashes on each host. Reports are
`target/static-result-context-and-structural-guards-native-windows-v21-report.json`
and `target/static-result-context-and-structural-guards-native-linux-v21-report.json`.

Expected NI checks are not positive language or native passes. In particular,
the unchanged single-entry nine-scope program still exceeds the independent
channel replay case bound at record 957. It has not entered Core or native
execution. That state-domain obligation remains separate from these accepted
static contexts; no complete compiler or corpus conformance is claimed here.
