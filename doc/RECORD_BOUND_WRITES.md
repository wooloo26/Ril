# Writes through structural record bounds

Structural type evidence preserves a member's type and declared mutability.
Write authority comes from the actual received path and its mutable loan.
The two proofs remain separate.

The checker records a `BoundFieldWrite` for each bounded field assignment. Its
pre-write `GenericBoundProjection` remains `ValueOnly`: looking up the old
member does not authorize the store. The write also references the actual RHS
and receiver expression observations, a historical `ObservedAccess`, the
received replacement, and the existing receiver graph after the store. Core
preserves these records and identities.

Independent replay locates the real assignment in its lexical owner's source
body. It checks RHS-before-receiver evaluation order, the exact parameter root,
whole argument arity, the real `mut` formal loan, member mutability and frozen
allocation epoch. It reconstructs the temporary-path restriction applied by
mutable reception. It cannot add write permission to the original argument.

The historical access keeps its original participants, owners and allocation
epoch. Frame normalization cannot rewrite this receipt. Its transported write
footprint must remain in the actual invocation summary; the ordinary exclusive
access and stored-authority checks still apply. Missing records, a readonly
receiver, an unrelated root or a changed epoch cannot discharge the obligation.

The first implemented replay admits direct named `mut` parameters, exact
singleton receiver storage and scalar `=` replacements with an unchanged actual
RHS descriptor. It checks the complete post-store graph, preserving every other
field, node, dimension and relation. Compound operations, nested mutable loan
paths, retained parameters, weak updates and reference/Result replacements need
their own receiving and store proofs and remain explicit incomplete work.
This component does not certify every capability transfer in the compiler.

The original valid fixture was incomplete in the frozen compiler:
`target/record-bound-write-source-before-windows-v2.json` reports the missing
assignment result observation. The first replay gate then exposed the missing
temporary-path receiving step; that failure remains in
`target/record-bound-writes-source-windows-v1.log`. After reconstructing that
step, all seven initial compiler test groups passed in
`target/record-bound-writes-and-template-source-windows-v2.log`. They exercise
real Source/Core lowering, readonly and immutable-member errors, evidence
deletion and mutations of tokens, order, arity, receiver permissions, loans,
epochs, owners, replacement and post-store graph. The expanded eight groups,
including 32-bit static layout and deletion of the actual summary's write
footprint, passed on Windows and Linux in
`target/scoped-write-template-source-windows-v4.log` and
`target/scoped-write-template-source-linux-v4.log`. Those combined gates still
fail a separate static Map/coalescing case and are not whole-batch passes.
The subsequent v9 integrated gate passes 590 Rust tests on each host, with one
explicit ignore. The actual scalar-store program also executes successfully
on Windows and Linux in
`target/scoped-write-template-native-windows-v9-record-bound-writes.log` and
`target/scoped-write-template-native-linux-v9-record_bound_writes.log`.
The whole component-native batch runs 36 distinct positive sources and 38 entry
executions per host. Its ten test executables all succeed, and the CLI, runtime
and test executable hashes remain unchanged throughout execution. Negative and
incomplete sources are checked separately and are not native passes.
