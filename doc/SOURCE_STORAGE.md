# Storage source schemas and write receipts

Status: design for the confirmed storage receiving defects. The ledger below is
not implemented or verified yet. `storage_source_receiving.rs` deliberately
retains four strict failing regressions and a matching-schema positive group.
Before evidence is in `target/storage-source-before-v45-report.json`.

## Declaration identity

Keep an append-only declaration-source arena indexed by a typed source ID and
the actual dynamic `BindingId`. A binding's current `Value`, its latest source
witness, its name, its source span, a backing length and a heap node cannot
replace the declaration's type view. Scope and invocation identity remain
necessary when a declaration is evaluated repeatedly.

Freeze written binding types before evaluating the initializer. Retain the
actual initializer root returned by the recorder and its allocation epoch.
Inferred bindings use the initializer's original complete source, with explicit
unresolved entries for missing evidence. Empty literal element inference needs
an owned, monotone type obligation; missing evidence must neither become an
ambient type nor permanently disable existing ordinary inference.

Typed patterns project the actual initializer and declared schema through the
same tuple/record/payload path. Named formals are frozen after their real generic
selection and before binding; closures also retain their actual creation scope.
Captured variable cells refer to the original binding/source ID.

## Reception

Each assignment and storage intrinsic checks the original RHS source against
every possible destination schema before type ascription or storage mutation.
Variable reassignments preserve their declared source view. For example, writing
`[2]int` into a `[]int` variable must leave subsequent reads typed `[]int`.
Record and tuple projections must preserve this rule for their members too.

Collection roles cover array elements, map keys and values, and set elements.
The same interface should later cover opaque Deque/Heap insertion contracts.
Expected element types come from the original receiver source, never current
contents or inserted values. Recursive scalar element graphs need a frozen
proof of absence of Array/Fn coordinates even if their whole recursive schema
has no finite expanded tree. Unknown type/row/source conditions remain duties.

Source coordinate compatibility is separate from mutation, retained-sharing,
loan, effect, Result, resource and fixed-storage resize checks. Callable bounds
retain their original lexical environment; matching raw annotation text alone
does not establish resolved row equality.

## Physical evidence and independent validation

Use actual recorder-returned expression indices and epochs for the RHS,
receiver and selector. A target may execute after the RHS and cause recency
transitions. Do not search later by source span or take the last expression.
Ordinary intrinsics reuse `CallArguments.supplied` and `argument_of(event,slot)`.
Pipelines need their own genuine observations; an enclosing call cannot supply
missing pipeline operands.

Add source-reception receipts alongside actual write/access facts. Existing
`BoundFieldWrite` is limited to genuine bound projections and exact scalar
stores, so it cannot certify arbitrary ordinary stores. If ordinary writes use
`ObservedAccess`, coverage must be the union of independently validated receipt
families, rather than a flag that exempts new records from checking.

Independent replay reconstructs declarations, assignments and intrinsic stores
from the real source program and actual activation. It checks missing arenas,
retargeted bindings/paths, borrowed RHS/receiver tokens, wrong epochs, repeated
loop occurrences, unrelated calls, and joins with several possible receivers.
Successful storage installs only the declaration's type view; the original RHS
observation remains unchanged. No presentation record issues permission.
