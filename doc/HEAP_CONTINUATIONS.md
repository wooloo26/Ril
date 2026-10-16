# Heap comparator continuations

`Heap::new`, `Heap::push` and `Heap::pop`, including builtin values assigned to
local aliases, expand into structured Core before selective CPS. Each comparison
is a real callback call. An admissible comparator may therefore handle a local
effect, use Parallel, or run scoped cleanup without crossing the synchronous
callback ABI. Heap identity, `len`, `peek`, stable ties and clone behavior keep
their existing opaque `PriorityHeap` representation.

The private operations under the NUL-prefixed `ril.heap.` namespace are `new`,
`begin_push`, `begin_pop`, `next`, `accept` and `commit`; none invokes a callback.
A `HeapMutation` object owns
the receiver, its complete original snapshot, the working entries, comparator,
sift phase and eventual pop result. GC traces every managed handle held by that
state. It is neither a source constructor nor a cloneable or foreign-encodable
data value. `next` requests the comparator and two operands; generated Core calls
it and submits its `Ordering` through `accept`. Replaying a pending request or
reply, or committing before the sift finishes, is an internal error.

Push compares the new child against its parent. Pop compares right against left
when both children exist, then the selected child against its parent. Equal
comparisons use the original `u128` insertion sequence number, preserving the
earliest equal element and the previous comparator invocation order. Generated
sift loops carry no source loop charge. Both normal and metered callback entries
are emitted when the program needs both conventions.

Only a successful final `commit` replaces the receiver's stored heap. Comparator
failure or a nonlocal exit abandons the working state and leaves the receiver's
entries and insertion counter unchanged. This is a receiver transaction;
observable work performed by callbacks is not rolled back. Before publication,
commit compares the entire receiver against the original snapshot, including the
comparator and insertion counter. It rejects a stale or reentrant mutation even
when nested work restores the same visible elements.

Semantic environment and effect restrictions are unchanged. Runtime construction
accepts a builtin comparator or a Managed, CPS or budget closure whose actual
environment is Unit or an empty record. A CPS label by itself is not an
environment-free witness. Capturing closures, retained handlers and unknown
environments remain rejected. Source tests also retain the existing rejection of
yielding or externally mutating comparators.

Heap operations inside `Div::budget` now retain the actual comparator's coverage
evidence. Construction, length and peek are finite primitives; they do not invoke
the retained comparator or require an additional comparison-coverage witness.
Construction still checks Order's existing finite, pure, environment-free
qualification, as required by STD. Its static signature probe contributes no
callback entry or transitive work to the active budget. A finite comparator using
Parallel can therefore be retained without executing Parallel inside a budget.

Push and pop require one exact receiver origin with a complete `$members` family,
no uncertain slots, one-object multiplicity and the actual `$compare` value. All
origin-choice branches must identify that same receiver. The comparator must
have an independently finite, environment-free target with no escaping handler.
Its static invocation records actual callback, local-handler, cleanup and
transitive coverage; the finalized `BudgetProof` carries that evidence into the
termination witness. Missing, joined, repeated or uncertain origins retain an
explicit provenance NI. Another heap's comparator cannot discharge it, and
restoring observed fields after an unknown write cannot repair the whole family.

Native threshold checks use the established sift trace: five pushes and five
pops perform twelve comparisons. Action entry plus those comparator entries
requires thirteen units; twelve exhausts. One comparison with a local handler
and `resume` needs four units including action entry; three exhausts. A builtin
comparator through aliases needs two units including action entry; one exhausts.
Creation, length and peek alone complete with one unit. These checks distinguish
actual callback charges from the uncharged internal sift loop. A diverging
comparator remains `E0534`, including at construction.

Windows and Linux each pass four runtime transactions, one private semantic
proof test, three compiler/Core regressions and eight CLI groups. Validation uses
fresh runtime/CLI builds, two Cargo jobs and two test threads. Runtime, runtime-api
and codegen all-target Clippy and the targeted compiler/CLI test Clippy pass with
warnings denied on each host. The final logs under `target` are
`heap-budget-runtime-{windows,linux}.log`,
`heap-budget-private-{windows,linux}-final.log`,
`heap-budget-core-{windows,linux}-final.log`,
`heap-budget-native-{windows,linux}.log` and the matching `clippy` and
`test-clippy` logs.

Runtime tests verify exact sift order with the transaction as the receiver's only
GC root, private-state restrictions, partial-pop rollback and complete snapshot
checks. The semantic test covers cross-heap, partial-choice, repeated-origin and
unknown-write counterexamples. Core tests cover ordinary and budgeted Heap calls,
the finalized comparator cause chain, absence of generated loop charges and
escaping-handler incompleteness. CLI groups also retain Parallel with stable ties
and clone, panic cleanup, static restrictions, aliases and exact budget thresholds.
The latent-comparator test includes a formal Heap parameter's passive length call
with no retained comparison witness.

The original
`target/scheduling-audit/heap-handled-native.json` is retained as the pre-change NI
report. The unchanged source now returns unit in
`heap-handled-native-after-windows.json` and `heap-handled-native-after-linux.json`
in that same audit directory.

The original `heap-budget-before.ril` and provenance NI report are preserved in
the audit directory; `heap-budget-after-{windows,linux}.json` accept that unchanged
source. The `heap-budget-maydiverge-after-*` and
`heap-budget-escaping-handler-after-*` reports preserve `E0534` and the escaping
comparator's provenance NI. The three numeric threshold fixtures are also saved
there; their assertions execute as part of the CLI suite on both hosts.
