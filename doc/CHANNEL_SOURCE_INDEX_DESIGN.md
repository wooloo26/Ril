# Channel source lookup and proof budgets

The private lexical source index is registered in
`sema/channel_repetition_validation.rs`, with its implementation and tests in
`channel_source_index.rs` and `channel_source_index_tests.rs`. Guard
representation, public facts, Core, ABI and proof limits have not changed.

The v11 same-source compiler gate passes **605 tests, with one explicit audit
ignored, on each of Windows and Linux**. This includes all eleven source-index
tests, the previous Source and mutation gates, and the static Result-map gates.
Logs are `target/source-index-and-result-maps-integration-{windows,linux}-v11.log`.
The v11 frozen native gate also passes on both platforms: twelve test targets
execute 38 distinct positive sources through 42 entry executions on each host.
That total includes the new original-source adapter's three entries. The CLI,
runtime and twelve test executables retain all fourteen manifest hashes across
each gate; native execution did not rebuild them.

There are two different retained failures. They must not be conflated.

| Preserved source | Original failure | Current actual Source result |
| --- | --- | --- |
| `optional_callback_source_controls_scope_budget_before.ril` | Event 657: bounded inactive event intersection is unavailable. | Still explicitly NotImplemented; no normal Core lowering or native execution. |
| `optional_callback_source_controls_split_work_budget_before.ril` | Channel execution-bound analysis exceeds its work bound. | The byte-identical source now verifies through a real Session and Core lowering. |

Both sources, their hashes and raw JSON are retained in the channel-message
audit. Replaying the second source with the same frozen compiler produces a
byte-identical JSON result with that old compiler. The second source is now
preserved as
`crates/ril-compiler/tests/fixtures/channel_message_optional_callback_source_index_checked.ril`,
SHA-256 `601566E3663EC15B261EEDFE865E3EC8A3D195F4551EEB4335B25D254ADA4227`.
The first is
`channel_message_optional_callback_scope_budget.ril`, SHA-256
`E50829579B8E6185754B6D04B714503D538CE7683E6F5465388F0C4E1CD8987F`.
The smaller previous native composition remains a separate source and cannot
stand in for either preserved input.

## Proof intersection

`channel_message_validation::Replay::step` first forms the active event guard,
then computes `case.guard AND NOT event.guard` for the inactive continuation.
The original event-657 diagnostic comes from that latter `and`, after `not`
succeeded. It is an actual guarded-custody proof operation, not an AST lookup.

`ChannelGuard::and` may return unavailable because of operand validity, pair
work, literal count, output term count or normalization work. The preserved
diagnostic identifies this phase; it does not identify the internal counter.
No claim about the exact term sizes or quota is made without instrumentation.
The later frozen v15 test-only sample identifies absorption at work
65,538/65,536: the case guard and event complement are the same 36 singleton
clauses. The intersection is nonempty, and its ten Transport references are
absent from the case's executed set. The exact-empty oracle is therefore
inapplicable; an exact structural-idempotence optimization is a separate
central guard change. Its first complete-source gate reaches a further NI at
record661; exact raw-clause subset absorption then reaches record858. Witnessed
physical term subsumption passes the v20 six private/seventeen algebra tests,
but the unchanged entire source now reaches record957's distinct replay-state
bound and still reports NI. It does not yet verify or execute natively. See
[the measured sample](CHANNEL_GUARD_BDD_DESIGN.md).
Its registered test now explicitly requires that NI as a non-authorization
regression. That Rust test passing cannot count as the original language input
passing; its complete Source/Core positive target stays unregistered/pending.

A syntax index cannot make this intersection valid or pay any debt. Future
factoring, guard representation or state compaction needs its own soundness
work. Completed-scope history cannot simply be discarded: retained booleans,
producer aliases and task order can still refer to it. The original single
entry with nine scopes remains NotImplemented.

## Repeated source work

The execution reader already caches selected application bounds by physical
CopyCallEventId. Its `syntax(owner, span, call_only)` nevertheless scans the
function/closure registry and walks the same frozen lexical body repeatedly.
`execution` also scans all InvocationCall rows to find each named ancestor's
caller links. These operations charge the source reader's work counter.

The registered private optimization introduces a lazy index per real lexical
CallableOwner. Index construction walks the same body, signature-where items
and defaults as the current reader, records expression occurrences and their
pure syntactic loop bounds, and preserves all ambiguity. It does not descend
into a nested named function or lambda body under the enclosing owner.

The lookup key includes the complete owner kind/identity, file/start/end span
and query role (any expression versus actual Call). Different owners cannot
borrow equal numeric spans. Multiple matching source expressions stay
ambiguous; missing or unclosed source stays incomplete. Closures with the same
site must have one congruent lexical body, otherwise indexing must refuse the
proof. Building indexes only on demand avoids spending the transport budget
on unrelated declarations.

Each index construction and lookup still consumes work from the unchanged
65,536-operation source budget. A separate lazy read-only row index retrieves
all InvocationCall records by their actual InstanceId;
the reader must still validate and traverse the matching records. This is an
index of evidence, not a cache of a caller's proof result.

Do not memoize selected callees, formal argument aliases, borrowed authority,
optional identities, Result generations, callback entry, iteration counts,
defaults or custody by source span. These facts depend on actual invocation
observations and frozen inputs. Keep application identity/context checks and
the existing per-application cache separate from lexical syntax lookup.

## Registered change and verification scope

The change is private to channel repetition validation. It needs no
SemanticFacts, Core, ABI or lowering changes. The original walker remains under
`cfg(test)` for differential comparison. The tests compare actual occurrences
and bounds, and exercise owner/role/file separation, ambiguous expressions,
nested named functions and lambdas, defaults, duplicate definition/site
headers and bodies, exact application IDs, every caller row, failed partial
index publication and charged repeated lookups.

The first integrated v10 run had one test-only failure: the nested-function
test searched for the written name `nested`, although static lexical
elaboration had renamed its `where` declaration. The corrected test selects
the actual registered function using the enclosing frozen `where` declaration
and lexical owner, then queries its real DefinitionId. Production indexing was
unchanged. The narrow Windows gate subsequently passed all eleven tests in
`target/channel-source-index-nested-anchor-windows-v1.log`; both v11 full gates
also pass them.

`crates/ril-cli/tests/channel_source_index.rs` retains the original 601566
source verbatim and defines three independent native entry tests. Each uses a
fresh CLI subprocess and temporary directory, a 20-second deadline and process
tree cleanup. CLI success, `status=executed`, `runtime=returned-unit` and
`exit=0` are all required. This adds one distinct source and three entry
executions, containing nine concrete input routes; it does not change the
previous seventeen-source/nineteen-entry channel adapter or run the E508 gap.
All three original-source entries actually execute on each platform in the
v11 gate. Their per-target logs are
`target/source-index-and-result-maps-native-linux-v11-channel_source_index.log`
and
`target/source-index-and-result-maps-native-windows-v11-channel_source_index.stdout.log`;
the Windows stderr companion and both gate manifests are retained separately.

All previous selector/ownership/source mutation gates remain green. The real
Session/Core test now proves that reduced source traversal admits the retained
split composition. A separate real Session test still requires the original
event-657 source to report its proof-intersection NotImplemented result. The
next guard-algorithm and shared source-facade proposals are described in
[Bounded channel guard proofs](CHANNEL_GUARD_BDD_DESIGN.md); they are not
registered by this source-index batch.
