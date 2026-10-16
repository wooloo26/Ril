# Scoped symbolic member identity: implemented contract and v30 acceptance

Status: v30 passes on Windows MSVC and Linux GNU. All three original inferred
symbolic sources pass Source, solved-facts replay, Core, native IR and actual
native execution; the older four scoped native fixtures remain unchanged and
also pass. All three new positives check pointer32/pointer64 static layouts;
native execution uses the supported x64 targets.

The full v30 compiler gate ran 25 Source targets per platform with 679 Rust
passes and one explicit ignored test, and compiler Clippy `--all-targets` with
`-D warnings` passed. Frozen native execution ran 17 test executables / 22 Rust
tests per platform, covering 49 distinct positive Ril sources / 53 entry
executions. All 19 hashed artifacts were unchanged. The ignored test, rejected
sources and NI guards are excluded from positive language/native counts.

Evidence is in `target/const-int-and-dependent-bound-full-source-{windows,linux}-v30.log`,
`target/const-int-and-dependent-bound-clippy-{windows,linux}-v30.log` and the two
`target/const-int-and-dependent-bound-native-{windows,linux}-v30-report.json` reports.
The new three-source adapter's actual output is in
`target/const-int-and-dependent-bound-native-linux-v30-record_bound_symbolic.log`
and `target/const-int-and-dependent-bound-native-windows-v30-record_bound_symbolic.stdout.log`.

The two-platform v22 first gate has now compiled the registered modules. The
old nested8/rigid5/scoped10 groups passed; new symbolic8 had two passing guards
and six failures. The original positive sources failed ordinary generic U
inference/selection before the new member proof could be accepted. A narrow
retry used explicit `first<U>`, `count<U>` and `read<U>` forwarding and still
failed in v23 because ordinary explicit named application is a separate NI.
These are retained historical failures; bounded input dependency inference and
the private numeric follow-up fixed the original inferred sources by v30.

## Repaired ordinary bound-input inference and historical inputs

The original legal sources remain in the repository, with their actual native
entry and value assertions unchanged. They have been restored as the primary
Source fixtures and pass v30; copies in `pending/` preserve the v22/v23 original
failure bytes and are historical regression inputs, not unimplemented inferred
cases:

| Source under `crates/ril-compiler/tests/fixtures/record_bounds/pending/` | Required final behavior | Observed first-gate gap |
|---|---|---|
| `scoped_symbolic_array_inferred.ril` | Accept, then execute `test_native` returning its assertion success | Return U belonged to the wrong function/invocation namespace (`E0301`) |
| `scoped_symbolic_empty_inferred.ril` | Accept, then execute `test_native` without inventing an empty-array U value | U was not determined through the required structural member (`E0344`) |
| `scoped_symbolic_callable_inferred.ril` | Accept, then execute `test_native` with the original callable interface | U was not determined through the required callable member (`E0344`) |

These original inferred sources now pass actual native execution on both
platforms; they are not negative tests. The v23
explicit retry still failed: ordinary named Generic application itself is NI
(`expressions.rs` constructor/standard dispatch). Preserve the three explicit
retry sources as `pending/scoped_symbolic_{array,empty,callable}_explicit.ril`.
They must also ultimately work, but are outside the current dependency-inference
change; explicit arguments must not be silently ignored. Preserve the v22/v23 failure logs at
`target/scoped-symbolic-members-first-{windows,linux}-v22.log`. Type/identity
checks must remain strict when the inference/actual-U scope substitution is
checked in any future extension. The bounded ordinary input-dependency and private numeric
follow-up accept and execute the three original inferred positives in v30; the explicit
ordinary named Generic application is still a separate pending implementation.

The bounded producer/replay design is now documented separately in
`ORDINARY_BOUND_INPUT_INFERENCE_DESIGN.md`. All acceptance/native results for this
new dependency batch are recorded in that document. The CLI adapter is registered
as `crates/ril-cli/tests/record_bound_symbolic.rs` after Source actually passed;
native execution passed on both platforms in v30.

## The concrete missing proof

An original parameter such as `({items:[0][2]U,..S},int)` names a complete type
coordinate under a genuine lexical `U` even when it contains no runtime `U`
element. Its array member cannot carry a *closed* `SourceTypeWitness`. The same
issue occurs for a promised member of `T:{items:[2]U,..R}` during universal
declaration replay. Erased `Ty::Array`/`Ty::Callable`, a raw annotation, or an
empty element iteration cannot provide this identity.

The extension consumes original declarations and existing frozen members. It
does not produce a closed witness, invent a `U` value, erase an opaque row,
settle hidden Result/copy duties, or authorize an access.

## Private staged API

The private implementation is
`crates/ril-compiler/src/sema/record_bound_validation/scoped_members.rs`.

| Entry | Required evidence | Result |
|---|---|---|
| `declared_bound_probe(projection, site)` | Actual `ProjectionSite.base` from the existing bounded source walk; actual owner/context/source observation; genuine bound; complete original argument table; every material `T` path; actual readonly parameter reception and exact entry epoch | Private `DeclaredBoundProbe` |
| `declared_probe_member(reception, label)` | Original bound field under its genuine scope; one existing stored member; full type/shape/callable replay | Private `MemberIdentity` bound to that snapshot and member reference |
| `scoped_original_formal(identity)` | Registered identity arena occurrence; real callee header and all `T` paths; exact original formal/header/root/ancestor replay for every occurrence; equal complete source keys and exact entry epochs | Private `ScopedOriginalFormal` containing every canonical original/actual whole-entry pair |
| `scoped_formal_member(reception, ordinal, side, label)` | A covered canonical occurrence and its original header field; existing stored member; full type/shape/callable replay | `MemberIdentity` for that exact canonical snapshot/member |
| `scoped_check_member(reception, check, label)` | Registered actual bound-check occurrence, same required/context/path/epoch, complete frozen snapshot equality to the canonical argument, genuine matching rigid header/scope | A new `MemberIdentity` for the specific check snapshot/member |
| `require_member_identity(identity, snapshot, stored, field, scope)` | Exact snapshot/member occurrence, label/mutability/full key/full namespace | Successful type-only replay |

The stages and member-token fields are private. There is no constructor taking
an arbitrary raw header and snapshot. Both final member constructors run the
complete member replay before returning their token.

`scoped_check_member` matters because `GenericBoundCheck.actual` is a separately
frozen copy of `CopyInvocation.arguments`. A token for the canonical argument
must not simply be reused by NodeId or span. The bridge first checks the entire
frozen value, all nodes/fields, relations, lengths and fixed flags with the
existing `same_snapshot`, and then selects and binds the actual member reference
in the registered check snapshot.

## Exact registration hooks

1. The private module is registered in `record_bound_validation.rs`. Narrowly expose
   `original_formal_view` and `every_scoped_occurrence_is_material` from
   `scoped_identity.rs` as `pub(super)`. No public arena/Core/ABI change is needed.
2. Extract the existing prefix of `replay_scoped_source_identity` into
   `scoped_original_formal`; do not execute the old prefix and the new prefix
   consecutively. The prefix must finish **all** real `T` paths before any
   stored-member fallback runs. Keep the current identity ID/uniqueness/coverage
   checks in `scoped_source_coverage`.
3. Keep `projections()`' existing `sites = projection_sites(facts)?` walk and use
   its matched `ProjectionSite.base` directly. After genuine source observation,
   cause and readonly reception checks, the universal bound-member path may
   obtain `DeclaredBoundProbe`. Do not add a caller-built `Expr` ingress, reset
   the source-walk budget per member, or expand the channel index API.
4. In `stored_schema`, change only the branch rejecting a missing complete
   array/callable witness. A caller must supply an explicit staged member token;
   `None` retains the existing rejection. Closed witnesses still undergo their
   full existing checks, even when a staged token is present. Retain every
   ordinary field, slot-mode, shape, row-tail and row-lacks check.
5. For scoped identity replay, original and actual canonical schemas receive
   tokens from the matching covered occurrence and side. For `schema(check)`'s
   rigid branch, use `scoped_check_member` to bind the separately frozen snapshot.
   A projection receipt cannot stand in for an absent `T` projection AST.
6. The producer-only candidate helper is in
   `checker/record_bounds/symbolic_members.rs`. Use it only after obtaining the
   real original formal/header anchor and existing stored field, for a missing
   array/callable closed witness containing a genuine scoped `U`. Retain exact
   field semantic type, full original key, and old closed-witness guards.
   `known_field_conflict` may use `definite_member_conflict` for known coordinate
   differences beneath symbolic members. Different `U`/`V` alone remains an
   unresolved type equation, not an independence proof.

The staged proof is local to the immutable facts being independently replayed.
It must not be stored in the shared source syntax index or reused across edits,
invocations, allocation epochs, or newly mutated fact sets.

## Conservatively retained obligations

- The target `T` still appears only along exact material tuple/record paths.
  Arrays/maps/empty containers containing `T`, type-only paths and missing input
  tables are not enabled by this member proof.
- Every generic coordinate names a real nearest Type binder. Fixed dimensions
  are normalized target integers, including inner dimensions below outer zero.
- Full callable modes and explicit supported qualifications remain in the key.
  The actual signature, return descriptors, original namespace, callable IDs,
  and bound descriptors must agree. A descriptor from another creator or a
  receiving substitution still needs its own complete transport proof.
- `symbolic_member_sources` traverses only existing frozen sources/payloads and
  rejects a generic value whose possible reference sources were erased. Empty
  arrays do not create element observations or settle Result/copy obligations.
- Nested opaque rows, unknown computed dimensions, named state/effect scopes,
  retained/shared/mutable reception and cross-recent/older source transport
  remain outside the initial candidate range.
- Ordinary `CallerBound` composite forwarding from an ancestor generic bound
  cannot borrow the rigid-record header entry. If needed, it requires a separate
  genuine declared-bound receiving path; it must not trigger a raw-header
  fallback or be declared complete by the two initial entry constructors.

## Source and mutation acceptance

Six fixtures registered in `record_bound_symbolic.rs` cover `[2]U`, empty `[0][2]U`, `fn(U)->U`, known inner
dimension mismatch, different real binders and readonly element writes.
The candidate/dependency producer includes ten pure tests; the Source target's
twelve groups pass on both platforms, including the new own-static-row deletion,
captured-row replacement and numeric input-conflict checks. The binder/readonly nonauthorization group permits
retained NI and is explicitly not a positive language or native conformance case.

Source/solved facts/Core/native-IR checks and actual native execution passed for
the lawful sources. Mutations independently delete or
alter original/current argument entries, a secondary `T` path, original root
observations/source events, header scope/binder, fixed dimensions below zero,
member identity/mutability, callable modes/qualification/returns, generic origins,
Result membership and the exact check-snapshot bridge. Missing tokens and changed
probe metadata must never make required proof coverage vacuous. Source failures,
NI, crashes or timeouts cannot be counted as successful positive cases.
