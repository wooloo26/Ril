# Ordinary structural input Type dependencies

Status: v30 acceptance is complete for this implemented range on Windows MSVC
and Linux GNU. The three original inferred positives pass pointer32/pointer64
Source checks, solved-facts replay, Core and x64 native IR, and execute their
original native assertions on both platforms. All twelve Source test groups
pass, including the repaired true expected-only NI boundary, own-static-row
mutations and the numeric input-conflict check. The old scoped fixtures are
unchanged.

The full v30 compiler gate passed Clippy `--all-targets -D warnings` and 25 Source
targets (679 Rust passes / one explicit ignored test) per platform. Frozen native
execution passed 17 test executables / 22 Rust tests per platform, representing
49 distinct positive Ril sources / 53 entries, with all 19 artifact hashes stable.
These are the actual implemented acceptance cases, not full-language corpus
completion; rejects, NI checks and the explicit ignored test are excluded from
positive language/native counts. Source/Clippy evidence uses
`target/const-int-and-dependent-bound-{full-source,clippy}-{windows,linux}-v30.log`;
native evidence is in the corresponding
`target/const-int-and-dependent-bound-native-{windows,linux}-v30-report.json` files.

The v22 and v23 first gates preserved nested8, rigid5 and scoped10 but rejected
the three new symbolic sources before their new member proof could complete.
`infer_named_arguments` selected `T` from `(T,int)` and `(T,T)` while `U` appeared
only in T's structural clause. `infer_static_keys_and_bounds` skips registered
structural bounds. Therefore U was still missing when the callee's return was
checked or its E0344 was emitted; a late result meta could also keep the callee's
UID instead of the caller's rigid U. The explicit retry did not solve this:
ordinary named `ExprKind::Generic` still reaches the standard-dispatch NI path.

## Registered private hooks

- `checker/record_bounds/dependencies.rs` is called after the actual schema and
  every T occurrence have matching complete identities, before rebuilding the
  expected selected fields. It matches original field keys and the actual real
  syntax structurally: dimensions, callable arity/modes/qualifications, labels,
  mutability and constructor shells must agree before selecting any leaf.
- Only this callee's unselected Type U with no own bound or an explicit Type
  bound is flexible. Structural/key/value/constructor constrained binders, T and
  row binders are excluded. Existing input choices are checked, never replaced.
  The initial supported leaves are closed ordinary scalars with an actual
  syntax/key witness, or a genuine caller U with its original UID. A composite
  leaf needing an unavailable exact projection remains NI.
- Candidate maps are local. The entire bound application is transactional:
  later field/type/key/shape/row failure rolls back substitutions, witnesses and
  row selections, and no partial bound-check set is committed. `calls.rs`'s
  existing missing-binder recomputation runs after that transaction and before
  constructing the actual body return context.
- `record_bound_validation/dependencies.rs` independently reconstructs an open
  U equation from the real unconstrained/Type callee header and the complete
  original source descriptor. It first stages real ancestry/root/readonly
  reception, full entry arity, every T path and exact epochs; it never calls
  `schema` or `application_header` recursively. It checks all known key
  coordinates and every repeated U, and requires one consistent selection across
  this actual invocation's checks. A producer substitution is the proposition,
  not the proof. The complete stored schema/shape validation remains mandatory
  afterward.
- The new local receipt permits only a rigid caller-U equality when an existing
  effect argument has no closed syntax/key. Closed scalar arguments retain their
  existing full static-argument checks. No access, clone, independence, Result
  inspection, callable defaults, row closure or freshness is authorized here.

## Gate and retained cases

The original inferred three fixtures are accepted native positives. Their
`*_inferred.ril` copies in `tests/fixtures/record_bounds/pending/` preserve the
historical v22 failure inputs; they no longer represent an unimplemented inference
gap. The separate `*_explicit.ril` retry inputs remain pending ordinary explicit
named application cases, never desired rejects.
The CLI adapter is now `crates/ril-cli/tests/record_bound_symbolic.rs`, registered
after actual Source/Core acceptance. Its three original programs actually execute
on both platforms in v30; their per-target logs are
`target/const-int-and-dependent-bound-native-linux-v30-record_bound_symbolic.log`
and `target/const-int-and-dependent-bound-native-windows-v30-record_bound_symbolic.stdout.log`.

The tests include real caller UID selection and rigidity, a fixed-dimension
conflict despite identical erased array types, and independent mutations of a
dependent substitution to another genuine binder, actual member deletion,
complete callable modes and empty-inner dimension metadata. These tests pass in
the v30 unified gate. Existing NI guards stay nonauthorization evidence,
not positive language/native passes.

## Private numeric preparation follow-up (accepted in v30)

`numeric_application.rs` originally classified U as expected-only before argument
evaluation because the semantic parameter template contains T, not the U in its
bound. `calls.rs` also validated the prepared application before the bound
transaction selected U. Merely moving validation would leave the first NI.

The private follow-up records the candidate through existing
application target/event/templates/substitutions and recomputes its deferred set
at validation. Declaration reachability is not a proof. Before entering the body,
after the full bound transaction, a deferred choice must consume that exact
invocation/source-event's committed GenericBoundCheck, its original whole-entry
snapshot, complete field equation and closed scalar witness, and its real own
static-argument position. Expected numeric and actual input choices must agree;
an int input cannot be overwritten by an f64 receiving context. A failed/missing
receipt leaves the application Invalid, not Frozen. True expected-only instances
without a material structural input retain their separate NI boundary.

No public numeric structure/arena was changed. The application is still private
to Numeric State; the resulting existing Source/bound/static-argument evidence
continues through independent solved-facts replay. The own-static-row validation
now fails locally on missing/misplaced rows or a captured replacement, even
though the global static-argument coverage validator already enforced that table.
The numeric type-conflict and repaired true expected-only boundary cases pass
both platforms in v30. Parser rejection is not the boundary's pass criterion.
The original ARRAY positive is unchanged and actually executes on both platforms.

## Remaining implementation boundaries

Ordinary explicit named `ExprKind::Generic` is still NI and must acquire an
actual caller-scope/type-application contract before it is accepted. Composite
leaf U selections requiring unavailable full source projections remain NI;
callee binders with their own structural/constructor/key/value constraints are
outside this narrow dependency solver. Ancestor `CallerBound` composite forwarding
still needs a separate genuine receiving proof and cannot borrow the rigid-header
entry. Named state/effect bounds and cross-recent/older source transport retain
their prior obligations. None of these boundaries is completed by the v30 green
range, and none can be relaxed using an erased Ty or backing cardinality.
