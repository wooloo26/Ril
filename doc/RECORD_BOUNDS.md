# Structural record constraints

A constraint such as `T: { id: int, ..R }` supplies a structural view of `T`.
The value retains its genuine generic binder identity. The view neither closes
`R` nor creates a new object, independent origin, writable path, immutable graph,
or Result inspection receipt.

## Declaration and application evidence

`sema::record_bounds` separates four arenas:

- `GenericRecordBound` identifies the actual declaration and parameter index,
  original syntax, scoped field keys, mutability, and row tail.
- `BoundRowDeclaration` identifies an implicit residual or a genuine declared
  Type parameter with a row role. Shared tails use the same lexical identity
  and accumulated absence constraints. An implicit `R` is never inserted as a
  fictitious generic parameter.
- `GenericBoundCheck` binds a requirement to a real invocation, argument index,
  selected type path, activation, allocation epoch, and frozen argument graph.
  A closed actual needs its complete source-type witness. Caller bounds and
  rigid open parameters preserve their unknown tail.
- `GenericBoundProjection` records the source and output graphs, field,
  requirement, call context, access category, epoch, and cause.

The application solver instantiates flexible residuals once per invocation and
solves all constraints together. Two arguments sharing `R` cannot independently
select different remainders. Exact field keys preserve array dimensions and
callable interfaces even when the runtime representation erases those details.
Already selected rows must agree with the remainder; a missing complete witness
is an outstanding proof obligation.

`provenance_lower::record_bounds` transports these identities and snapshots to
Core. It does not decide permissions or repair an unresolved application.

## Independent validation

`sema::record_bound_validation` rebuilds declaration headers and the nearest
lexical namespaces from actual source declarations and callable ownership. It
checks scoped keys, row equations, actual argument coverage, and stored edges.
The declaration and an application cannot validate each other merely by
agreeing on forged metadata.

Projection reception uses real invocation expression and parameter binding
identities. Writable reception also uses the corresponding loan. Read reception
has no mutable loan, so its evidence instead consists of the actual parameter
binding, argument snapshot, mode, activation, and epoch. Declaration probes have
no caller activation; ordinary calls must match their actual caller scope.
Source spans locate syntax and diagnostics; they do not identify objects or
grant authority.

## Unknown row members

An ordinary formal open row carries a real opaque member-family edge. It retains
possible Result duties and unknown aliasing. A symbolic `keyof` projection can
carry only a genuinely borrowed opaque family as a possibility: the compiler
checks the matching row edge and its formal origins and producer identities.
A known-field Result does not qualify merely because it also has an outside
owner. The projection preserves all possible origins and duties, clears definite
return and outer-result membership, and grants no tag inspection.

Static Result flow likewise keeps the complete value's generic identity. Its
`BoundRecord` shape exposes guaranteed fields but records whether the remainder
is open. Reading a guaranteed field can use that field's graph. Transporting the
whole open shape still requires an opaque-family proof; it cannot be treated as
an empty closed record. Immutable bound environments are shared by `Arc` and
follow lexical captures and callable entry/return.

## Current component gates

The first integration gates exposed overly strong validator assumptions about
read reception, caller scopes, symbolic substitutions, and inherited roots.
The failed logs are retained. Windows v6 passed all five source groups, all four
mutation groups, six static-argument groups, two layout groups, three numeric
groups, and seven foreign-schema groups (27 total), including the byte-preserved
SPEC projection and open-tail forwarding. Separate Windows gates passed six
static-key groups and six independent validator units, including nearest-name
shadowing and the distinction between opaque and known-field Result producers.

The static bound-environment integration preserved all 36 existing static loop
and Result groups on Windows and Linux. This does not establish new constrained
meta acceptance: complete actual type reception and application selection are
being integrated, and the meta constraint guard remains in place. Four new
static bound/Result source groups are being integrated with actual type
reception. The ordinary component checkpoint has since passed five source
groups, eight mutation groups and six static-key groups on both Windows and
Linux. All nine ordinary native programs also executed successfully on both
platforms. These are component gates, not full-workspace acceptance.

The literal-coordinate gate adds actual syntax selection for string, raw
string and escaped labels. Independent replay requires the corresponding key
expression in the same invocation, its string sort, exact label and source
cause, together with the existing stored-field projection proof. The key grants
no permission. Mutation checks reject deleted key observations, altered labels
or sorts, and deleted field observations. Another group fixes a declared Type
row from a second actual argument and rejects consistently forged substitution
metadata selecting a different remainder. A runtime string parameter remains
an invalid computed coordinate. The native gate includes all three literal
forms and the declared-Type-row example, in addition to the five original
ordinary programs.

The latest component logs are `target/record-bound-literal-source-{windows,linux}-v1.log`,
`target/record-bound-literal-keys-{windows,linux}-v1.log` and
`target/record-bound-literal-native-{windows,linux}-v1.log`. Both runtime static
libraries were freshly built for that execution gate. Earlier failed compile
logs remain evidence of integration attempts, not passed tests.

Collection and type-only selected paths, fixed captured rows without creator evidence,
independent replay of safe bound-projection facts, and recursive or
quantified Result transport need their own complete evidence. They remain
explicit incomplete paths until that evidence is implemented; an unknown source
is never a positive proof.

## Exact nested products

Nested tuple and named-record selections retain the whole actual argument
snapshot. The source parameter type determines the genuine `T` position, and
the stored tuple/field edge determines the selected value. Independent replay
rebuilds both paths and the selected complete type identity. Repeated `T`
occurrences must have the same complete type; shared objects keep their actual
origins. Existing nested formal objects receive their declared field schemas
and fixed-storage promises before invocation entry.

Readonly reception replays the parameter root and every intermediate product
expression from the frozen argument graph. Each actual expression and computed
coordinate must exist in its invocation, and each projection must have the
corresponding source/stored causes. The replay retains the full value metadata,
including loans, publication, retained obligations and copy dependencies. It
does not treat a child as a fresh parameter or restore authority through its
field type.

The first Windows nested gate passed six groups and correctly rejected the new
readonly fixture for declaring unused mutable authority (`E0527`). The fixture
then exercised its declared write before creating its view. The final component
gates passed eight nested source/Core/mutation groups and all thirteen previous
ordinary source/mutation groups on both Windows and Linux (21 groups per host).
All nine new native programs executed successfully on both hosts, including
two different bounded types in one tuple sharing one residual row.

The evidence is `target/record-bound-nested-source-windows-v3.log`,
`target/record-bound-nested-source-linux-v2.log`,
`target/record-bound-nested-native-windows-v2.log` and
`target/record-bound-nested-native-linux-v1.log`. Native execution used freshly
built CLI/test binaries and runtime static libraries; compiling tests without
running them was not counted as native acceptance. Earlier dependency compile
failures remain in their original logs. This checkpoint covers exact tuple and
field selections and CallerBound forwarding, not nested rigid-parameter schemas,
collection/type-only selections or writes.

## Nested rigid formals

The rigid formal registry now retains multiple structural schemas for one real
parameter. Registration walks only existing tuple and record children. Each
schema keeps the actual declaration and parameter index, the original open
record type subterm, its lexical scope, complete known fields and its rigid row.
Independent replay locates that source subterm in the real parameter header and
checks the full field family, mutability, semantic types and row identity before
replaying the stored graph. A shared row remains open; known fields cannot make
it closed or provide additional absence premises.

The frozen Windows component gate in
`target/rigid-bound-source-frozen-windows-v2.log` passed five Rust groups. This
includes three lawful tuple/field/shared-row programs through Source, Core and
native IR; parameter/scope/type-subterm and row-premise mutations; and real
missing-member/mutability type errors. The fifth group separately confirms an
outstanding complete-source-identity obligation for a lawful fixed-array
fixture. That `NotImplemented` outcome is a proof guard and is **not** counted
as accepted Ril conformance. Linux subsequently passed the same five groups
and all twenty-one previous ordinary/nested groups in
`target/record-bound-rigid-source-linux-v1.log`. The three Linux programs also
executed successfully using a newly built frozen CLI/runtime in
`target/record-bound-rigid-native-linux-v2.log`; the compiler and runtime hashes
are recorded in `target/rigid-static-io-linux-v2-hashes.txt`. Windows also executed
the three programs successfully in `target/record-bound-rigid-native-windows-v4.log`
after the shared frozen CLI build in
`target/optional-rigid-static-native-build-windows-v4.log`. Native execution is
therefore verified on both platforms for these three primitive-field schemas;
it does not cover the outstanding fixed-array fixture.

The historical fifth-group NI guard above has now been replaced by actual
Source/Core/native-IR acceptance of the unchanged `nested_rigid_fixed.ril`.
The new scoped-source component passes ten groups on both platforms in
`target/record-bound-scoped-source-frozen-windows-v4.log` and
`target/record-bound-scoped-source-frozen-linux-v4.log`. These verify four lawful
fixed/empty-inner-array/callable/immutable-field programs, fixed layout checking
under pointer32 and pointer64, concrete dimension/callable-mode type errors,
and independent mutations of coverage, entries, paths, source tokens, keys and
epochs. The subsequent integrated v9 Source run passed 590 Rust tests with one
explicitly ignored test on each platform; neither ignored work nor NI guards
are accepted language cases.

Linux subsequently executed all four new scoped programs successfully in
`target/scoped-write-template-native-linux-v9-record_bound_scoped.log` using the
fresh v9 CLI/runtime. The complete ten-executable native report is
`target/scoped-write-template-native-linux-v9-report.json`; compiler, runtime
and all ten test-executable hashes match before and after execution in the
corresponding `-hashes-before.json` and `-hashes-after.json` files. The Linux CLI
SHA-256 is `725054d1e8ff7fcc4361dc5b478cbd8df6c21a04e246d47fe4122befe2d70458`.
Windows also executed all four new scoped programs successfully in
`target/scoped-write-template-native-windows-v9-record-bound-scoped.log`.
Its complete ten-executable report is
`target/scoped-write-template-native-windows-v9-results.json`; all twelve frozen
artifact hashes likewise match before and after execution. The Windows CLI
SHA-256 is `234958D437DEA03B2FFA25AFA1EC34607041DE9CB141148A392C0E0A418A52BA`.
The scoped fixed/empty-inner-array/callable/immutable-field batch is therefore
verified through actual native execution on both platforms. This status does
not count the separate rejection/NI checks, ignored Rust test or unregistered
symbolic-member drafts as executed positive language cases.

## Complete scoped source identities

`ScopedSourceIdentity` is a separate identity arena and is transported intact
into Core provenance. It does not manufacture a closed `SourceTypeWitness`
for a rigid row, grant access, establish freshness or assert independence.
Each real `T` occurrence selects an existing tuple/record child from the actual
callee's complete frozen argument entry. Its original formal anchor selects
the same object from an ancestor's whole frozen entry and the corresponding
real parameter-header subterm. The descriptor retains the source namespace,
genuine row binder, full normalized key, source cause and actual invocation.

Independent coverage starts at the real callee generic and parameter headers,
including every material `T` occurrence. It checks whole-entry arity before
selection, and does not skip obligations when a declaration-probe or ancestor
flag changes. Missing or extra certificates, erased entries, deleted original
observations and missing stored paths fail replay. A formal root is anchored
to a real parameter Name token and its actual expression occurrence. Each
parent edge is checked against a real Call/callee token, the original call
event and its named-target observation, rather than agreeing owner metadata.
Readonly reception, participants, stored fields, row absences and fixed-storage
invariants are reconstructed separately from the original header and graph.

Array keys retain every normalized dimension, including inner dimensions under
an empty outer array. Unknown computations remain obligations; mere equality
of symbolic dimension strings is insufficient. Callable parameter modes and
qualifications and `Immut` wrappers remain explicit. Transparent aliases are
normalized consistently in semantic field views without erasing those complete
keys or changing nominal/opaque identities. A mismatch in a complete known
field is a concrete type error; unrelated opaque rows remain unproved equations.

An actual invocation may receive a closed record despite its enclosing open
formal annotation. In that case, only a genuine structurally bounded `T` can
select an existing material product child and consume its complete closed
structural schema. All `T` occurrences must have the same complete identity;
the enclosing tuple is not made closed and no element is invented for an
empty collection. The independent bound application replays the entire frozen
actual graph and its selected child's closed schema.

The current scoped transport requires exact equality of original and current
allocation epochs. A reused recent/older NodeId alone is not an object-identity
proof. Cross-recency, unconstrained-generic and array/map/type-only selections
retain their own obligations; a structural bound does not waive them.

The implemented rigid-row cases currently require complete closed identities
for known array/callable members. A genuine symbolic `U` nested inside such a
member still needs its separate original-header member proof. Unregistered
symbolic-member drafts and fixtures are being prepared and are not included in
the accepted Source or native counts above.

## Further evidence contracts

Empty arrays and maps require a separate type-level selection from the whole
source-type witness: an empty container supplies no `T` object. Present members
still need their own physical-storage and authority checks.

Writes need actual assignment observations containing the source occurrence,
pre-write receiver, old field, incoming value, scope, invocation, epoch and
corresponding write access. The assignment's member mutability and received
write loan must be independently replayed, followed by the existing exclusive
access, stored-authority and Result-transfer checks. A read projection of the
old field cannot authorize the assignment. The direct mutable scalar-assignment
contract is described in [RECORD_BOUND_WRITES.md](RECORD_BOUND_WRITES.md).
Readonly scoped type identity is not consumed as mutable-access evidence.
