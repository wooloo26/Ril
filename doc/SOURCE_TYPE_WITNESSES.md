# Complete source type identity

`sema::model::Value.source_type_witness` shares an immutable, optional descriptor
containing closed source syntax and a canonical key. It preserves dimensions,
nested fields, callable modes and supported qualifications omitted by runtime
`Ty`. It grants no origin, freshness, disjointness, writable authority, resource
eligibility, Result inspection, lifetime, callback or termination evidence.

Witnesses come from checked ascriptions, constructors and complete source
expression schemas. A literal array without fixed ascription remains dynamic.
A dynamic view never acquires its backing node's fixed declaration identity;
empty `[0][2]int` retains its inner dimension from source syntax, without invented
element nodes. Joins retain metadata only when both canonical keys agree.

Actual generic binder witnesses accompany semantic substitutions through calls,
defaults and retained callable environments. Canonical TypeArguments, actual and
captured StaticArgumentWitness observations, and storage checks consume the same
schema. Core exports the key plus structured ArgumentKey; retained return
contracts export their captured schemas too. Unknown or resource-limited evidence
remains unresolved. Named callable state/effect bounds require frozen lexical
identity; a spelling alone never supplies it.

Type identity and callable call-site interfaces are separate. Written `T` leaves
preserve the actual Value's labels and defaults through nested containers and
retained returns. Explicit callable destinations retain the existing rule:
destination labels replace source labels by position, and source defaults are
not imported. Closed canonical syntax is never an implicit interface ascription.
Alias interface transport is checked against the independently normalized type
identity and changes no mode, obligation bound or provenance rule.

Payload-clone Option/Result/nominal/sum constructors clear inherited outer
metadata immediately. Complete wrapper schemas use actual payload descriptors;
constructor instances retain checked owner syntax in a private table. Projection
and Immut copy wrapping preserve frozen subtype syntax without changing the
existing graph/permission/borrow/copy algorithms.

Independent validation checks bounded closed/key consistency and resolved names
in current Values, nested payloads, retained contract DAGs, copy/default/closure
history, loans, resumption/scope-exit roots, and channel snapshots. The Core mapper
validates before canonical-key interning and propagates conversion failures as
NI. The separate StaticArgumentWitness validator checks syntax/key agreement,
registered symbolic binders, headers and complete actual/captured coverage.

Regression coverage lives in compiler `source_type_witness` (13 groups) and CLI
`source_type_witness` (nine executed fixtures), passing on Windows and Linux.
These tests cover fixed/empty nested arrays, dynamic views, helper/tuple/record
and retained callable transport, true effect specialization, constructor roots,
mode/dimension/permission/alias rejection, and mutated historical evidence. The
audit sources, binary hashes, before/after JSON, complete frozen-field walk matrix
and checkpoint limitations remain under `target/implementation-gap-audit/`.
