# Effect specialization evidence

This document describes the frontend evidence boundary. The observations below
are not, by themselves, a native specialization certificate. A planner must prove
complete coverage and create explicit owner and operation mappings. The current
closed direct-call implementation and its remaining boundaries are recorded below.

## Declaration and binder identity

A named generic binder belongs to `(DefinitionId, parameter index)`. Its source
span and written name are diagnostic information. Repeated activations of one
declaration retain that identity; separate foreign-default instances can contain
different declarations at the same source span. Their binders and Core TypeIds
must remain distinct. Local declaration verification is keyed by DefinitionId.

`GenericBinder.definition` carries this owner through semantic facts and Core
provenance. `lower.generic_types` uses the typed owner/index pair. An inherited
outer binder keeps its original declaration owner, while a same-named local
binder replaces only the lexical name lookup.

## Actual invocation partitions

The frontend reuses `copy_templates::InstanceId` and `CopyInvocation` for every
named invocation. This is one shared identity chain, not a second interpretation
of call order. The record supplies target, parent, declaration-probe status,
completion status, and frozen argument/result evidence. `invocation_calls`
additionally retains the exact caller CallableOwner, including closure owners.

`EffectInvocation` references that identity and records each static argument's
binder owner/index, normalized full TypeExpr witness, and structural ArgumentKey.
Captured outer arguments are separate. Missing witnesses and unknown captured
binders remain explicit. They cannot be reconstructed from erased value-level Ty
or runtime arguments. An absent completed observation is not an empty effect row.

`invocation_expressions` associates each ExpressionFact with both its dynamic
named invocation and lexical CallableOwner. These can differ while an outer
handler arm runs. Handler operation targets and post-resume expression facts are
included. The complete Value remains in the referenced expression fact; no
capability, copy dependency, Result producer, or loan evidence is discarded.

`invocation_witnesses` records actual writes of numeric contextual types, implicit
unwrap and sum-projection evidence, static-key checks, handler registrations, retained-handler
selection, and finite-budget proof. A budget witness is captured before merging
the global source-span summary, and a retained-handler witness is captured before
merging other invocations' selected handlers. Global span tables are not fallback
evidence for a missing invocation partition.

## Requirements for a native certificate

A planner must establish all of the following before lowering a specialized body:

- A canonical target declaration, complete closed own and captured static
  arguments, and a completed checked invocation. Nongeneric declaration probes
  legitimately contain closed calls; a probe ancestor alone does not disqualify
  such a call. Unresolved generic dependencies still do.
- Exact lexical-owner/site selection of every operation and named-call target
  required by the body. A performed-operation set alone is insufficient.
- Coverage of all emitted syntax, including branches skipped by constant
  evaluation, omitted defaults, local declarations, handler arms, and callbacks.
  Template evidence plus certified substitution can provide coverage; the absence
  of an actual observation cannot.
- Agreement among every observation of the same canonical instance. Conflicting
  operation, callee, literal type, unwrap, or static-key evidence requires a
  narrower instance key or explicit NI.
- Explicit remapping for function definitions, lambda sites, handler sites,
  retained recipes, and every nested owner reference. Reusing a source span as
  an owner, or selecting the first operation seen there, is invalid.

Defaults are evaluated before the named body invocation is entered. Their
expressions therefore retain the caller invocation together with the default's
logical callable owner. Supporting them requires an explicit default-use edge
or independently complete template substitution; they must not be included by
assuming that the callee's body interval contains their evaluation.

Core specialization records are traceable mappings, not new source authority.
Ordinary reception, borrow exclusion, cleanup, Result inspection, and copy
requirements remain those established by semantic checking. Unsupported static
value algebra, missing full source shapes, and incomplete owner mappings retain
their NI boundary.

## Closure creation and qualification

Each ClosureInfo records its creating named invocation and enclosing dynamic
closure invocation. Each later closure call has a separate ClosureInvocationId,
the actual ClosureInfo index, both dynamic parents, lexical caller owner, and a
completion status. A shared ClosureSiteId never identifies a particular captured
environment. Explicit callable probes remain distinguishable from ordinary
flow. Diagnostics and NI mark active closure calls before diagnostic deduplication.

Expression and witness contexts carry both closure object and closure call IDs.
A known nonpositive budget marks the protected action's mandatory validation as
`budget_validation`; recovery lies outside that marker. This does not waive
typing, effects, copy, or resource requirements. Missing recipe selection in a
validation-only call is not a normal empty-recipe certificate. Native code still
needs compatible body evidence and an independently checked creation or ordinary
invocation recipe; contradictory nonempty selections remain errors or NI.

Generic callable aliases instantiate complete source syntax through the ordinary
static argument binder. Parameter modes, result shapes, capability annotations,
and their original lexical-environment locations survive. Nonempty generic effect
rows and callable defaults still need additional substitution witnesses. This
operation does not reconstruct callable qualifications from erased Ty.

Latent analysis can discover handler/helper captures absent from a lambda's
free-name scan. After preview rollback, the checker rebuilds their Capture edges
and recomputes mutable/observer environment classification from the complete graph.
Scalar storage cells are live roots too. An observer requires lawful view
reception; a mutable environment requires a writable invocation handle. Capturing
environments remain noncopyable, and captured Result obligations are not inspected
or returned merely by qualification ascription.

## Current closed native instances

`lower/specialize.rs` selects completed named invocation records by canonical
DefinitionId and complete closed static argument keys. It allocates a fresh
DefinitionId per distinct key, records every contributing CopyInstanceId, and
rewrites exact direct calls before HOF and CPS lowering. Equal keys share code
only when their operation, callable, literal, projection, handler and budget
selections agree. Template operation and expression sites must all have solved
coverage; the checker may supply that coverage by previewing an inactive branch.

Core `provenance.specializations` and Native `specializations` carry structured
argument shapes and explicit source-to-target CallableOwner and HandlerSiteId
maps. Source locations are unchanged. Each local handler site is independently
remapped for each instance; existing normal/metered entry generation uses that
same remapped identity. This introduces no runtime dictionary or new native ABI.

Numeric literal selection uses the exact invocation's contextual-write witness.
When no write was necessary, the already-solved numeric ExpressionFact supplies
the fallback type. An explicit contextual write takes precedence over the earlier
expression value. A global source-span type table never fills a missing instance.

Dynamic closure creation and invocation records now select distinct nested
ClosureSiteId mappings for each static instance. Every actual captured object is
linked to its creating named, closure, or default-use context. Escaped retained
recipes use the corresponding remapped handler sites after their creation
activation ends, including repeated creation with different captured values and
normal/metered calls. No source site is used as a captured-object identity.

Windows and Linux pass `native_specialization` (4 tests),
`generic_closure_specialization` (3), and `generic_default_specialization` (3).
The CLI suites pass `generic_effects` (7 actual executions and 1 explicit NI
boundary), `generic_defaults` (6 actual executions), and `default_metering` (2
tests). These targeted results cover closed int/str operations, transitive
calls, local handlers, escaped recipes, both conditional paths, supplied and
omitted arguments, and exact default/helper entry accounting. They do not
replace the separate full-workspace or frozen-corpus results.

Nested named functions, unknown callbacks, captured static binders, record-rest
bindings, closure parameter defaults, and implicit/default exits without a
completed application certificate retain their NI boundaries. Callable
extraction and uninstantiated symbolic templates also remain NI.

## Native default views

Each specialized parameter has a `DefaultSlot` tracing exact application event
IDs and completed DefaultUseIds. The planner validates every slot and its full
static witnesses against the entered instance. Default expressions get their
own fact view, operation selections, handlers, contextual literal types, and
budget proofs; body observations cannot stand in for this earlier evaluation.
Calls inside defaults select their own child instances from those use contexts.
Default-created closures join the instance through `creation_default`, then use
the same actual-object and later-invocation rules as body-created closures.

An empty evaluation list removes only that private instance's fallback, after
every covered application proves the parameter supplied. Universal default
checking remains in the frontend. An evaluated callee event that stops in its
arguments has no entered-body certificate and stays NI even when another call
at the same source location completed successfully. The planner checks that
event independently rather than inferring completion from a nearby invocation.

At runtime, omitted defaults execute before the callee's FunctionEntry charge.
Their own helper calls still charge their entries, and explicit arguments keep
their existing call-expression accounting. The change uses the existing CPS
parameter prologue and does not add an ABI or a runtime substitution dictionary.

## Default application identity

`DefaultUseId` identifies one evaluation of one omitted parameter. Its origin is
an explicit `CopyCallEventId`, an independently tagged declaration probe, or an
implicit invocation fallback. Explicit call events are passed into argument
preparation without consuming the event reserved for the named body invocation.
Every slot separately records Supplied, Default(use), or Missing. Written
arguments evaluate first in source order; omitted defaults follow in parameter
order under the callee's lexical bindings and inferred static binder identities.
Inference reuses the ordinary named-argument constraints on the supplied slots;
the caller's spelling of an unrelated `T` supplies no substitution.

Each use freezes its canonical target, parameter index, caller named/closure
context, logical lexical owner, complete static witnesses, and actual result
graph. Expression/witness contexts carry the active default use; closures carry
their creating default use in addition to their dynamic invocation ancestry.
Completed evaluation alone does not certify body entry. A use becomes Completed
only after the exact source event enters a completed named invocation whose full
static witnesses agree. A stopping default neither evaluates subsequent defaults
nor borrows an entered-body record from another same-key application. Declaration
probes retain their separate status and universally validate even supplied slots.

Actual default producers transfer their Result duties to the application owner
without inspection. Earlier Result arguments therefore survive later default
panic, aliasing, and recovery boundaries. Budget recovery now evaluates from its
entry snapshot independently of the completed action. Existing producer IDs and
normal/recovery inspections meet at the actual delimiter; an abandoned action's
inspection supplies no recovery proof. Scalar Results and complete immutable
carriers preserve their original producers. An exact member projection can use
conditional producer absence only with a complete fresh construction witness;
missing fields, unknown indices, partial rows, recency summaries and opaque
representations never count as absence. Scoped and unsupported heap ownership
exits retain their separate NI boundaries.

Parameter reception freezes actual ClosureInfo object IDs with their receipt
environment origins and causes. Forwarding an already received object avoids
reclassifying its existing hidden captures as newly acquired ambient references.
Allocation recency can move an origin but cannot merge or reuse a ClosureInfo ID.
New wrappers and actual ambient reads still contribute their own capabilities.
All escaped sharing counts, retained handlers, graph permissions, loan ends,
pending copies, and Result producer obligations continue through the ordinary
checks. A source span, lexical closure site, or coincident older origin is never
enough to establish this transfer.

## Independent frozen argument checks

Each static argument retains both a canonical key, consumed by specialization,
and normalized syntax, consumed by type substitution. The solved-facts validator
checks their agreement before constructing a verified program. It recomputes
the structural key under the registered declaration binders without reopening
the caller's substitutions. Fixed dimensions, callable modes and annotation
rows therefore cannot disagree between these two consumers.

The observation must cover its target's declared parameters and complete
captured binder environment. A symbolic type names its registered private
binder token; a plain spelling such as `T` is not a substitute. Missing syntax
and key remain an unresolved obligation together. A single missing component,
an altered owner/index, a duplicated capture, or an omitted capture is invalid.
Diagnostic positions do not define identity.

The check is bounded independently of language evaluation events. It checks
metadata consistency; it grants no graph freshness, permissions, non-escape
proof or body-entry certificate. `static_argument_witnesses.rs` mutates actual
solved effect and default observations, including empty nested arrays and
captured defaults, to check these boundaries.
