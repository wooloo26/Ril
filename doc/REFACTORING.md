# Compiler quality and editor tooling plan

## Execution order

1. Complete the native implementation against SPEC.md and STD.md, including
   capability safety oracles and actual applicable corpus execution on Windows
   MSVC and Linux GNU. Record actual failures and unsupported work honestly.
2. Commit that implementation before beginning the architectural refactoring.
3. Refine the design below from the completed implementation, then refactor with
   the goal of a highly maintainable, extensible compiler. Preserve language
   behavior and conservative verification throughout.
4. Implement the LSP and its VS Code extension using the refactored interfaces.
   Hover must expose both required capability annotations and the compiler's
   complete capability analysis for the selected symbol.

Implementation work is still in progress. This document records the user's
follow-on requirements; it does not declare any stage complete. Specification
contradictions go in SPEC_ISSUES.md. Ordinary implementation gaps stay in
IMPLEMENTATION.md and test reports.

## Refactoring direction

- Keep explicit phase boundaries: source and recovery syntax, lexical resolution,
  typed HIR, solved semantic facts, private verification, structured Core, native
  lowering, backend emission, runtime. Each phase has an owned input/output
  contract; obtaining an AST or constructing IR never grants verification.
- Separate declaration identity, storage identity, permission roots, abstract
  regions, loans, dynamic call instantiation, and source locations with typed
  identifiers. Source spans locate evidence; they do not substitute for identity.
  Assign expression/statement identities before semantic traversal and preserve
  them across controlled cloning. Replace the temporary `syntax_sites` ambiguity
  gate with those identities, so owned ASTs with equal diagnostic spans retain
  distinct handler/closure definitions and execute correctly. Replace global
  span-keyed contextual numeric inference as well: independent literal/value
  occurrences must not influence each other's default or contextual type.
  Keep the existing
  event-based copy invocation/reference ledger and its dynamic-parent checks.
- Replace the temporary NUL-prefixed committed-float normalized-AST carrier
  with a typed normalized literal node. Preserve its explicit IEEE width/bits
  across independent type/effect/foreign normalizers; canonical type-argument
  NaNs belong to that identity boundary only. Public source/owned AST validation
  must keep rejecting private carriers, and Core must consume them as committed
  values rather than opening new numeric inference holes.
- Move semantic domains behind focused operations and monotone lattice contracts.
  Heap shapes, conditional relations, permissions, effect/state obligations,
  Result/resource duties, termination and coverage retain explicit dependencies.
  Keep common fixed-point scheduling separate from each domain's transfer rules.
- Give every compiler-created assumption an explanation and retain its discharge
  or unresolved status. Eliminate parallel ad hoc implementations that erase
  permissions, row tails, alias alternatives, or static constraints.
- Provide shared exhaustive traversal/folding facilities for HIR and IR so adding
  a language construct cannot silently omit normalization, checking, provenance,
  code generation, tracing, or editor projection. Avoid a generic utility layer
  that obscures phase ownership.
- Centralize value-child, origin, type and contract traversal. Per-tag witnesses,
  Result families and return-contract DAGs must participate in copying,
  substitution, narrowing, escape checks and evidence projection through these
  operations. Preserve sharing with explicit memoization; neither a join nor an
  editor projection may expand a finite proof DAG into its exponential paths.
- Make standard-library declarations and their semantic/runtime contracts a
  versioned, typed registry. Share identities and signatures, while keeping the
  frontend independent of host runtime implementation and concrete backends.
- Expose immutable analysis snapshots and stable query results to CLI and tools.
  Preserve an explicitly uncertified analyzed HIR, diagnostics and unresolved
  facts while a document contains errors. VerifiedProgram wraps only a completed
  successful analysis and remains the sole normal lowering input; editor queries
  must not depend on obtaining that certificate.
  Scope incremental invalidation to actual dependencies; compare edited sessions
  with fresh sessions, including diagnostics and semantic summaries.
- Isolate native ABI and platform exceptions; explicit outcome, cleanup, GC roots,
  scheduler and host I/O contracts remain independently testable. Compiler crates
  keep unsafe_code=forbid.
- Refactor one ownership boundary at a time. Avoid a wholesale rewrite. Each
  change must have a stated simplification or extension benefit and relevant
  verification. Code size alone does not justify a new crate or abstraction.

## Refactoring acceptance

The completed implementation's passing corpus remains passing on both targets.
No invalid program becomes authorized, no unsupported case is counted as a pass,
and capability oracle/property/incremental tests continue to pass. Architecture
checks, formatting, lints, and relevant workspace tests pass. Public phase and
extension contracts are documented, duplicate semantic decisions are removed,
and a new backend or editor consumer can use typed results without importing the
checker internals. Performance changes require representative measurements where
they affect fixed-point solving, compilation, GC, or editor responsiveness.

## LSP analysis contract

The LSP consumes a versioned immutable project snapshot and a presentation model
derived from compiler evidence, not a second type or capability checker. Symbols
have declaration and occurrence identities, exact source ranges, inferred types,
mandatory written annotations, complete inferred obligations, and provenance.
Diagnostics and hover for a request must belong to the same document revision.
Cancellation and stale-result suppression must work across multi-file edits.
LSP UTF-16 positions are translated explicitly from compiler byte spans.

Hover starts with the ordinary signature or variable type, followed by readable
Chinese capability labels with a stable legend: 只读, 可写, 共享写, 已冻结,
构造中, 借用中, and 未知. The presentation remains replaceable; these labels
are not language syntax. Compiler identities are shown as cross-reference labels
where useful instead of unexplained mathematical glyphs.

The complete projection includes all applicable facts:

- Binding reassignment, referent writes, closure-environment writes, retained
  sharing, path/member restrictions, and immutable/live/construction status.
- Possible sources and reachable members, alias alternatives, conditional
  equality/disjointness, freshness, clone relationships, and unresolved overlap.
- Permission roots, loans and suspended parents, ownership scopes/tasks,
  captures, retention, escape dependencies, and boundary obligations.
- Concrete and symbolic effect/state summaries, callbacks, return/member
  relationships, handler/resumption, cleanup and termination/coverage evidence.
- Outstanding Result/resource duties and the derivation causes for accepted
  permissions as well as failed or unresolved proofs.

Hover must not silently truncate facts or describe unknown overlap as disjoint.
Shared graph nodes are displayed once with explicit references; full evidence
remains accessible through the same versioned presentation model. A VS Code
command may also open a navigable explanation document for large graphs, but it
does not replace the required capability information in hover.

## Editor deliverables and validation

Provide an LSP server with project loading, incremental diagnostics, symbol
hover, definition/reference navigation, cancellation and protocol tests; add
other operations through the same analysis API. Provide a packaged VS Code
extension with Ril file association, syntax configuration, server discovery and
settings, launch/stop lifecycle, and explanation navigation. Neither hover nor
diagnostics depend on executing a user's program.

Test initialization/shutdown, open/change/close, Unicode and UTF-16 ranges,
multi-file edits, stale requests, malformed source recovery, capability changes,
conditional aliases, mutable captures, generic instantiation, and explanation
completeness. Exercise the actual server protocol and extension build/package,
in addition to compiler-level tests.
