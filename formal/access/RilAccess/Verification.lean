import RilAccess.Call.Proofs
import RilAccess.Graph.Authority
import RilAccess.Effects.Boundary
import RilAccess.Call.Summary
import RilAccess.Effects.Resumption
import RilAccess.Access.Footprints
import RilAccess.Provenance.Limits

/-! Mathematical core certificate. The fields state the exact verified scope;
this does not assert surface elaboration, arbitrary entry-history conformance or
execution of every library/language mechanism. Derived adapters are audited
against these obligations rather than each receiving another theorem suite. -/
namespace RilAccess.CoreVerification

structure Guarantees : Prop where
  leastFixedPoint : ∀ (rules : List (Rule Fact)),
    Closed rules (solve rules) ∧ Grounded rules (solve rules) ∧ (solve rules).Nodup
  minimalSolution : ∀ (rules : List (Rule Fact)) facts,
    Closed rules facts → ∀ fact ∈ solve rules, fact ∈ facts
  allFinitePrefixes : ∀ (program : ResolvedProgram) analysis state event,
    analyze program = .ok analysis → Trace program (initial program.entry) state → event ∈ state.events →
      Fact.event event.kind event.origin.source ∈ analysis.facts
  pointSources : ∀ (program : ResolvedProgram) analysis state pc register origin,
    analyze program = .ok analysis → Trace program (initial program.entry) state → state.pc = some pc →
      origin ∈ state.roots register → Fact.root register origin.source ∈ analysis.at pc
  callAccessAndSources : ∀ (program : Calls.Syntax) analysis middle event,
    Calls.check program = .ok analysis →
    Integrated.Prefix (Integrated.erase (Calls.lower program)) Integrated.initialWorld.raw middle →
    event ∈ middle.observations → event.pointer.source ∈ analysis.origins ∧
      ∃ evidence, evidence.observation = event ∧ Integrated.authorized evidence = true
  callProgress : ∀ (program : Calls.Syntax) analysis,
    Calls.check program = .ok analysis → ∃ result, result ∈ Calls.execute program Integrated.initialWorld.raw
  cyclicGraphClosure : ∀ (graph : GraphAuthority.Graph Nat) fact,
    fact ∈ GraphAuthority.analyze graph ↔ GraphAuthority.Granted graph fact
  pathAuthority : ∀ (edges : List (GraphAuthority.Edge Nat)) root access fields object mode,
    GraphAuthority.Path edges root access fields object mode → mode.writes = true → access.writes = true
  immutablePublication : ∀ (graph : GraphAuthority.Graph Nat) immutable writer,
    GraphAuthority.immutableConsistent graph = true → immutable ∈ GraphAuthority.analyze graph →
    immutable.access = .immutable → writer ∈ GraphAuthority.analyze graph →
    writer.object = immutable.object → writer.access.writes = true → False
  graphSeparation : ∀ heap left right leftRoot leftTarget rightRoot rightTarget,
    CoreEntry.separated heap left right = true → leftRoot ∈ left → Reach heap leftRoot leftTarget →
      rightRoot ∈ right → Reach heap rightRoot rightTarget → leftTarget.object ≠ rightTarget.object
  correlatedSeparation : ∀ alternatives pair,
    correlatedSeparated alternatives = true → pair ∈ alternatives → Separated pair.1 pair.2
  relationalJoin : ∀ left right,
    correlatedSeparated left = true → correlatedSeparated right = true → correlatedSeparated (left ++ right) = true
  simultaneousAccess : ∀ (evidence : Integrated.Evidence) peer,
    Integrated.authorized evidence = true → peer ∈ evidence.peers →
      Integrated.overlaps peer evidence.resolved.pointer = false
  temporaryLifetime : ∀ (resolved : Integrated.Resolved) token,
    Integrated.live resolved = true → token ∈ resolved.tokens → token.active = true
  constructionHandoff : ∀ handle authority fresh result,
    transferConstruction handle authority fresh = some result → result.target.origin = handle.origin ∧
      ¬CanWrite handle result.sourceAuthority ∧ result.target.authority ≠ handle.authority
  completeAuthorityRoots : ∀ (world : Integrated.World) scope region root,
    Integrated.confinedTo world scope region = true → root ∈ Integrated.authorityRoots world →
      Integrated.overlaps root.pointer region = true → scope ≤ root.scope ∧ root.kind ≠ .retained
  soundDischarge : ∀ activation task scope abstract concrete events event,
    FootprintCovers abstract concrete → event ∈ events →
    event ∉ discharge activation task scope abstract events →
    event ∉ discharge activation task scope concrete events
  effectEnvironment : ∀ (boundary : CoreBoundary.Boundary) activation task scope origin,
    origin ∈ boundary.handlerEnvironment ++ boundary.cleanupEnvironment → owned activation task scope origin = false →
    CoreBoundary.outward boundary activation task scope = CoreBoundary.state boundary
  handlerCleanupState : ∀ (boundary : CoreBoundary.Boundary) activation task scope origin,
    (origin ∈ boundary.handler.writes ∨ origin ∈ boundary.cleanup.writes) →
    owned activation task scope origin = false →
    ∃ event ∈ CoreBoundary.outward boundary activation task scope, event.kind = .write ∧ event.origin = origin
  concreteSummaryIdentity : ∀ actual (summary : CoreSummary.Template) origin,
    CoreSummary.Reference.concrete origin ∈ CoreSummary.references summary →
    origin ∈ CoreSummary.origins (CoreSummary.instantiate actual summary)
  freshSummaryOrigins : ∀ (actual : CoreSummary.CallInstance) source serial object,
    object ∈ actual.existingObjects → (CoreSummary.resolve actual (.fresh source serial)).object ≠ object ∧
      (CoreSummary.resolve actual (.fresh source serial)).source = source
  frozenEntrySources : ∀ formal heap roots target,
    target ∈ (CoreEntry.capture formal heap roots).origins ↔ ∃ root ∈ roots, Reach heap root target
  checkedSummaryEntry : ∀ actual entries summary result formal selection,
    CoreSummary.check actual entries summary = .ok result →
    CoreSummary.Reference.parameter formal selection ∈ CoreSummary.references summary →
    ∃ entry ∈ entries, entry.formal = formal ∧ actual.parameter formal selection ∈ entry.origins
  producedSummaryEntry : ∀ actual heap arguments summary result formal selection,
    CoreSummary.checkAtEntry actual heap arguments summary = .ok result →
    CoreSummary.Reference.parameter formal selection ∈ CoreSummary.references summary →
    ∃ savedRoots, (formal, savedRoots) ∈ arguments ∧
      ∃ root ∈ savedRoots, Reach heap root (actual.parameter formal selection)
  checkedSummaryFreshness : ∀ actual entries summary result entry origin source serial,
    CoreSummary.check actual entries summary = .ok result → entry ∈ entries → origin ∈ entry.origins →
    (CoreSummary.resolve actual (.fresh source serial)).object ≠ origin.object
  separateFreshTemplates : ∀ actual entries summary result leftSource leftSerial rightSource rightSerial,
    CoreSummary.check actual entries summary = .ok result →
    CoreSummary.Reference.fresh leftSource leftSerial ∈ CoreSummary.references summary →
    CoreSummary.Reference.fresh rightSource rightSerial ∈ CoreSummary.references summary →
    (leftSource, leftSerial) ≠ (rightSource, rightSerial) →
    (CoreSummary.resolve actual (.fresh leftSource leftSerial)).object ≠
      (CoreSummary.resolve actual (.fresh rightSource rightSerial)).object
  oldSourcesAreNotLocal : ∀ actual entries summary result reference,
    CoreSummary.check actual entries summary = .ok result → reference ∈ CoreSummary.references summary →
    (∀ source serial, reference ≠ .fresh source serial) →
    owned actual.activation actual.task actual.scope (CoreSummary.resolve actual reference) = false
  boundaryElimination : ∀ (boundary : CoreBoundary.Boundary) activation task scope event,
    event ∈ CoreBoundary.state boundary → event ∉ CoreBoundary.outward boundary activation task scope →
    localEvent event.kind = true ∧ owned activation task scope event.origin = true ∧
      confined activation task scope (CoreBoundary.footprint boundary) = true
  affineResumeAliases : ∀ (state next finish : CoreResumption.State) ticket,
    CoreResumption.resume state ticket = some next → CoreResumption.Trace next finish →
      CoreResumption.resume finish ticket = none
  operationAuthority : ∀ (state next : CoreResumption.State) ticket,
    CoreResumption.resume state ticket = some next →
    ∃ slot ∈ state.slots, slot.id = ticket ∧
      (∀ authority ∈ slot.temporary, authority ∉ next.activeAuthority) ∧
      (∀ authority ∈ state.activeAuthority, authority ∉ slot.temporary → authority ∈ next.activeAuthority)
  resumeStateConservation : ∀ (start finish : CoreResumption.State),
    CoreResumption.Trace start finish → finish.committed = start.committed
  externalContract : ∀ (contract : ForeignContract) trace event,
    ForeignConforms contract trace → event ∈ trace → event.origin.source ∈ contract.sources
  exactnessBoundary : ∀ step state, Publishes step (.running state) ↔ Halts step state
  noComputableExactness : ∀ (halts : Nat → Prop) computable decider,
    DiagonalRepresentable halts computable → computable decider →
    (∀ code, decider code = true ↔ halts code) → False

theorem verified : Guarantees where
  leastFixedPoint := fun _ => ⟨solve_closed, solve_grounded, solve_nodup⟩
  minimalSolution := fun _ _ => solve_least
  allFinitePrefixes := fun _ _ _ _ => provenance_coverage
  pointSources := fun _ _ _ _ _ _ => program_point_coverage
  callAccessAndSources := fun _ _ _ _ => Calls.every_prefix_authorized
  callProgress := fun _ _ => Calls.source_progress
  cyclicGraphClosure := fun _ _ => GraphAuthority.analyze_exact
  pathAuthority := fun _ _ _ _ _ _ => GraphAuthority.path_writable_root
  immutablePublication := fun _ _ _ => GraphAuthority.immutable_has_no_writer
  graphSeparation := fun _ _ _ _ _ _ _ => CoreEntry.separated_paths_cannot_alias
  correlatedSeparation := fun _ _ => correlated_separation_sound
  relationalJoin := fun _ _ => join_preserves_common_relation
  simultaneousAccess := fun _ _ => Integrated.simultaneous_participants_separated
  temporaryLifetime := fun _ _ => Integrated.active_dependency_required
  constructionHandoff := fun _ _ _ _ => transfer_consumes_and_preserves
  completeAuthorityRoots := fun _ _ _ _ => Integrated.confinement_covers_every_root
  soundDischarge := fun _ _ _ _ _ _ _ => static_discharge_safe
  effectEnvironment := fun _ _ _ _ _ => CoreBoundary.external_environment_blocks_discharge
  handlerCleanupState := fun _ _ _ _ _ => CoreBoundary.handled_handler_and_cleanup_writes_survive
  concreteSummaryIdentity := fun _ _ _ => CoreSummary.every_concrete_identity_survives
  freshSummaryOrigins := fun _ _ _ _ => CoreSummary.fresh_origin_excludes_existing
  frozenEntrySources := fun _ _ _ _ => CoreEntry.entry_capture_exact
  checkedSummaryEntry := fun _ _ _ _ _ _ => CoreSummary.checked_parameter_uses_frozen_entry
  producedSummaryEntry := fun _ _ _ _ _ _ _ => CoreSummary.checked_at_entry_parameter_is_reachable
  checkedSummaryFreshness := fun _ _ _ _ _ _ _ _ => CoreSummary.checked_fresh_origin_excludes_frozen_entry
  separateFreshTemplates := fun _ _ _ _ _ _ _ _ => CoreSummary.checked_distinct_fresh_objects
  oldSourcesAreNotLocal := fun _ _ _ _ _ => CoreSummary.checked_existing_origin_is_not_callee_local
  boundaryElimination := fun _ _ _ _ _ => CoreBoundary.discharged_state_requires_complete_confinement
  affineResumeAliases := fun _ _ _ _ => CoreResumption.aliases_cannot_resume_twice
  operationAuthority := fun _ _ _ => CoreResumption.operation_authority_ends
  resumeStateConservation := fun _ _ => CoreResumption.resume_keeps_committed_state
  externalContract := fun _ _ _ => foreign_sources_covered
  exactnessBoundary := fun _ _ => source_reachability_iff_halting
  noComputableExactness := fun _ _ _ => no_computable_exact_decider _

end RilAccess.CoreVerification
