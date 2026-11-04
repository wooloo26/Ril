import RilAccess.Call.Proofs
import RilAccess.Call.Summary
import RilAccess.Provenance.Identity
import RilAccess.Effects.Boundary
import RilAccess.Effects.Resumption
import RilAccess.Access.Handoff
import RilAccess.Draft.Boundary
import RilAccess.Provenance.Limits

/-! Principal interface results, grouped by semantics. This bundle is not a
refinement theorem for an unrestricted language combining every model. All
boundary authenticity/completeness premises remain explicit in their interfaces. -/
namespace RilAccess.CoreVerification

structure SolverGuarantees : Prop where
  leastGrounded : ∀ (rules : List (Rule Fact)), Closed rules (solve rules) ∧
    Grounded rules (solve rules) ∧ (solve rules).Nodup ∧
    ∀ facts, Closed rules facts → ∀ fact ∈ solve rules, fact ∈ facts

structure ProvenanceGuarantees : Prop where
  coverage : ∀ (program : ResolvedProgram) analysis state event,
    analyze program = .ok analysis → Trace program (initial program.entry) state → event ∈ state.events →
      Fact.event event.kind event.origin.source ∈ analysis.facts
  identity : ∀ (program : ResolvedProgram) state,
    Trace program (initial program.entry) state → ProvenanceIdentity.WorldInvariant state
  entry : ∀ (program : ResolvedProgram) state arguments,
    Trace program (initial program.entry) state →
    (∀ origin ∈ arguments.flatMap Prod.snd, ProvenanceIdentity.Known state origin) →
    ∃ frozen, CoreEntry.capturePrepared state.heap arguments = .ok frozen

structure AccessGuarantees : Prop where
  calls : ∀ (program : Calls.Syntax) analysis middle event,
    Calls.check program = .ok analysis →
    Integrated.Prefix (Integrated.erase (Calls.lower program)) Integrated.initialWorld.raw middle →
    event ∈ middle.observations → event.pointer.source ∈ analysis.origins ∧
      ∃ evidence, evidence.observation = event ∧ Integrated.authorized evidence = true
  progress : ∀ (program : Calls.Syntax) analysis,
    Calls.check program = .ok analysis → ∃ result, result ∈ Calls.execute program Integrated.initialWorld.raw
  handoff : ∀ (world next : Integrated.World) source destination,
    Integrated.checkAtom (.move source destination) world = .ok next →
    ∃ resolved, Integrated.resolve world ⟨source, []⟩ = some resolved ∧
      Integrated.rawLookup next.raw destination = some resolved.pointer
  derivedExpiry : ∀ (world next : Integrated.World) source destination resolved path derived id,
    Integrated.checkAtom (.move source destination) world = .ok next →
    Integrated.resolve world ⟨source, []⟩ = some resolved →
    Integrated.resolve next path = some derived →
    id ∈ derived.permission.dependencies → id ∈ resolved.permission.dependencies →
    Integrated.live derived = false

structure EntryGuarantees : Prop where
  physical : ∀ (frozen : CoreEntry.Frozen) entry object,
    entry ∈ frozen.snapshots →
    (object ∈ entry.objects ↔ ∃ root ∈ entry.roots, Identity.Reach frozen.heap root.object object)
  parameter : ∀ actual heap arguments summary result formal selection,
    CoreSummary.checkAtEntry actual heap arguments summary = .ok result →
    CoreSummary.Reference.parameter formal selection ∈ CoreSummary.references summary →
    ∃ roots, (formal, roots) ∈ arguments ∧
      ∃ root ∈ roots, Identity.Reach heap root.object (actual.parameter formal selection).object
  substitution : ∀ actual frozen summary result,
    CoreSummary.check actual frozen summary = .ok result →
      CoreSummary.InputFacts actual frozen summary ∧ result = CoreSummary.instantiate actual summary

structure EffectGuarantees : Prop where
  environments : ∀ (boundary : CoreBoundary.Boundary) activation task scope origin,
    origin ∈ boundary.handlerEnvironment ++ boundary.cleanupEnvironment →
    owned activation task scope origin = false →
    CoreBoundary.outward boundary activation task scope = CoreBoundary.state boundary
  affine : ∀ (state next finish : CoreResumption.State) ticket,
    CoreResumption.resume state ticket = some next → CoreResumption.Trace next finish →
      CoreResumption.resume finish ticket = none
  lifetime : ∀ (state next : CoreResumption.State) ticket id path resolved,
    CoreResumption.resume state ticket = some next →
    Integrated.resolve next.authority path = some resolved →
    id ∈ Integrated.temporaryWrites state.authority state.authority.scope → id ∈ resolved.permission.dependencies →
      Integrated.live resolved = false
  loans : ∀ (state next : CoreResumption.State) ticket loan,
    CoreResumption.resume state ticket = some next → loan ∈ next.authority.loans →
    loan.token ∈ Integrated.lifetimeClosure state.authority
      (Integrated.temporaryWrites state.authority state.authority.scope) → loan.active = false
  retained : ∀ (state next : CoreResumption.State) ticket id token,
    CoreResumption.resume state ticket = some next →
    Integrated.lookupToken state.authority id = some token → token.retained = true →
      Integrated.lookupToken next.authority id = some token

structure DraftGuarantees : Prop where
  prefixes : ∀ (input : Draft.Input) program analysis,
    Draft.check input program = some analysis →
    ∃ start, Draft.prepare input = some start ∧ ∀ middle, Draft.Prefix program start middle →
      Draft.WorldInvariant input middle ∧ Draft.SourcesCovered middle.memory input.sources ∧
        ∀ event ∈ middle.events, Fact.event event.kind event.origin.source ∈ analysis.facts
  publication : ∀ (input : Draft.Input) start program finish published,
    Draft.prepare input = some start → Draft.Trace program start finish → finish.output = some published →
    published.access = .immutable ∧ finish.active = false ∧
      (∀ command, Draft.step command finish = none) ∧ ∃ cell, finish.memory published.object = some cell
  externalFrame : ∀ (input : Draft.Input) start program finish observation next actualEvents actualEffects footprint origin,
    Draft.prepare input = some start → Draft.Trace program start finish →
    Draft.step (.external observation) finish = some next →
    Draft.ExternalConforms observation actualEvents actualEffects footprint →
    origin ∈ footprint.roots ++ footprint.environments ++ footprint.escaping →
      origin.object ∉ finish.draftObjects

structure Guarantees : Prop where
  solver : SolverGuarantees
  provenance : ProvenanceGuarantees
  access : AccessGuarantees
  entry : EntryGuarantees
  effects : EffectGuarantees
  draft : DraftGuarantees

theorem verified : Guarantees where
  solver := ⟨fun _ => ⟨solve_closed, solve_grounded, solve_nodup, fun _ => solve_least⟩⟩
  provenance := ⟨fun _ _ _ _ => provenance_coverage,
    fun _ _ => ProvenanceIdentity.trace_invariant, fun _ _ _ => ProvenanceIdentity.cfg_entry_can_freeze⟩
  access := ⟨fun _ _ _ _ => Calls.every_prefix_authorized, fun _ _ => Calls.source_progress,
    fun _ _ _ _ => Integrated.handoff_preserves_identity, fun _ _ _ _ _ _ _ _ => Integrated.handoff_ends_derived_access⟩
  entry := ⟨fun _ _ _ => CoreEntry.snapshot_objects,
    fun _ _ _ _ _ _ _ => CoreSummary.checked_at_entry_parameter_is_reachable,
    fun _ _ _ _ h => ⟨CoreSummary.checked_facts h, (CoreSummary.checked_valid h).2⟩⟩
  effects := ⟨fun _ _ _ _ _ => CoreBoundary.external_environment_blocks_discharge,
    fun _ _ _ _ => CoreResumption.aliases_cannot_resume_twice,
    fun _ _ _ _ _ _ => CoreResumption.derived_access_ends,
    fun _ _ _ _ => CoreResumption.dependent_operation_loan,
    fun _ _ _ _ _ => CoreResumption.retained_authority_survives⟩
  draft := ⟨fun _ _ _ => Draft.checked_recipe_prefixes,
    fun _ _ _ _ _ => Draft.publication_ends_privilege,
    fun _ _ _ _ _ _ _ _ _ _ => Draft.conforming_external_cannot_escape⟩

end RilAccess.CoreVerification
