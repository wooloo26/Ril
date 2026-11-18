import RilAccess.Call.Proofs
import RilAccess.Call.Summary
import RilAccess.Reference.Provenance.Identity
import RilAccess.Effects.Boundary
import RilAccess.Effects.Concurrency
import RilAccess.Access.Handoff
import RilAccess.Access.Scoped
import RilAccess.Visibility
import RilAccess.Draft.Lowering
import RilAccess.Reference.Provenance.Limits
import RilAccess.Provenance.MachineProofs
import RilAccess.Provenance.Module
import RilAccess.Provenance.Cleanup

/-! Principal interface results, grouped by semantics. This bundle is not a
refinement theorem for an unrestricted language combining every model. All
boundary authenticity/completeness premises remain explicit in their interfaces. -/
namespace RilAccess.CoreVerification

structure SolverGuarantees : Prop where
  leastGrounded : ∀ (Fact : Type) [DecidableEq Fact] (rules : List (Rule Fact)), Closed rules (solve rules) ∧
    Grounded rules (solve rules) ∧ (solve rules).Nodup ∧
    ∀ facts, Closed rules facts → ∀ fact ∈ solve rules, fact ∈ facts

structure ProvenanceGuarantees : Prop where
  resolved : ∀ (program : Provenance.Program) budget certificate,
    Provenance.check program budget = .ok certificate →
    Provenance.Checked program certificate.facts ∧
    ∀ result, Provenance.Executes program.erase 0 {} result →
      Provenance.Covered program certificate.facts Provenance.startEntry result ∧
      Provenance.RuntimeGuarantee program certificate.facts Provenance.startEntry {} result
  erasedMachine : ∀ (program : Provenance.Program) budget certificate machine,
    Provenance.check program budget = .ok certificate → Provenance.MachineTrace program.erase machine →
    Provenance.MachineGuarantee program certificate.facts machine
  erasedProgress : ∀ (program : Provenance.Program) budget certificate fn pc frame stack,
    Provenance.check program budget = .ok certificate →
    Provenance.MachineTrace program.erase (.running fn pc frame stack) →
    ∃ next, Provenance.MachineStep program.erase (.running fn pc frame stack) next

structure ReferenceProvenanceGuarantees : Prop where
  coverage : ∀ (program : ResolvedProgram) analysis state event,
    analyze program = .ok analysis → Trace program (initial program.entry) state → event ∈ state.events →
      Fact.event event.kind event.origin.source ∈ analysis.facts
  identity : ∀ (program : ResolvedProgram) state,
    Trace program (initial program.entry) state → ProvenanceIdentity.WorldInvariant state
  entry : ∀ (program : ResolvedProgram) state arguments,
    Trace program (initial program.entry) state →
    (∀ origin ∈ arguments.flatMap Prod.snd, ProvenanceIdentity.Known state origin) →
    ∃ frozen, CoreEntry.capturePrepared state.heap arguments = .ok frozen

structure CompositionGuarantees : Prop where
  entryFootprint : ∀ signature before arguments prepared,
    Provenance.prepare signature before arguments = .ok prepared →
    Includes (prepared.caller.external ++ prepared.caller.liveObjects) prepared.entered.outside
  summary : ∀ (program : Provenance.Program) (entry : Provenance.Entry) budget summary frozen result,
    Provenance.summarize program entry budget = .ok summary →
    entry.world.raw = Provenance.RawFrame.abstract frozen →
    Provenance.Executes program.erase entry.function frozen result →
    Provenance.SummaryCovers program summary frozen result
  cleanupOrder : ∀ first resources,
    Provenance.cleanupInvocations (Provenance.cleanupRoute first resources) =
      resources.reverse.map Provenance.CleanupSlot.closer
  cleanupContinuation : ∀ first resources target args destination next onAbort,
    Provenance.Instruction.invoke target args destination next onAbort ∈ Provenance.cleanupRoute first resources →
    onAbort = none ∧ ∃ register,
      Provenance.Instruction.step [.expire register] (next + 1) ∈ Provenance.cleanupRoute first resources
  cleanupHandler : ∀ slot effect above below,
    Provenance.resolveCleanups [] [.handler effect above, .resource slot (some effect), .handler effect below] =
      [{ slot with closer := above }]
  draftHeap : ∀ (input : Draft.Input) (cell : Draft.Cell) child index member,
    cell ∈ input.pool → (Draft.Value.reference child, index) ∈ cell.contents.zipIdx →
    cell.storage.member index = some member →
    (⟨cell.origin.object, index, child⟩ : HeapLink Nat) ∈ input.physicalHeap
  transfer : ∀ (world : Provenance.World) register object moved ended frame outside,
    Provenance.consume world register = .ok (object, moved, ended) →
    world.raw = Provenance.RawFrame.abstract frame →
    Includes (outside.map Provenance.Object.abstract) (ended.liveObjects ++ ended.external) →
    ∃ root, frame.get register = some root ∧
      ∀ target, Heap.Reaches (Provenance.ownedLinks world.ownership frame.memory.heap) [root] target →
        Heap.Reaches frame.memory.heap outside target → False

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
  reachableUses : ∀ (program : Calls.Syntax) analysis requirement,
    Calls.check program = .ok analysis →
    requirement ∈ analysis.worlds.flatMap Integrated.World.requirements →
      Integrated.satisfiesUse (Integrated.allUses analysis.worlds) requirement = true
  retainedSurvival : ∀ entry frontier (argument : Calls.Argument),
    Calls.requiredUse entry frontier argument = true →
    argument.mode = .retained →
      ∃ token, Calls.parameterToken entry argument.formal = some token ∧
        ∃ world ∈ frontier, Calls.retainedBeyond token world = true

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
  residualEffects : ∀ (boundary : CoreBoundary.Boundary) handledEffect effect,
    effect ∈ (CoreBoundary.handled boundary handledEffect).effects ↔
      (effect ∈ boundary.body.effects ∧ effect ≠ handledEffect) ∨
        effect ∈ boundary.handler.effects ∨ effect ∈ boundary.cleanup.effects
  environments : ∀ (boundary : CoreBoundary.Boundary) activation scope origin,
    origin ∈ boundary.handlerEnvironment ++ boundary.cleanupEnvironment →
    owned activation scope origin = false →
    CoreBoundary.outward boundary activation scope = CoreBoundary.state boundary
  fnRevokesTemporary : ∀ (authority next : Integrated.World) opScope id path resolved,
    CoreBoundary.completeFnOp authority opScope = some next →
    Integrated.resolve next path = some resolved →
    id ∈ Integrated.temporaryWrites authority authority.scope →
    id ∈ resolved.permission.dependencies →
      Integrated.live resolved = false
  fnEndsDependentLoans : ∀ (authority next : Integrated.World) opScope loan,
    CoreBoundary.completeFnOp authority opScope = some next →
    loan ∈ next.loans →
    loan.token ∈ Integrated.lifetimeClosure authority
      (Integrated.temporaryWrites authority authority.scope) →
      loan.active = false
  fnPreservesNonTemporary : ∀ (authority next : Integrated.World) opScope id token,
    CoreBoundary.completeFnOp authority opScope = some next →
    Integrated.lookupToken authority id = some token →
    token.temporary = false →
      Integrated.lookupToken next id = some token
  sharedFnPreservesIsolation : ∀ pureSources admissibleEffects branch handler handlerEnv effect,
    CoreBoundary.concurrentShareableFnHandler pureSources admissibleEffects handler handlerEnv = true →
      (CoreBoundary.dischargeSharedFnEffect branch handler effect).writes = branch.writes ∧
      (CoreBoundary.dischargeSharedFnEffect branch handler effect).retained = branch.retained ∧
      (∀ e ∈ (CoreBoundary.dischargeSharedFnEffect branch handler effect).effects,
        (e ∈ branch.effects ∧ e ≠ effect) ∨ e ∈ admissibleEffects)

structure DraftGuarantees : Prop where
  preparedRoot : ∀ (shape : Draft.RootShape) value input start,
    Draft.prepareRoot shape value input = .ok start →
    ∃ tag root cell, shape.objectTag = some tag ∧ value = .reference root ∧
      Draft.lookup input.pool root = some cell ∧ cell.storage.tag = tag ∧
      Draft.prepare { input with root } = some start
  prefixes : ∀ (input : Draft.Input) recipe analysis,
    Draft.checkRecipe input recipe = some analysis →
    ∃ start commands, Draft.prepare input = some start ∧ Draft.lowerRecipe start recipe = some commands ∧
      ∀ middle, Draft.Prefix commands start middle →
        Draft.WorldInvariant input middle ∧ Draft.SourcesCovered middle.memory input.sources ∧
    ∀ event ∈ middle.events, Draft.Fact.event event.kind event.origin.source ∈ analysis.facts
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

structure ScopedGuarantees : Prop where
  resourceNoPlainOrSharedCopy : ∀ (world : Integrated.World) resolved mode scope,
    resolved.grant.resource = true → (mode.access = .immutable ∨ mode.access = .shared) →
      Integrated.receiving world resolved mode scope = false
  resourceNoRetain : ∀ (evidence : Integrated.Evidence),
    Integrated.authorized evidence = true → evidence.rule = .retain →
      evidence.resolved.grant.resource = false
  resourceHandoffExclusive : ∀ (world next : Integrated.World) source destination resolved,
    Integrated.checkAtom (.move source destination) world = .ok next →
    Integrated.resolve world ⟨source, []⟩ = some resolved →
      (∀ dep ∈ resolved.permission.dependencies, (Integrated.lookupToken next dep).any Integrated.Token.active = false) ∧
        ∃ fresh, Integrated.lookupToken next world.nextToken = some fresh ∧
          fresh.qualified = true ∧ fresh.active = true ∧ fresh.region = resolved.pointer
  scopedRejectsEscape : ∀ (world : Integrated.World) resolved mode scope,
    resolved.permission.isScoped = true →
      Integrated.eligibleMove world resolved = false ∧
        Integrated.receiving world resolved mode scope = false
  scopedNoRetain : ∀ (evidence : Integrated.Evidence),
    Integrated.authorized evidence = true → evidence.rule = .retain →
      evidence.resolved.permission.isScoped = false
  scopedRejectsReassignment : ∀ (world : Integrated.World) source destination target,
    Integrated.lookupPermission world destination = some target →
    target.isScoped = true →
      Integrated.transfer world (.assign ⟨source, []⟩ destination) = none
  scopeExitDeactivatesInner : ∀ (world next : Integrated.World) frame perm,
    Integrated.checkAtom .leaveScope world = .ok next →
    world.frames.head? = some frame →
    perm ∈ next.permissions →
    frame.parentScope < perm.scope →
      perm.alive = false
  cleanupContract : ∀ (contract : Integrated.ScopedCleanupContract),
    Integrated.validScopedCleanupContract contract = true ↔
      (contract.mode = .observe ∨ contract.mode = .mutable ∨ contract.mode = .construction) ∧
      contract.returnsUnit = true ∧ contract.hasFiberEffect = false ∧
      contract.writes = decide (contract.mode = .mutable) ∧
      contract.retains = false ∧ contract.captures = false

structure VisibilityGuarantees : Prop where
  opaqueScopeBoundary :
    VisibilityModel.visibleFrom .pubExport .samePkg = true ∧
    VisibilityModel.visibleFrom .pubExport .externalPkg = true ∧
    VisibilityModel.representationTransparent .pubExport .opaqueScope .sameScope = true ∧
    VisibilityModel.representationTransparent .pubExport .opaqueScope .samePkg = false ∧
    VisibilityModel.representationTransparent .pubExport .opaqueScope .externalPkg = false
  signatureVisibility : ∀ (decl : VisibilityModel.DeclarationVisibility) refs,
    VisibilityModel.signatureWellFormed decl refs = true ↔
      ∀ ref ∈ refs, decl.effective.rank ≤ ref.effective.rank
  topLevelPurity :
    VisibilityModel.validTopLevelBinding .pureConst = true ∧
    VisibilityModel.validTopLevelBinding .metaConst = true ∧
    VisibilityModel.validTopLevelBinding .mutableOrLiveState = false
  sumClosedInPkg : ∀ (s : VisibilityModel.SumDef) ctx covered,
    (ctx = .sameScope ∨ ctx = .samePkg) →
    VisibilityModel.canMatchVariants s ctx = true → (∀ v ∈ s.variants, v ∈ covered) →
      VisibilityModel.exhaustiveMatch s ctx covered false = true ∧
        VisibilityModel.exhaustiveMatch s ctx covered true = false
  extensibleOpenExternally : ∀ (s : VisibilityModel.SumDef) covered,
    s.extensible = true →
    VisibilityModel.canMatchVariants s .externalPkg = true →
      VisibilityModel.exhaustiveMatch s .externalPkg covered false = false ∧
        VisibilityModel.exhaustiveMatch s .externalPkg covered true = true
  opaqueScopeSumBlocksOutsideMatch : ∀ (s : VisibilityModel.SumDef) ctx covered hasWildcard,
    s.op = .opaqueScope → ctx ≠ .sameScope →
      VisibilityModel.exhaustiveMatch s ctx covered hasWildcard = false
  pkgAnchorIsolation :
    VisibilityModel.visibleFrom .pubPkg (VisibilityModel.importContext .pkg) = true ∧
    VisibilityModel.visibleFrom .pubPkg (VisibilityModel.importContext .ril) = false ∧
    VisibilityModel.visibleFrom .pubPkg (VisibilityModel.importContext .externalDep) = false ∧
    VisibilityModel.validDependencyMountName "pkg" = false ∧
    VisibilityModel.validDependencyMountName "ril" = false
  enclosingSubCapsVisibility : ∀ moduleHasPub (enclosingSubs : List VisibilityModel.Visibility) declVis subVis,
    subVis ∈ enclosingSubs →
      VisibilityModel.Visibility.le (VisibilityModel.pathVisibility moduleHasPub enclosingSubs declVis) subVis = true

structure CallableMatchGuarantees : Prop where
  reflexive : ∀ (pureSources : List Source) (s : Summary), s.subsumes pureSources s = true
  transitive : ∀ (pureSources : List Source) (a b c : Summary),
    b.subsumes pureSources a = true → c.subsumes pureSources b = true → c.subsumes pureSources a = true
  pureMatchesReturns : ∀ (pureSources : List Source) (actual expected : Summary),
    actual.isPure pureSources = true →
      (expected.subsumes pureSources actual = true ↔
        (∀ o ∈ actual.rootReturn, o ∈ expected.rootReturn) ∧
        (∀ o ∈ actual.contained, o ∈ expected.contained))
  foreignNeverPure : ∀ (pureSources : List Source) (expected actual : Summary) (o : Origin),
    o.source.kind = .foreign → o ∈ actual.namedReads → expected.subsumes pureSources actual = true →
      o ∈ expected.namedReads ∨ o ∈ expected.writes ∨ o ∈ expected.retained
  retainedStrict : ∀ (pureSources : List Source) (expected actual : Summary) (o : Origin),
    o ∈ actual.retained → expected.subsumes pureSources actual = true → o ∈ expected.retained
  instantiationMonotone : ∀ (pureSources : List Source) (expected actual : CoreSummary.Template) (call : CoreSummary.CallInstance),
    expected.subsumes pureSources actual = true →
      (CoreSummary.instantiate call expected).subsumes pureSources (CoreSummary.instantiate call actual) = true
  exactRejectsExcessWrite : ∀ (pureSources : List Source) (declared actual : Summary) (o : Origin),
    o ∈ declared.writes → o ∉ actual.writes →
      Summary.exactContract pureSources declared actual = false
  exactRejectsExcessRetained : ∀ (pureSources : List Source) (declared actual : Summary) (o : Origin),
    o ∈ declared.retained → o ∉ actual.retained →
      Summary.exactContract pureSources declared actual = false
  exactRejectsMissingEnvironment : ∀ (pureSources : List Source) (declared actual : Summary) (o : Origin),
    o ∈ actual.createdEnvironments → o ∉ declared.createdEnvironments →
      Summary.exactContract pureSources declared actual = false
  exactRejectsMissingLocalRead : ∀ (pureSources : List Source) (declared actual : Summary) (o : Origin),
    o.source.kind ≠ .module → o ∈ actual.namedReads → o ∉ declared.namedReads →
      Summary.exactContract pureSources declared actual = false

structure ConcurrencyGuarantees : Prop where
  sharedCaptureRejectsMutableScopedOrResource : ∀ (world : Integrated.World) (r : Integrated.Resolved),
    CoreConcurrency.eligibleSharedCapture world r = true →
      r.grant.resource = false ∧ r.permission.isScoped = false ∧
        Integrated.deepImmutable r = true ∧ Integrated.live r = true ∧
        r.permission.mode.replaceable = false ∧ r.permission.mode.access = .immutable ∧
        CoreConcurrency.sendableData r = true
  sharedCaptureReadOnly : ∀ (world : Integrated.World) path (e : Integrated.Evidence),
    Integrated.resolve world path = some e.resolved →
    e.resolved.permission.mode.access = .immutable →
    Integrated.authorized e = true →
      e.rule = .read ∧ e.observation.kind = .read
  spawnMoveDisjoint : ∀ (world next : Integrated.World) source childDestination resolved,
    CoreConcurrency.spawnMoveCapture world source childDestination = .ok next →
    Integrated.resolve world ⟨source, []⟩ = some resolved →
      CoreConcurrency.sendableData resolved = true ∧
      Integrated.rawLookup next.raw childDestination = some resolved.pointer ∧
      (∀ dep ∈ resolved.permission.dependencies, (Integrated.lookupToken next dep).any Integrated.Token.active = false) ∧
      (∀ path derived dep, Integrated.resolve next path = some derived →
        dep ∈ derived.permission.dependencies → dep ∈ resolved.permission.dependencies →
        Integrated.live derived = false)
  channelNoMutabilityLaundering : ∀ (world : Integrated.World) (r : Integrated.Resolved),
    r.effective = .immutable → CoreConcurrency.eligibleChannelSend true world r = false
  crossScopeRejected : ∀ (nursery : CoreConcurrency.NurseryState) taskId taskSigma asMove,
    taskSigma ≠ nursery.activeSigma →
      CoreConcurrency.joinTask nursery taskId taskSigma asMove = none ∧
        CoreConcurrency.cancelTask nursery taskId taskSigma = none
  singleShotTaskNoReuse : ∀ (nursery next : CoreConcurrency.NurseryState) taskId taskSigma nextSigma anyMove,
    CoreConcurrency.joinTask nursery taskId taskSigma true = some next →
      CoreConcurrency.joinTask next taskId nextSigma anyMove = none ∧
        CoreConcurrency.cancelTask next taskId nextSigma = none
  fallibleTaskResultRequired : ∀ (nursery : CoreConcurrency.NurseryState) entry,
    entry ∈ nursery.tasks → entry.pendingResult = true →
      CoreConcurrency.canExitScope nursery = false ∧ CoreConcurrency.drainPlainTasks nursery = none

structure Guarantees : Prop where
  solver : SolverGuarantees
  provenance : ProvenanceGuarantees
  referenceProvenance : ReferenceProvenanceGuarantees
  composition : CompositionGuarantees
  access : AccessGuarantees
  entry : EntryGuarantees
  callableMatch : CallableMatchGuarantees
  effects : EffectGuarantees
  concurrency : ConcurrencyGuarantees
  draft : DraftGuarantees
  scopedClose : ScopedGuarantees
  visibility : VisibilityGuarantees

theorem verified : Guarantees where
  solver := by
    constructor
    intro α inst rules
    exact ⟨solve_closed, solve_grounded, solve_nodup, fun _ => solve_least⟩
  provenance := {
    resolved := fun _ _ _ => Provenance.verified_program
    erasedMachine := fun _ _ _ _ => Provenance.verified_machine
    erasedProgress := fun _ _ _ _ _ _ _ => Provenance.machine_progress
  }
  referenceProvenance := ⟨fun _ _ _ _ => provenance_coverage,
    fun _ _ => ProvenanceIdentity.trace_invariant, fun _ _ _ => ProvenanceIdentity.cfg_entry_can_freeze⟩
  composition := {
    entryFootprint := fun _ _ _ _ => Provenance.prepared_external_roots
    summary := fun _ _ _ _ _ _ => Provenance.summarize_sound
    cleanupOrder := Provenance.cleanupRoute_lifo
    cleanupContinuation := fun _ _ _ _ _ _ _ => Provenance.cleanupRoute_call_continuation
    cleanupHandler := Provenance.later_handler_does_not_replace_saved_cleanup
    draftHeap := fun _ _ _ _ _ => Draft.stored_reference_in_physical_heap
    transfer := fun _ _ _ _ _ _ _ => Provenance.consumed_region_isolated
  }
  access := ⟨fun _ _ _ _ => Calls.every_prefix_authorized, fun _ _ => Calls.source_progress,
    fun _ _ _ _ => Integrated.handoff_preserves_identity,
    fun _ _ _ _ _ _ _ _ => Integrated.handoff_ends_derived_access,
    fun _ _ _ h hr => Calls.check_reachable_uses h hr,
    fun _ _ _ h hm => Calls.retained_mode_needs_survival h hm⟩
  entry := ⟨fun _ _ _ => CoreEntry.snapshot_objects,
    fun _ _ _ _ _ _ _ => CoreSummary.checked_at_entry_parameter_is_reachable,
    fun _ _ _ _ h => ⟨CoreSummary.checked_facts h, (CoreSummary.checked_valid h).2⟩⟩
  callableMatch := ⟨summary_subsumes_refl, fun _ _ _ _ => summary_subsumes_trans,
    fun _ _ expected hp => pure_summary_subsumes_iff hp expected,
    fun _ _ _ _ => foreign_read_not_erased_by_pure,
    fun _ _ _ _ => retained_not_subsumed_by_write_only,
    fun _ _ _ call h => CoreSummary.template_subsumes_instantiate h call,
    fun _ _ _ _ hdecl hnoW => exactContract_rejects_excess_write hdecl hnoW,
    fun _ _ _ _ hdecl hnoR => exactContract_rejects_excess_retained hdecl hnoR,
    fun _ _ _ _ hactual hmissing => exactContract_rejects_missing_environment hactual hmissing,
    fun _ _ _ _ hlocal hactual hmissing => exactContract_rejects_missing_local_read hlocal hactual hmissing⟩
  effects := ⟨CoreBoundary.handled_effects_exact,
    fun _ _ _ _ => CoreBoundary.external_environment_blocks_discharge,
    fun _ _ _ _ _ _ h hr hi hd => CoreBoundary.complete_fn_op_revokes_temporary_permission h hr hi hd,
    fun _ _ _ _ h hl hi => CoreBoundary.complete_fn_op_ends_dependent_loan h hl hi,
    fun _ _ _ _ _ h hlook hnonTemp => CoreBoundary.complete_fn_op_preserves_non_temporary h hlook hnonTemp,
    fun _ _ _ _ _ _ h =>
      let hiso := CoreBoundary.shared_fn_handler_preserves_branch_isolation h
      ⟨hiso.1, hiso.2.1, hiso.2.2.2.2.1⟩⟩
  concurrency := ⟨fun _ _ h => CoreConcurrency.cross_fiber_capture_rejects_mutable_scoped_or_resource h,
    fun _ _ _ hr himm hauth => CoreConcurrency.shared_capture_forbids_authorized_writes hr himm hauth,
    fun _ _ _ _ _ h hr => CoreConcurrency.spawned_move_disjoint_from_parent_live_permissions h hr,
    fun _ _ hfrozen => CoreConcurrency.frozen_object_cannot_launder_mutability_via_channel hfrozen,
    fun _ _ _ _ hcross => CoreConcurrency.cross_scope_task_rejected hcross,
    fun _ _ _ _ _ _ h => CoreConcurrency.duplicate_exclusive_task_consumption_rejected h,
    fun _ _ => CoreConcurrency.pending_result_blocks_scope_exit⟩
  draft := ⟨fun _ _ _ _ => Draft.prepared_root_sound, fun _ _ _ => Draft.checked_path_recipe_prefixes,
    fun _ _ _ _ _ => Draft.publication_ends_privilege,
    fun _ _ _ _ _ _ _ _ _ _ => Draft.conforming_external_cannot_escape⟩
  scopedClose := ⟨fun _ _ _ _ hres hmode => Integrated.resource_rejects_plain_and_shared_receiving hres hmode,
    fun _ h hr => Integrated.resource_cannot_retain h hr,
    fun _ _ _ _ _ h hr => Integrated.resource_handoff_transfers_exclusively h hr,
    fun _ _ _ _ hsc => Integrated.scoped_rejects_escape hsc,
    fun _ h hr => Integrated.scoped_cannot_retain h hr,
    fun _ _ _ _ hlook hsc => Integrated.scoped_rejects_reassignment hlook hsc,
    fun _ _ _ _ h hf hp hinner => Integrated.leaveScope_deactivates_inner_permission h hf hp hinner,
    Integrated.scoped_cleanup_contract_iff⟩
  visibility := ⟨VisibilityModel.opaqueScope_boundary,
    VisibilityModel.signature_visibility_iff,
    VisibilityModel.topLevel_rejects_mutable_and_live_state,
    fun _ _ _ => VisibilityModel.extensible_closed_inside_pkg,
    fun _ _ => VisibilityModel.extensible_open_outside_pkg,
    fun _ _ _ _ hop hout => VisibilityModel.opaqueScope_sum_blocks_outside_scope_match hop hout,
    VisibilityModel.pkg_anchor_isolates_package_visibility,
    fun _ _ _ _ hmem => VisibilityModel.enclosing_sub_caps_pathVisibility hmem⟩

end RilAccess.CoreVerification
