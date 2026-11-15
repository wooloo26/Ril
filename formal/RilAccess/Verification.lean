import RilAccess.Call.Proofs
import RilAccess.Call.Summary
import RilAccess.Provenance.Identity
import RilAccess.Effects.Boundary
import RilAccess.Effects.Resumption
import RilAccess.Effects.Concurrency
import RilAccess.Access.Handoff
import RilAccess.Access.Linear
import RilAccess.Visibility
import RilAccess.Draft.Lowering
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
  residualEffects : ∀ (boundary : CoreBoundary.Boundary) handledEffect effect,
    effect ∈ (CoreBoundary.handled boundary handledEffect).effects ↔
      (effect ∈ boundary.body.effects ∧ effect ≠ handledEffect) ∨
        effect ∈ boundary.handler.effects ∨ effect ∈ boundary.cleanup.effects
  environments : ∀ (boundary : CoreBoundary.Boundary) activation scope origin,
    origin ∈ boundary.handlerEnvironment ++ boundary.cleanupEnvironment →
    owned activation scope origin = false →
    CoreBoundary.outward boundary activation scope = CoreBoundary.state boundary
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
  fnRejectsResume : ∀ (state : CoreResumption.State) ticket,
    (∀ slot ∈ state.slots, slot.id = ticket → slot.kind = .fn) →
      CoreResumption.resume state ticket = none
  fnCannotAbort : ∀ delimiterScope (authority : Integrated.World),
    CoreResumption.abortOpDelimiter .fn delimiterScope authority = none ∧
      CoreResumption.canInvokeEffect .fn delimiterScope authority = true
  fnPreservesLinear : ∀ (state next : CoreResumption.State) ticket id token,
    CoreResumption.completeFnOp state ticket = some next →
    Integrated.lookupToken state.authority id = some token → token.temporary = false →
      Integrated.lookupToken next.authority id = some token
  fnRevokesTemporary : ∀ (state next : CoreResumption.State) ticket id path resolved,
    CoreResumption.completeFnOp state ticket = some next →
    Integrated.resolve next.authority path = some resolved →
    id ∈ Integrated.temporaryWrites state.authority state.authority.scope →
    id ∈ resolved.permission.dependencies →
      Integrated.live resolved = false
  ctlNotConcurrentShareable : ∀ pureSources admissibleEffects handler handlerEnv,
    CoreBoundary.concurrentShareableFnHandler pureSources admissibleEffects false handler handlerEnv = false
  sharedFnPreservesIsolation : ∀ pureSources admissibleEffects isFn branch handler handlerEnv effect,
    CoreBoundary.concurrentShareableFnHandler pureSources admissibleEffects isFn handler handlerEnv = true →
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

structure LinearGuarantees : Prop where
  callsDischargeAll : ∀ (program : Calls.Syntax) analysis world token,
    Calls.check program = .ok analysis → world ∈ analysis.worlds →
      token ∈ world.tokens → token.linear = true → token.active = false
  scopeExitDischarge : ∀ (world next : Integrated.World) frame token,
    Integrated.checkAtom .leaveScope world = .ok next → world.frames.head? = some frame →
      token ∈ world.tokens → token.linear = true → frame.parentScope < token.scope →
      token.active = false
  noPlainOrSharedCopy : ∀ (world : Integrated.World) resolved mode scope,
    resolved.grant.linear = true → (mode.access = .immutable ∨ mode.access = .shared) →
      Integrated.receiving world resolved mode scope = false
  noRetain : ∀ (evidence : Integrated.Evidence),
    Integrated.authorized evidence = true → evidence.rule = .retain →
      evidence.resolved.grant.linear = false
  handoffConservesObligation : ∀ (world next : Integrated.World) source destination resolved,
    Integrated.checkAtom (.move source destination) world = .ok next →
    Integrated.resolve world ⟨source, []⟩ = some resolved →
    resolved.grant.linear = true →
      (∀ dep ∈ resolved.permission.dependencies, (Integrated.lookupToken next dep).any Integrated.Token.active = false) ∧
        ∃ fresh, Integrated.lookupToken next world.nextToken = some fresh ∧
          fresh.linear = true ∧ fresh.active = true ∧ fresh.region = resolved.pointer
  destructureDischarges : ∀ (world next : Integrated.World) source resolved,
    Integrated.checkAtom (.destructure source) world = .ok next →
    Integrated.resolve world ⟨source, []⟩ = some resolved →
      Integrated.Use.mk source .writable ∈ next.uses ∧
        (∀ dep ∈ resolved.permission.dependencies, (Integrated.lookupToken next dep).any Integrated.Token.active = false) ∧
        (∀ path derived dep, Integrated.resolve next path = some derived →
          dep ∈ derived.permission.dependencies → dep ∈ resolved.permission.dependencies →
          Integrated.live derived = false)
  effectSuspensionGuard : ∀ delimiterScope (authority : Integrated.World) token,
    token ∈ authority.tokens → token.linear = true → token.active = true →
      delimiterScope < token.scope →
      CoreResumption.canSuspendEffect delimiterScope authority = false ∧
        CoreResumption.abortDelimiter delimiterScope authority = none
  abortPreservesOuterLinear : ∀ delimiterScope (authority after : Integrated.World) id token,
    CoreResumption.abortDelimiter delimiterScope authority = some after →
    Integrated.lookupToken authority id = some token →
    token.linear = true → token.active = true →
      token.scope ≤ delimiterScope ∧ Integrated.lookupToken after id = some token

structure VisibilityGuarantees : Prop where
  opaquePkgRequiresPub : ∀ (vis : VisibilityModel.Visibility),
    VisibilityModel.validOpacity vis .opaquePkg = true ↔ vis = .pubExport
  opaquePkgBoundary :
    VisibilityModel.visibleFrom .pubExport .externalPkg = true ∧
    VisibilityModel.representationTransparent .pubExport .opaquePkg .samePkg = true ∧
    VisibilityModel.representationTransparent .pubExport .opaquePkg .externalPkg = false
  signatureLeakRejected : ∀ (refs : List VisibilityModel.Visibility),
    VisibilityModel.Visibility.pubPkg ∈ refs →
      VisibilityModel.signatureWellFormed true .pubExport refs = false
  rilExtensibleClosedInPkg : ∀ (s : VisibilityModel.SumDef) ctx covered,
    s.origin = .rilPkg → s.extensible = true → (ctx = .sameScope ∨ ctx = .samePkg) →
    VisibilityModel.canMatchVariants s ctx = true → (∀ v ∈ s.variants, v ∈ covered) →
      VisibilityModel.exhaustiveMatch s ctx covered false = true ∧
        VisibilityModel.exhaustiveMatch s ctx covered true = false
  rilExtensibleOpenExternally : ∀ (s : VisibilityModel.SumDef) covered,
    s.origin = .rilPkg → s.extensible = true →
    VisibilityModel.canMatchVariants s .externalPkg = true →
      VisibilityModel.exhaustiveMatch s .externalPkg covered false = false ∧
        VisibilityModel.exhaustiveMatch s .externalPkg covered true = true
  foreignExtensibleOpenEverywhere : ∀ (s : VisibilityModel.SumDef) ctx covered,
    s.origin = .foreignDecl → s.extensible = true →
      VisibilityModel.exhaustiveMatch s ctx covered false = false
  opaquePkgSumBlocksExternalMatch : ∀ (s : VisibilityModel.SumDef) covered hasWildcard,
    s.op = .opaquePkg →
      VisibilityModel.exhaustiveMatch s .externalPkg covered hasWildcard = false
  pkgAnchorIsolation :
    VisibilityModel.visibleFrom .pubPkg (VisibilityModel.importContext .pkg) = true ∧
    VisibilityModel.visibleFrom .pubPkg (VisibilityModel.importContext .ril) = false ∧
    VisibilityModel.visibleFrom .pubPkg (VisibilityModel.importContext .externalDep) = false ∧
    VisibilityModel.validDependencyMountName "pkg" = false ∧
    VisibilityModel.validDependencyMountName "ril" = false
  nonPubSubBlocksOpaquePkg : ∀ moduleHasPub (enclosingSubs : List VisibilityModel.Visibility) declVis subVis,
    subVis ∈ enclosingSubs → subVis ≠ .pubExport →
      VisibilityModel.validPathOpacity moduleHasPub enclosingSubs declVis .opaquePkg = false
  genericSubStateless : ∀ depth, 0 < depth →
    VisibilityModel.validSubStorage depth .runtimeStorage = false ∧
      VisibilityModel.validSubStorage depth .metaConst = true

structure CallableMatchGuarantees : Prop where
  reflexive : ∀ (pureSources : List Source) (s : Summary), s.subsumes pureSources s = true
  transitive : ∀ (pureSources : List Source) (a b c : Summary),
    b.subsumes pureSources a = true → c.subsumes pureSources b = true → c.subsumes pureSources a = true
  pureMatchesAny : ∀ (pureSources : List Source) (actual expected : Summary),
    actual.isPure pureSources = true → expected.subsumes pureSources actual = true
  foreignNeverPure : ∀ (pureSources : List Source) (expected actual : Summary) (o : Origin),
    o.source.kind = .foreign → o ∈ actual.namedReads → expected.subsumes pureSources actual = true →
      o ∈ expected.namedReads ∨ o ∈ expected.writes ∨ o ∈ expected.retained
  retainedStrict : ∀ (pureSources : List Source) (expected actual : Summary) (o : Origin),
    o ∈ actual.retained → expected.subsumes pureSources actual = true → o ∈ expected.retained
  instantiationMonotone : ∀ (pureSources : List Source) (expected actual : CoreSummary.Template) (call : CoreSummary.CallInstance),
    expected.subsumes pureSources actual = true →
      (CoreSummary.instantiate call expected).subsumes pureSources (CoreSummary.instantiate call actual) = true

structure ConcurrencyGuarantees : Prop where
  sharedCaptureRejectsMutableOrLinear : ∀ (world : Integrated.World) (r : Integrated.Resolved),
    CoreConcurrency.eligibleSharedCapture world r = true →
      r.grant.linear = false ∧ Integrated.deepImmutable r = true ∧ Integrated.live r = true
  sharedCaptureReadOnly : ∀ (world : Integrated.World) path (e : Integrated.Evidence),
    Integrated.resolve world path = some e.resolved →
    e.resolved.permission.mode.access = .immutable →
    Integrated.authorized e = true →
      e.rule = .read ∧ e.observation.kind = .read
  spawnMoveDisjoint : ∀ (world next : Integrated.World) source childDestination resolved,
    CoreConcurrency.spawnMoveCapture world source childDestination = .ok next →
    Integrated.resolve world ⟨source, []⟩ = some resolved →
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
  linearTaskNoCancelOrLeak : ∀ (nursery : CoreConcurrency.NurseryState) taskId sigma entry,
    nursery.tasks.find? (fun t => decide (t.id = taskId)) = some entry →
    entry.linearResult = true →
      CoreConcurrency.cancelTask nursery taskId sigma = none ∧
        (entry.consumed = false →
          CoreConcurrency.canExitScope nursery = false ∧
          CoreConcurrency.drainPlainTasks nursery = none)
  fallibleTaskMustSettle : ∀ (nursery : CoreConcurrency.NurseryState) entry,
    entry ∈ nursery.tasks → entry.fallibleResult = true → entry.settled = false →
      CoreConcurrency.canExitScope nursery = false ∧ CoreConcurrency.drainPlainTasks nursery = none
  unshieldedAsyncBlocksLinear : ∀ delimiterScope (authority : Integrated.World) token,
    token ∈ authority.tokens → token.linear = true → token.active = true →
    delimiterScope < token.scope →
      CoreConcurrency.canSuspendAsync false delimiterScope authority = false ∧
        CoreConcurrency.canSuspendAsync true delimiterScope authority = true

structure Guarantees : Prop where
  solver : SolverGuarantees
  provenance : ProvenanceGuarantees
  access : AccessGuarantees
  entry : EntryGuarantees
  callableMatch : CallableMatchGuarantees
  effects : EffectGuarantees
  concurrency : ConcurrencyGuarantees
  draft : DraftGuarantees
  linear : LinearGuarantees
  visibility : VisibilityGuarantees

theorem verified : Guarantees where
  solver := ⟨fun _ => ⟨solve_closed, solve_grounded, solve_nodup, fun _ => solve_least⟩⟩
  provenance := ⟨fun _ _ _ _ => provenance_coverage,
    fun _ _ => ProvenanceIdentity.trace_invariant, fun _ _ _ => ProvenanceIdentity.cfg_entry_can_freeze⟩
  access := ⟨fun _ _ _ _ => Calls.every_prefix_authorized, fun _ _ => Calls.source_progress,
    fun _ _ _ _ => Integrated.handoff_preserves_identity, fun _ _ _ _ _ _ _ _ => Integrated.handoff_ends_derived_access⟩
  entry := ⟨fun _ _ _ => CoreEntry.snapshot_objects,
    fun _ _ _ _ _ _ _ => CoreSummary.checked_at_entry_parameter_is_reachable,
    fun _ _ _ _ h => ⟨CoreSummary.checked_facts h, (CoreSummary.checked_valid h).2⟩⟩
  callableMatch := ⟨summary_subsumes_refl, fun _ _ _ _ => summary_subsumes_trans,
    fun _ _ expected hp => pure_summary_subsumed_by_any hp expected,
    fun _ _ _ _ => foreign_read_not_erased_by_pure,
    fun _ _ _ _ => retained_not_subsumed_by_write_only,
    fun _ _ _ call h => CoreSummary.template_subsumes_instantiate h call⟩
  effects := ⟨CoreBoundary.handled_effects_exact,
    fun _ _ _ _ => CoreBoundary.external_environment_blocks_discharge,
    fun _ _ _ _ => CoreResumption.aliases_cannot_resume_twice,
    fun _ _ _ _ _ _ => CoreResumption.derived_access_ends,
    fun _ _ _ _ => CoreResumption.dependent_operation_loan,
    fun _ _ _ _ _ => CoreResumption.retained_authority_survives,
    fun _ _ hfn => CoreResumption.fn_slot_rejects_resume hfn,
    CoreResumption.fn_op_cannot_abort_delimiter,
    fun _ _ _ _ _ h hlook hnonTemp => CoreResumption.complete_fn_op_preserves_linear_token h hlook hnonTemp,
    fun _ _ _ _ _ _ h hr hi hd => CoreResumption.complete_fn_op_revokes_temporary_permission h hr hi hd,
    CoreBoundary.ctl_handler_not_concurrent_shareable,
    fun _ _ _ _ _ _ _ h =>
      let hiso := CoreBoundary.shared_fn_handler_preserves_branch_isolation h
      ⟨hiso.1, hiso.2.1, hiso.2.2.2.2.1⟩⟩
  concurrency := ⟨fun _ _ h => CoreConcurrency.cross_fiber_capture_rejects_mutable_or_linear h,
    fun _ _ _ hr himm hauth => CoreConcurrency.shared_capture_forbids_authorized_writes hr himm hauth,
    fun _ _ _ _ _ h hr => CoreConcurrency.spawned_move_disjoint_from_parent_live_permissions h hr,
    fun _ _ hfrozen => CoreConcurrency.frozen_object_cannot_launder_mutability_via_channel hfrozen,
    fun _ _ _ _ hcross => CoreConcurrency.cross_scope_task_rejected hcross,
    fun _ _ _ _ _ _ h => CoreConcurrency.duplicate_exclusive_task_consumption_rejected h,
    fun _ _ _ _ hfind hlin => CoreConcurrency.linear_task_cannot_cancel_or_leak hfind hlin,
    fun _ _ hm hfall hun => CoreConcurrency.unsettled_fallible_task_blocks_scope_exit hm hfall hun,
    fun _ _ _ hm hlin hact hinner => CoreConcurrency.unshielded_async_blocks_active_linear hm hlin hact hinner⟩
  draft := ⟨fun _ _ _ _ => Draft.prepared_root_sound, fun _ _ _ => Draft.checked_path_recipe_prefixes,
    fun _ _ _ _ _ => Draft.publication_ends_privilege,
    fun _ _ _ _ _ _ _ _ _ _ => Draft.conforming_external_cannot_escape⟩
  linear := ⟨fun _ _ _ _ h hw ht hlin => Integrated.checked_calls_no_unconsumed_linear h hw ht hlin,
    fun _ _ _ _ h hf ht hlin hinner => Integrated.leaveScope_no_active_inner_linear h hf ht hlin hinner,
    fun _ _ _ _ hlin hmode => Integrated.linear_rejects_plain_and_shared_receiving hlin hmode,
    fun _ h hr => Integrated.linear_cannot_retain h hr,
    fun _ _ _ _ _ h hr hlin => Integrated.linear_handoff_transfers_obligation h hr hlin,
    fun _ _ _ _ h hr => Integrated.destructure_discharges_and_revokes h hr,
    fun _ _ _ hm hlin hact hinner => CoreResumption.active_inner_linear_blocks_suspension hm hlin hact hinner,
    fun _ _ _ _ _ h hlook hlin hact => CoreResumption.abortDelimiter_preserves_active_linear h hlook hlin hact⟩
  visibility := ⟨fun _ => VisibilityModel.opaquePkg_requires_pubExport,
    VisibilityModel.opaquePkg_boundary,
    fun _ hmem => VisibilityModel.signature_rejects_pubPkg_leak hmem,
    fun _ _ _ horig hext hctx hcan hall => VisibilityModel.ril_extensible_closed_inside_pkg horig hext hctx hcan hall,
    fun _ _ horig hext hcan => VisibilityModel.ril_extensible_open_outside_pkg horig hext hcan,
    fun _ _ _ horig hext => VisibilityModel.foreign_extensible_open_everywhere horig hext,
    fun _ _ _ hop => VisibilityModel.opaquePkg_sum_blocks_external_match hop,
    VisibilityModel.pkg_anchor_isolates_package_visibility,
    fun _ _ _ _ hmem hnot => VisibilityModel.nonPub_enclosing_sub_rejects_opaquePkg hmem hnot,
    fun _ hgen => VisibilityModel.generic_sub_rejects_runtime_storage hgen⟩

end RilAccess.CoreVerification
