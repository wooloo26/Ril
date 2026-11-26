import RilAccess.Signatures
import RilAccess.Access.Scope

/-! The state/provenance and unified Route 1 dynamic effect-handler boundary kernel:
- Ril effects distinguish direct `fn` operations from one-shot algebraic `ctl`
  operations; both dispatch dynamically along the active call stack (closures
  and `where`-local `fn`s never implicitly capture outer `with` handlers).
- Effect handling discharges covered `@Eff` labels while preserving handler and
  `defer` cleanup state/environment obligations; handler arms run against the
  handler frame's parent stack.
- Completing a direct `fn` operation arm revokes temporary `mut` operation
  parameters and dependent views/holds while preserving outer and retained authority.
- Deep handler arms match `fn`/`ctl` prefixes (`E0623`) and forbid one-shot RHS (`E0534`);
  `absorb_panic` (`E0608`) and `derive` (`E0607`) enforce isolation against outer `ctl`. -/
namespace RilAccess.CoreBoundary

structure Boundary where
  body : Summary
  handler : Summary
  /-- Residual obligations after resolving handlers at each cleanup site.
  Cleanup effects handled inside the protected body belong to body instead. -/
  cleanup : Summary
  bodyRoots : Footprint
  handlerRoots : Footprint
  cleanupRoots : Footprint
  handlerEnvironment : List SourceInstance
  cleanupEnvironment : List SourceInstance
  deriving Repr, DecidableEq

def footprint (boundary : Boundary) : Footprint :=
  ⟨boundary.bodyRoots.roots ++ boundary.handlerRoots.roots ++ boundary.cleanupRoots.roots,
    (boundary.handlerEnvironment ++ boundary.cleanupEnvironment) ++
      boundary.bodyRoots.environments ++ boundary.handlerRoots.environments ++ boundary.cleanupRoots.environments,
    boundary.bodyRoots.escaping ++ boundary.handlerRoots.escaping ++ boundary.cleanupRoots.escaping⟩

def handled (boundary : Boundary) (effect : Nat) : Summary :=
  ((boundary.body.handle effect).combine boundary.handler).combine boundary.cleanup

/-- Operation arms use outer handlers, including for their own effect family.
Already-resolved cleanup obligations must not be handled a second time. -/
theorem handled_effects_exact (boundary : Boundary) (handledEffect effect : Nat) :
    effect ∈ (handled boundary handledEffect).effects ↔
      (effect ∈ boundary.body.effects ∧ effect ≠ handledEffect) ∨
        effect ∈ boundary.handler.effects ∨ effect ∈ boundary.cleanup.effects := by
  simp [handled, Summary.combine, Summary.handle]

def events (summary : Summary) (mechanism : Mechanism) : List Event :=
  summary.rootReturn.map (fun srcInst => ⟨.rootReturn, srcInst, mechanism⟩) ++
  summary.contained.map (fun srcInst => ⟨.containedReturn, srcInst, mechanism⟩) ++
  summary.writes.map (fun srcInst => ⟨.write, srcInst, mechanism⟩) ++
  summary.retained.map (fun srcInst => ⟨.retain, srcInst, mechanism⟩) ++
  summary.createdEnvironments.map (fun srcInst => ⟨.capture, srcInst, mechanism⟩) ++
  summary.namedReads.map (fun srcInst => ⟨.read, srcInst, mechanism⟩)

def state (boundary : Boundary) : List Event :=
  events boundary.body .call ++ events boundary.handler .handler ++ events boundary.cleanup .cleanup

def outward (boundary : Boundary) (activation scope : Nat) : List Event :=
  discharge activation scope (footprint boundary) (state boundary)

theorem handled_state_components (boundary : Boundary) (effect : Nat) :
    (handled boundary effect).rootReturn = boundary.body.rootReturn ++ boundary.handler.rootReturn ++ boundary.cleanup.rootReturn ∧
    (handled boundary effect).contained = boundary.body.contained ++ boundary.handler.contained ++ boundary.cleanup.contained ∧
    (handled boundary effect).writes = boundary.body.writes ++ boundary.handler.writes ++ boundary.cleanup.writes ∧
    (handled boundary effect).retained = boundary.body.retained ++ boundary.handler.retained ++ boundary.cleanup.retained ∧
    (handled boundary effect).createdEnvironments = boundary.body.createdEnvironments ++ boundary.handler.createdEnvironments ++ boundary.cleanup.createdEnvironments ∧
    (handled boundary effect).namedReads = boundary.body.namedReads ++ boundary.handler.namedReads ++ boundary.cleanup.namedReads :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem discharged_state_requires_complete_confinement
    (he : event ∈ state boundary) (hn : event ∉ outward boundary activation scope) :
    localEvent event.kind = true ∧ allocatedIn activation scope event.srcInst = true ∧
      confined activation scope (footprint boundary) = true := discharge_only_confined he hn

theorem outer_environment_blocks_containment
    (he : srcInst ∈ boundary.handlerEnvironment ++ boundary.cleanupEnvironment)
    (ho : allocatedIn activation scope srcInst = false) :
    outward boundary activation scope = state boundary := by
  have hn : confined activation scope (footprint boundary) = false := by
    cases hc : confined activation scope (footprint boundary) with
    | false => rfl
    | true =>
      have hm : srcInst ∈ (footprint boundary).roots ++ (footprint boundary).environments := by
        apply List.mem_append_right
        apply List.mem_append_left
        apply List.mem_append_left
        apply List.mem_append_left
        exact he
      have hp := confined_roots hc hm
      simp [ho] at hp
  simp [outward, discharge, hn]

theorem handled_handler_and_cleanup_writes_survive
    (he : srcInst ∈ boundary.handler.writes ∨ srcInst ∈ boundary.cleanup.writes)
    (ho : allocatedIn activation scope srcInst = false) :
    ∃ event ∈ outward boundary activation scope, event.kind = .write ∧ event.srcInst = srcInst := by
  have eventPresent : ∃ event ∈ state boundary, event.kind = .write ∧ event.srcInst = srcInst := by
    rcases he with hh | hc
    · refine ⟨⟨.write, srcInst, .handler⟩, ?_, rfl, rfl⟩
      apply List.mem_append_left
      apply List.mem_append_right
      simp [events, hh]
    · refine ⟨⟨.write, srcInst, .cleanup⟩, ?_, rfl, rfl⟩
      apply List.mem_append_right
      simp [events, hc]
  obtain ⟨event, hev, hk, heq⟩ := eventPresent
  refine ⟨event, List.mem_filter.mpr ⟨hev, ?_⟩, hk, heq⟩
  simp [heq, ho]

/-- Direct 1-shot `fn` operation completion over the authority ledger: returning
from the handler arm revokes temporary `mut` operation parameters for `opScope`
while preserving retained and outer non-temporary tokens. -/
def completeFnOp (authority : Integrated.World) (opScope : Nat) : Option Integrated.World :=
  let after := Integrated.endBoundary authority (Integrated.scopedWrites authority opScope)
  if decide (opScope = authority.scope) &&
      (Integrated.ledgerValid authority && Integrated.ledgerValid after) then
    some after
  else none

theorem complete_fn_op_facts {authority next : Integrated.World} {opScope : Nat}
    (h : completeFnOp authority opScope = some next) :
    opScope = authority.scope ∧
    next = Integrated.endBoundary authority (Integrated.scopedWrites authority opScope) ∧
    Integrated.WorldInvariant authority ∧
    Integrated.WorldInvariant next := by
  unfold completeFnOp at h
  change (if _ then _ else _) = some next at h
  split at h
  · rename_i hc
    have checks : opScope = authority.scope ∧
        (Integrated.ledgerValid authority = true ∧
          Integrated.ledgerValid (Integrated.endBoundary authority (Integrated.scopedWrites authority opScope)) = true) := by
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using hc
    cases h
    exact ⟨checks.1, rfl, Integrated.ledger_facts checks.2.1, Integrated.ledger_facts checks.2.2⟩
  · contradiction

theorem complete_fn_op_revokes_call_binding
    {authority next : Integrated.World} {opScope id : Nat}
    {path : Integrated.Path} {resolved : Integrated.Resolved}
    (h : completeFnOp authority opScope = some next)
    (hr : Integrated.resolve next path = some resolved)
    (hi : id ∈ Integrated.scopedWrites authority authority.scope)
    (hd : id ∈ resolved.binding.dependencies) :
    Integrated.live resolved = false := by
  obtain ⟨hscope, heq, _, hafter⟩ := complete_fn_op_facts h
  cases hl : Integrated.live resolved with
  | false => rfl
  | true =>
    have enabled := Integrated.resolved_live_dependencies hafter hr hl
    have ended : Integrated.scopeEnabled next resolved.binding.dependencies = false := by
      rw [heq, hscope]
      exact Integrated.dependency_ends_access hi hd
    simp [ended] at enabled

theorem complete_fn_op_ends_dependent_hold
    {authority next : Integrated.World} {opScope : Nat} {hold : Integrated.Hold}
    (h : completeFnOp authority opScope = some next)
    (hl : hold ∈ next.holds)
    (hi : hold.token ∈ Integrated.scopeClosure authority
      (Integrated.scopedWrites authority authority.scope)) :
    hold.active = false := by
  obtain ⟨hscope, heq, _, _⟩ := complete_fn_op_facts h
  rw [heq, hscope] at hl
  exact Integrated.dependent_hold_inactive hl hi

theorem complete_fn_op_preserves_non_scoped
    {authority next : Integrated.World} {opScope id : Nat} {token : Integrated.Token}
    (h : completeFnOp authority opScope = some next)
    (hlook : Integrated.lookupToken authority id = some token)
    (hnonTemp : token.scopedHold = false) :
    Integrated.lookupToken next id = some token := by
  obtain ⟨hscope, heq, _, _⟩ := complete_fn_op_facts h
  have notTemp : id ∉ Integrated.scopedWrites authority authority.scope := by
    intro hmem
    obtain ⟨selected, hs, htemp, _, _⟩ := Integrated.selected_scoped_write hmem
    have eq : token = selected := Option.some.inj (hlook.symm.trans hs)
    cases eq
    simp [hnonTemp] at htemp
  rw [heq, hscope, Integrated.unrelated_lookup notTemp]
  exact hlook

inductive OpKind where
  | directFn | algebraicCtl
  deriving Repr, DecidableEq

/-- Deep handler arm admissibility: `ctl` prefix must match the operation kind
(`E0623`) and the arm RHS cannot be a one-shot `&once` closure or `ctl(...)`
continuation (`E0534`). -/
def validHandlerArm (opKind : OpKind) (armHasCtlPrefix armIsOneShot : Bool) : Bool :=
  (decide (opKind = .algebraicCtl) == armHasCtlPrefix) && !armIsOneShot

theorem valid_handler_arm_iff (opKind : OpKind) (armHasCtlPrefix armIsOneShot : Bool) :
    validHandlerArm opKind armHasCtlPrefix armIsOneShot = true ↔
      decide (opKind = .algebraicCtl) = armHasCtlPrefix ∧ armIsOneShot = false := by
  simp [validHandlerArm, Bool.and_eq_true]

/-- `absorb_panic` boundary isolation (`E0608`): forbids outer live state, outward
effects, outer `ctl` handlers, and outer must-consume captures. Local `with { ctl ... }`
contained inside the `absorb_panic` closure does not set `usesOuterCtlHandler`. -/
def absorbPanicAdmissible (pureSources : List Source) (body : Summary)
    (outerEnv : List SourceInstance) (usesOuterCtlHandler capturesMustConsume : Bool) : Bool :=
  body.rootReturn.isEmpty &&
  body.contained.isEmpty &&
  body.writes.isEmpty &&
  body.retained.isEmpty &&
  body.effects.isEmpty &&
  body.namedReads.all (isPureInstance pureSources) &&
  body.createdEnvironments.all (isPureInstance pureSources) &&
  outerEnv.all (isPureInstance pureSources) &&
  !usesOuterCtlHandler &&
  !capturesMustConsume

theorem absorb_panic_isolated
    {pureSources : List Source} {body : Summary} {outerEnv : List SourceInstance}
    {usesOuterCtlHandler capturesMustConsume : Bool}
    (h : absorbPanicAdmissible pureSources body outerEnv usesOuterCtlHandler capturesMustConsume = true) :
    Summary.isPure pureSources body = true ∧
    (∀ o ∈ outerEnv, isPureInstance pureSources o = true) ∧
    usesOuterCtlHandler = false ∧
    capturesMustConsume = false := by
  simp only [absorbPanicAdmissible, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨hroot, hcont⟩, hwr⟩, hret⟩, heff⟩, hreads⟩, hcrenv⟩, henv⟩, hctl⟩, hmc⟩
  refine ⟨?_, henv, hctl, hmc⟩
  have hroot' : body.rootReturn = [] := List.isEmpty_iff.mp hroot
  have hcont' : body.contained = [] := List.isEmpty_iff.mp hcont
  simpa [Summary.isPure, hroot', hcont', hwr, hret, heff, List.all_eq_true] using
    And.intro hreads hcrenv

/-- `derive` update callback admissibility (`E0607`): forbids invoking outer or
unhandled `ctl` operations so a confined `Draft<T>` can never escape or persist
across a suspended continuation. -/
def deriveCallbackAdmissible (usesOuterCtl hasUnhandledCtl : Bool) : Bool :=
  !usesOuterCtl && !hasUnhandledCtl

theorem derive_rejects_outer_ctl (usesOuterCtl hasUnhandledCtl : Bool) :
    deriveCallbackAdmissible usesOuterCtl hasUnhandledCtl = true ↔
      usesOuterCtl = false ∧ hasUnhandledCtl = false := by
  simp [deriveCallbackAdmissible, Bool.and_eq_true]

end RilAccess.CoreBoundary
