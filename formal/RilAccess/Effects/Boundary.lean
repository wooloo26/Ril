import RilAccess.Contracts
import RilAccess.Access.Lifetime

/-! The state/provenance and direct `fn`-effect handler boundary kernel.
Ril effects consist exclusively of direct tail-resumptive `fn` operations:
- Effect handling discharges covered `@Eff` labels while preserving handler and
  cleanup state/environment obligations.
- Completing a `fn` operation arm revokes temporary `mut` operation parameters and
  dependent observers/loans while preserving outer and retained authority.
- Across concurrent boundaries (`E0615`), only pure stateless `fn` handlers with
  admissible outward effects may cross fibers. -/
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
  handlerEnvironment : List Origin
  cleanupEnvironment : List Origin
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
  summary.rootReturn.map (fun origin => ⟨.rootReturn, origin, mechanism⟩) ++
  summary.contained.map (fun origin => ⟨.containedReturn, origin, mechanism⟩) ++
  summary.writes.map (fun origin => ⟨.write, origin, mechanism⟩) ++
  summary.retained.map (fun origin => ⟨.retain, origin, mechanism⟩) ++
  summary.createdEnvironments.map (fun origin => ⟨.capture, origin, mechanism⟩) ++
  summary.namedReads.map (fun origin => ⟨.read, origin, mechanism⟩)

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
    localEvent event.kind = true ∧ owned activation scope event.origin = true ∧
      confined activation scope (footprint boundary) = true := discharge_only_confined he hn

theorem external_environment_blocks_discharge
    (he : origin ∈ boundary.handlerEnvironment ++ boundary.cleanupEnvironment)
    (ho : owned activation scope origin = false) :
    outward boundary activation scope = state boundary := by
  have hn : confined activation scope (footprint boundary) = false := by
    cases hc : confined activation scope (footprint boundary) with
    | false => rfl
    | true =>
      have hm : origin ∈ (footprint boundary).roots ++ (footprint boundary).environments := by
        apply List.mem_append_right
        apply List.mem_append_left
        apply List.mem_append_left
        apply List.mem_append_left
        exact he
      have hp := confined_roots hc hm
      simp [ho] at hp
  simp [outward, discharge, hn]

theorem handled_handler_and_cleanup_writes_survive
    (he : origin ∈ boundary.handler.writes ∨ origin ∈ boundary.cleanup.writes)
    (ho : owned activation scope origin = false) :
    ∃ event ∈ outward boundary activation scope, event.kind = .write ∧ event.origin = origin := by
  have eventPresent : ∃ event ∈ state boundary, event.kind = .write ∧ event.origin = origin := by
    rcases he with hh | hc
    · refine ⟨⟨.write, origin, .handler⟩, ?_, rfl, rfl⟩
      apply List.mem_append_left
      apply List.mem_append_right
      simp [events, hh]
    · refine ⟨⟨.write, origin, .cleanup⟩, ?_, rfl, rfl⟩
      apply List.mem_append_right
      simp [events, hc]
  obtain ⟨event, hev, hk, heq⟩ := eventPresent
  refine ⟨event, List.mem_filter.mpr ⟨hev, ?_⟩, hk, heq⟩
  simp [heq, ho]

/-- Direct 1-shot `fn` operation completion over the authority ledger: returning
from the handler arm revokes temporary `mut` operation parameters for `opScope`
while preserving retained and outer non-temporary tokens. -/
def completeFnOp (authority : Integrated.World) (opScope : Nat) : Option Integrated.World :=
  let after := Integrated.endBoundary authority (Integrated.temporaryWrites authority opScope)
  if decide (opScope = authority.scope) &&
      (Integrated.ledgerValid authority && Integrated.ledgerValid after) then
    some after
  else none

theorem complete_fn_op_facts {authority next : Integrated.World} {opScope : Nat}
    (h : completeFnOp authority opScope = some next) :
    opScope = authority.scope ∧
    next = Integrated.endBoundary authority (Integrated.temporaryWrites authority opScope) ∧
    Integrated.WorldInvariant authority ∧
    Integrated.WorldInvariant next := by
  unfold completeFnOp at h
  change (if _ then _ else _) = some next at h
  split at h
  · rename_i hc
    have checks : opScope = authority.scope ∧
        (Integrated.ledgerValid authority = true ∧
          Integrated.ledgerValid (Integrated.endBoundary authority (Integrated.temporaryWrites authority opScope)) = true) := by
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using hc
    cases h
    exact ⟨checks.1, rfl, Integrated.ledger_facts checks.2.1, Integrated.ledger_facts checks.2.2⟩
  · contradiction

theorem complete_fn_op_revokes_temporary_permission
    {authority next : Integrated.World} {opScope id : Nat}
    {path : Integrated.Path} {resolved : Integrated.Resolved}
    (h : completeFnOp authority opScope = some next)
    (hr : Integrated.resolve next path = some resolved)
    (hi : id ∈ Integrated.temporaryWrites authority authority.scope)
    (hd : id ∈ resolved.permission.dependencies) :
    Integrated.live resolved = false := by
  obtain ⟨hscope, heq, _, hafter⟩ := complete_fn_op_facts h
  cases hl : Integrated.live resolved with
  | false => rfl
  | true =>
    have enabled := Integrated.resolved_live_dependencies hafter hr hl
    have ended : Integrated.lifetimeEnabled next resolved.permission.dependencies = false := by
      rw [heq, hscope]
      exact Integrated.dependency_ends_access hi hd
    simp [ended] at enabled

theorem complete_fn_op_ends_dependent_loan
    {authority next : Integrated.World} {opScope : Nat} {loan : Integrated.Loan}
    (h : completeFnOp authority opScope = some next)
    (hl : loan ∈ next.loans)
    (hi : loan.token ∈ Integrated.lifetimeClosure authority
      (Integrated.temporaryWrites authority authority.scope)) :
    loan.active = false := by
  obtain ⟨hscope, heq, _, _⟩ := complete_fn_op_facts h
  rw [heq, hscope] at hl
  exact Integrated.dependent_loan_inactive hl hi

theorem complete_fn_op_preserves_non_temporary
    {authority next : Integrated.World} {opScope id : Nat} {token : Integrated.Token}
    (h : completeFnOp authority opScope = some next)
    (hlook : Integrated.lookupToken authority id = some token)
    (hnonTemp : token.temporary = false) :
    Integrated.lookupToken next id = some token := by
  obtain ⟨hscope, heq, _, _⟩ := complete_fn_op_facts h
  have notTemp : id ∉ Integrated.temporaryWrites authority authority.scope := by
    intro hmem
    obtain ⟨selected, hs, htemp, _, _⟩ := Integrated.selected_temporary hmem
    have eq : token = selected := Option.some.inj (hlook.symm.trans hs)
    cases eq
    simp [hnonTemp] at htemp
  rw [heq, hscope, Integrated.unrelated_lookup notTemp]
  exact hlook

/-- E0615 concurrent handler capture guard: only pure stateless `fn` handlers with
no writes, retentions, or reference returns, pure immutable Ril/static reads and
captured environments, and admissible outward effects may cross fiber boundaries. -/
def concurrentShareableFnHandler (pureSources : List Source) (admissibleEffects : List Nat)
    (handler : Summary) (handlerEnv : List Origin) : Bool :=
  handler.rootReturn.isEmpty &&
  handler.contained.isEmpty &&
  handler.writes.isEmpty &&
  handler.retained.isEmpty &&
  handler.namedReads.all (isPureOrigin pureSources) &&
  handler.createdEnvironments.all (isPureOrigin pureSources) &&
  handlerEnv.all (isPureOrigin pureSources) &&
  handler.effects.all (fun e => decide (e ∈ admissibleEffects))

def dischargeSharedFnEffect (branch handler : Summary) (effect : Nat) : Summary :=
  (branch.handle effect).combine handler

theorem concurrent_handler_pure_and_stateless
    {pureSources : List Source} {admissibleEffects : List Nat}
    {handler : Summary} {handlerEnv : List Origin}
    (h : concurrentShareableFnHandler pureSources admissibleEffects handler handlerEnv = true) :
    { handler with effects := [] }.isPure pureSources = true ∧
    (∀ o ∈ handlerEnv, isPureOrigin pureSources o = true) ∧
    (∀ e ∈ handler.effects, e ∈ admissibleEffects) := by
  simp only [concurrentShareableFnHandler, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨hroot, hcont⟩, hwr⟩, hret⟩, hreads⟩, hcrenv⟩, henv⟩, heff⟩
  refine ⟨?_, henv, heff⟩
  simp only [Summary.isPure, List.isEmpty_nil, Bool.true_and, Bool.and_eq_true, List.all_eq_true]
  exact ⟨⟨⟨⟨⟨hroot, hcont⟩, hwr⟩, hret⟩, hreads⟩, hcrenv⟩

theorem shared_fn_handler_preserves_branch_isolation
    {pureSources : List Source} {admissibleEffects : List Nat}
    {branch handler : Summary} {handlerEnv : List Origin} {effect : Nat}
    (h : concurrentShareableFnHandler pureSources admissibleEffects handler handlerEnv = true) :
    (dischargeSharedFnEffect branch handler effect).writes = branch.writes ∧
    (dischargeSharedFnEffect branch handler effect).retained = branch.retained ∧
    (dischargeSharedFnEffect branch handler effect).rootReturn = branch.rootReturn ∧
    (dischargeSharedFnEffect branch handler effect).contained = branch.contained ∧
    (∀ e ∈ (dischargeSharedFnEffect branch handler effect).effects,
      (e ∈ branch.effects ∧ e ≠ effect) ∨ e ∈ admissibleEffects) ∧
    (∀ o ∈ (dischargeSharedFnEffect branch handler effect).namedReads,
      o ∈ branch.namedReads ∨ isPureOrigin pureSources o = true) := by
  have hstat := concurrent_handler_pure_and_stateless h
  have hpure := hstat.1
  simp only [Summary.isPure, List.isEmpty_nil, Bool.true_and, Bool.and_eq_true,
    List.isEmpty_iff, List.all_eq_true] at hpure
  rcases hpure with ⟨⟨⟨⟨⟨hroot, hcont⟩, hwr⟩, hret⟩, hreads⟩, _⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [dischargeSharedFnEffect, Summary.combine, Summary.handle, hwr]
  · simp [dischargeSharedFnEffect, Summary.combine, Summary.handle, hret]
  · simp [dischargeSharedFnEffect, Summary.combine, Summary.handle, hroot]
  · simp [dischargeSharedFnEffect, Summary.combine, Summary.handle, hcont]
  · intro e he
    simp only [dischargeSharedFnEffect, Summary.combine, Summary.handle, List.mem_append,
      List.mem_filter, bne_iff_ne, ne_eq] at he
    rcases he with hb | hh
    · exact Or.inl hb
    · exact Or.inr (hstat.2.2 e hh)
  · intro o ho
    simp only [dischargeSharedFnEffect, Summary.combine, Summary.handle, List.mem_append] at ho
    rcases ho with hb | hh
    · exact Or.inl hb
    · exact Or.inr (hreads o hh)

end RilAccess.CoreBoundary
