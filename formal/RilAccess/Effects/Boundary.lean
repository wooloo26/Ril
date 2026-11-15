import RilAccess.Contracts

/-! The state/provenance boundary kernel. Handler selection and callback bodies
arrive through resolved contracts; effect elimination and local discharge must
preserve their state obligations and concrete environment identities. -/
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

/-- E0615 concurrent handler capture guard: only `fn` handlers (`isFn = true`) with
no writes, retentions, or reference returns, pure immutable Ril/static reads and
captured environments, and admissible outward effects may be shared across
`Scope::spawn` or `Parallel::*` boundaries. -/
def concurrentShareableFnHandler (pureSources : List Source) (admissibleEffects : List Nat)
    (isFn : Bool) (handler : Summary) (handlerEnv : List Origin) : Bool :=
  isFn &&
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

theorem ctl_handler_not_concurrent_shareable
    (pureSources : List Source) (admissibleEffects : List Nat)
    (handler : Summary) (handlerEnv : List Origin) :
    concurrentShareableFnHandler pureSources admissibleEffects false handler handlerEnv = false := by
  simp [concurrentShareableFnHandler]

theorem concurrent_handler_pure_and_stateless
    {pureSources : List Source} {admissibleEffects : List Nat}
    {isFn : Bool} {handler : Summary} {handlerEnv : List Origin}
    (h : concurrentShareableFnHandler pureSources admissibleEffects isFn handler handlerEnv = true) :
    isFn = true ∧
    { handler with effects := [] }.isPure pureSources = true ∧
    (∀ o ∈ handlerEnv, isPureOrigin pureSources o = true) ∧
    (∀ e ∈ handler.effects, e ∈ admissibleEffects) := by
  simp only [concurrentShareableFnHandler, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨hfn, hroot⟩, hcont⟩, hwr⟩, hret⟩, hreads⟩, hcrenv⟩, henv⟩, heff⟩
  refine ⟨hfn, ?_, henv, heff⟩
  simp only [Summary.isPure, List.isEmpty_nil, Bool.true_and, Bool.and_eq_true, List.all_eq_true]
  exact ⟨⟨⟨⟨⟨hroot, hcont⟩, hwr⟩, hret⟩, hreads⟩, hcrenv⟩

theorem shared_fn_handler_preserves_branch_isolation
    {pureSources : List Source} {admissibleEffects : List Nat}
    {isFn : Bool} {branch handler : Summary} {handlerEnv : List Origin} {effect : Nat}
    (h : concurrentShareableFnHandler pureSources admissibleEffects isFn handler handlerEnv = true) :
    (dischargeSharedFnEffect branch handler effect).writes = branch.writes ∧
    (dischargeSharedFnEffect branch handler effect).retained = branch.retained ∧
    (dischargeSharedFnEffect branch handler effect).rootReturn = branch.rootReturn ∧
    (dischargeSharedFnEffect branch handler effect).contained = branch.contained ∧
    (∀ e ∈ (dischargeSharedFnEffect branch handler effect).effects,
      (e ∈ branch.effects ∧ e ≠ effect) ∨ e ∈ admissibleEffects) ∧
    (∀ o ∈ (dischargeSharedFnEffect branch handler effect).namedReads,
      o ∈ branch.namedReads ∨ isPureOrigin pureSources o = true) := by
  have hstat := concurrent_handler_pure_and_stateless h
  have hpure := hstat.2.1
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
    · exact Or.inr (hstat.2.2.2 e hh)
  · intro o ho
    simp only [dischargeSharedFnEffect, Summary.combine, Summary.handle, List.mem_append] at ho
    rcases ho with hb | hh
    · exact Or.inl hb
    · exact Or.inr (hreads o hh)

end RilAccess.CoreBoundary
