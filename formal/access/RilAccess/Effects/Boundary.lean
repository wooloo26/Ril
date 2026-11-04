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

def outward (boundary : Boundary) (activation task scope : Nat) : List Event :=
  discharge activation task scope (footprint boundary) (state boundary)

theorem handled_state_components (boundary : Boundary) (effect : Nat) :
    (handled boundary effect).rootReturn = boundary.body.rootReturn ++ boundary.handler.rootReturn ++ boundary.cleanup.rootReturn ∧
    (handled boundary effect).contained = boundary.body.contained ++ boundary.handler.contained ++ boundary.cleanup.contained ∧
    (handled boundary effect).writes = boundary.body.writes ++ boundary.handler.writes ++ boundary.cleanup.writes ∧
    (handled boundary effect).retained = boundary.body.retained ++ boundary.handler.retained ++ boundary.cleanup.retained ∧
    (handled boundary effect).createdEnvironments = boundary.body.createdEnvironments ++ boundary.handler.createdEnvironments ++ boundary.cleanup.createdEnvironments ∧
    (handled boundary effect).namedReads = boundary.body.namedReads ++ boundary.handler.namedReads ++ boundary.cleanup.namedReads :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem discharged_state_requires_complete_confinement
    (he : event ∈ state boundary) (hn : event ∉ outward boundary activation task scope) :
    localEvent event.kind = true ∧ owned activation task scope event.origin = true ∧
      confined activation task scope (footprint boundary) = true := discharge_only_confined he hn

theorem external_environment_blocks_discharge
    (he : origin ∈ boundary.handlerEnvironment ++ boundary.cleanupEnvironment)
    (ho : owned activation task scope origin = false) :
    outward boundary activation task scope = state boundary := by
  have hn : confined activation task scope (footprint boundary) = false := by
    cases hc : confined activation task scope (footprint boundary) with
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
    (ho : owned activation task scope origin = false) :
    ∃ event ∈ outward boundary activation task scope, event.kind = .write ∧ event.origin = origin := by
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

end RilAccess.CoreBoundary
