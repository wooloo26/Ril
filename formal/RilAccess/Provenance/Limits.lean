import RilAccess.Provenance.Semantics

namespace RilAccess

/-- An arbitrary deterministic small-step machine, with `none` meaning halted. -/
inductive Halts (step : Nat → Option Nat) : Nat → Prop where
  | stop : step state = none → Halts step state
  | next : step state = some next → Halts step next → Halts step state

inductive Instrumented where
  | running (state : Nat)
  | published
  deriving Repr, DecidableEq

inductive MachineStep (step : Nat → Option Nat) : Instrumented → Instrumented → Prop where
  | run : step state = some next → MachineStep step (.running state) (.running next)
  | publish : step state = none → MachineStep step (.running state) .published

inductive Publishes (step : Nat → Option Nat) : Instrumented → Prop where
  | here : Publishes step .published
  | before : MachineStep step a b → Publishes step b → Publishes step a

theorem halting_to_source (h : Halts step state) : Publishes step (.running state) := by
  induction h with
  | stop hs => exact .before (.publish hs) .here
  | next hs _ ih => exact .before (.run hs) ih

theorem source_to_halting (h : Publishes step start) :
    ∀ state, start = .running state → Halts step state := by
  induction h with
  | here => simp
  | before hs _ ih =>
    cases hs with
    | run he =>
      intro state heq
      cases heq
      exact .next he (ih _ rfl)
    | publish he =>
      intro state heq
      cases heq
      exact .stop he

theorem source_reachability_iff_halting :
    Publishes step (.running state) ↔ Halts step state :=
  ⟨fun h => source_to_halting h _ rfl, halting_to_source⟩

/-- The computational premise is explicit: the language can represent the diagonal
program associated with a computable proposed decider. This is not an axiom or
an assertion that the surface-to-core translation has already been verified. -/
def DiagonalRepresentable (halts : Nat → Prop) (computable : (Nat → Bool) → Prop) : Prop :=
  ∀ decide : Nat → Bool, computable decide → ∃ code, halts code ↔ decide code = false

theorem no_computable_exact_decider
    (decider : Nat → Bool)
    (diagonal : DiagonalRepresentable halts computable)
    (algorithm : computable decider)
    (exactness : ∀ code, decider code = true ↔ halts code) : False := by
  obtain ⟨code, hdiag⟩ := diagonal decider algorithm
  cases hv : decider code with
  | false =>
    have hh := hdiag.mpr hv
    have ht := (exactness code).mpr hh
    simp [hv] at ht
  | true =>
    have hh := (exactness code).mp hv
    have hf := hdiag.mp hh
    simp [hv] at hf

/-- Allocation-site abstraction intentionally forgets the unbounded serial. -/
theorem same_site_distinct_objects (s : Source) (activation task scope serial : Nat) :
    (Origin.mk s activation serial task scope).source =
      (Origin.mk s activation (serial + 1) task scope).source ∧
    Origin.mk s activation serial task scope ≠
      Origin.mk s activation (serial + 1) task scope := by
  refine ⟨rfl, ?_⟩
  intro he
  have hobj := congrArg Origin.object he
  simp at hobj

end RilAccess
