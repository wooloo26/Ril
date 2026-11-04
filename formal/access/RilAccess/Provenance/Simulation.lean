import RilAccess.Provenance.Semantics

namespace RilAccess

theorem Trace.trans (hab : Trace p a b) (hbc : Trace p b c) : Trace p a c := by
  induction hbc with
  | refl => exact hab
  | tail _ step ih => exact .tail ih step

inductive SurfaceTrace (transition : σ → σ → Prop) : σ → σ → Prop where
  | refl : SurfaceTrace transition s s
  | tail : SurfaceTrace transition a b → transition b c → SurfaceTrace transition a c

/-- The explicit remaining obligation for a future elaborator/compiler. The
simulation concerns concrete transitions, not the desired static theorem. -/
structure Lowering (σ : Type) (transition : σ → σ → Prop)
    (events : σ → List Event) (p : ResolvedProgram) where
  encode : σ → Configuration
  initialState : σ
  initialCorrect : encode initialState = initial p.entry
  stepCorrect : ∀ a b, transition a b → Trace p (encode a) (encode b)
  eventsCorrect : ∀ s e, e ∈ events s → e ∈ (encode s).events

theorem lowering_trace (lowering : Lowering σ transition events p)
    (ht : SurfaceTrace transition a b) :
    Trace p (lowering.encode a) (lowering.encode b) := by
  induction ht with
  | refl => exact .refl
  | @tail b c _ step ih =>
    exact ih.trans (lowering.stepCorrect b c step)

theorem complete_sources_given_lowering (lowering : Lowering σ transition events p)
    (ha : analyze p = .ok analysis)
    (ht : SurfaceTrace transition lowering.initialState state)
    (he : event ∈ events state) :
    Fact.event event.kind event.origin.source ∈ analysis.facts := by
  have coreTrace := lowering_trace lowering ht
  rw [lowering.initialCorrect] at coreTrace
  exact provenance_coverage ha coreTrace (lowering.eventsCorrect state event he)

end RilAccess
