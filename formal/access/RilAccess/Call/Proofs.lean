import RilAccess.Call.Core

namespace RilAccess.Calls

open Integrated

theorem checkMany_replace (h : checkMany first inputs = .ok outputs)
    (law : ∀ input ∈ inputs, ∀ front, first input = .ok front → second input = .ok front) :
    checkMany second inputs = .ok outputs := by
  induction inputs generalizing outputs with
  | nil => simpa [checkMany] using h
  | cons input rest ih =>
    cases hf : first input with
    | error error => simp [checkMany, hf] at h
    | ok front =>
      cases ht : checkMany first rest with
      | error error => simp [checkMany, hf, ht] at h
      | ok tail =>
        have hhead := law input (by simp) front hf
        have htail := ih ht (fun input hin front hf => law input (by simp [hin]) front hf)
        simpa [checkMany, hhead, htail, hf, ht] using h

theorem infer_agrees (h : infer program entry = .ok worlds) :
    Integrated.infer (lower program) entry = .ok worlds := by
  induction program generalizing entry worlds with
  | access body => exact h
  | sequence first second ihFirst ihSecond =>
    cases hf : infer first entry with
    | error error => simp [infer, hf] at h
    | ok front =>
      have hc : checkMany (infer second) front = .ok worlds := by simpa [infer, hf] using h
      have ht := checkMany_replace (second := Integrated.infer (lower second)) hc
        (fun input _ out hi => ihSecond hi)
      simpa [lower, Integrated.infer, ihFirst hf] using ht
  | branch left right ihLeft ihRight =>
    cases hl : infer left entry with
    | error error => simp [infer, hl] at h
    | ok l =>
      cases hr : infer right entry with
      | error error => simp [infer, hl, hr] at h
      | ok r => simpa [infer, lower, Integrated.infer, hl, hr, ihLeft hl, ihRight hr] using h
  | invoke arguments captures body ih =>
    rw [infer] at h
    split at h
    · cases hp : Integrated.infer (.sequence (.atom .enterScope) (prepare arguments)) entry with
      | error error => simp [hp] at h
      | ok prepared =>
        simp only [hp, except_bind_ok] at h
        have htranslated := checkMany_replace
          (second := Integrated.infer (.sequence (lower body) (.atom .leaveScope))) h ?_
        · change (Integrated.infer (.sequence (.atom .enterScope) (prepare arguments)) entry >>=
            fun front => checkMany (Integrated.infer (.sequence (lower body) (.atom .leaveScope))) front) =
              .ok worlds
          rw [hp, except_bind_ok]
          exact htranslated
        · intro input _ out hbody
          cases hb : infer body input with
          | error error => simp [hb] at hbody
          | ok front =>
            simp only [hb, except_bind_ok] at hbody
            split at hbody
            · simpa only [Integrated.infer, ih hb, except_bind_ok, finish] using hbody
            · contradiction
    · contradiction

theorem prepare_erases (arguments : List Argument) (state : RawState) :
    Integrated.execute (erase (prepare arguments)) state = prepareRaw arguments state := by
  induction arguments generalizing state with
  | nil => rfl
  | cons argument rest ih =>
    simp only [prepare, List.foldr_cons, erase, Integrated.execute, eraseAtom, prepareRaw]
    congr 1
    funext next
    exact ih next

theorem lower_correct (program : Syntax) (state : RawState) :
    execute program state = Integrated.execute (erase (lower program)) state := by
  induction program generalizing state with
  | access body => exact Integrated.lower_correct body state
  | sequence first second ihFirst ihSecond =>
    simp only [execute, lower, erase, Integrated.execute, ihFirst]
    congr 1
    funext next
    exact ihSecond next
  | branch left right ihLeft ihRight =>
    simp [execute, lower, erase, Integrated.execute, ihLeft, ihRight]
  | invoke arguments captures body ih =>
    simp only [execute, lower, erase, Integrated.execute, eraseAtom, rawStep]
    congr 1
    · funext next
      simp [← ih]
    · simp [prepare_erases]

theorem checked_core (h : check program = .ok analysis) :
    Integrated.infer (lower program) initialWorld = .ok analysis.worlds ∧
      analysis.origins = analysis.worlds.flatMap worldOrigins := by
  unfold check at h
  split at h <;> try contradiction
  cases hi : infer program initialWorld with
  | error error => simp [hi] at h
  | ok worlds =>
    simp only [hi, except_bind_ok] at h
    split at h
    · contradiction
    · split at h
      · contradiction
      · cases h
        exact ⟨infer_agrees hi, rfl⟩

theorem access_and_provenance (h : check program = .ok analysis)
    (hr : state ∈ execute program initialWorld.raw)
    (he : event ∈ state.observations) :
    event.pointer.source ∈ analysis.origins ∧
      ∃ evidence, evidence.observation = event ∧ authorized evidence = true := by
  obtain ⟨hi, horigins⟩ := checked_core h
  rw [lower_correct] at hr
  obtain ⟨world, hm, hraw⟩ := infer_simulation hi hr
  have hw : event ∈ world.raw.observations := by simpa [hraw] using he
  obtain ⟨evidence, _, heq, hsafe⟩ := certified_evidence (infer_certified hi hm) hw
  refine ⟨?_, evidence, heq, hsafe⟩
  rw [horigins]
  exact List.mem_flatMap.mpr ⟨world, hm,
    List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨event, hw, rfl⟩))⟩

theorem every_prefix_authorized (h : check program = .ok analysis)
    (hp : Prefix (erase (lower program)) initialWorld.raw middle)
    (he : event ∈ middle.observations) :
    event.pointer.source ∈ analysis.origins ∧
      ∃ evidence, evidence.observation = event ∧ authorized evidence = true := by
  obtain ⟨result, hr, hevent⟩ := prefix_event_extends hp (infer_faultFree (checked_core h).1) he
  rw [← lower_correct] at hr
  exact access_and_provenance h hr hevent

theorem source_progress (h : check program = .ok analysis) :
    ∃ result, result ∈ execute program initialWorld.raw := by
  rw [lower_correct]
  exact (infer_faultFree (checked_core h).1).progress

theorem retained_mode_needs_survival
    (h : requiredUse entry frontier argument = true) (hm : argument.mode = .retained) :
    ∃ token, parameterToken entry argument.formal = some token ∧
      ∃ world ∈ frontier, retainedBeyond token world = true := by
  unfold requiredUse at h
  split at h
  · contradiction
  · rename_i token htoken
    refine ⟨token, htoken, ?_⟩
    simpa [hm, List.any_eq_true] using h

end RilAccess.Calls
