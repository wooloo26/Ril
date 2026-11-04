import RilAccess.Access.Proofs

namespace RilAccess.Integrated

variable {w next : World} {operation : Atom} {code : Code} {worlds : List World}
  {program : Syntax} {analysis : Analysis} {state : RawState}

def FaultFree : Erased → RawState → Prop
  | .atom operation, state => ∃ next, rawStep operation state = some next
  | .sequence first second, state => FaultFree first state ∧
      ∀ middle ∈ execute first state, FaultFree second middle
  | .choice left right, state => FaultFree left state ∧ FaultFree right state

theorem infer_faultFree (h : infer code w = .ok worlds) : FaultFree (erase code) w.raw := by
  induction code generalizing w worlds with
  | atom operation =>
    cases hc : checkAtom operation w with
    | error error => simp [infer, hc] at h
    | ok result => exact ⟨result.raw, checkAtom_erases hc⟩
  | sequence first second ihFirst ihSecond =>
    cases hf : infer first w with
    | error error => simp [infer, hf] at h
    | ok front =>
      refine ⟨ihFirst hf, ?_⟩
      intro middle hm
      obtain ⟨world, hw, hraw⟩ := infer_simulation hf hm
      have htail : checkMany (infer second) front = .ok worlds := by simpa [infer, hf] using h
      obtain ⟨tail, ht, _⟩ := checkMany_each (infer second) htail hw
      simpa [hraw] using ihSecond ht
  | choice left right ihLeft ihRight =>
    cases hl : infer left w with
    | error error => simp [infer, hl] at h
    | ok l =>
      cases hr : infer right w with
      | error error => simp [infer, hl, hr] at h
      | ok r => exact ⟨ihLeft hl, ihRight hr⟩

theorem FaultFree.progress {code : Erased} (h : FaultFree code state) :
    ∃ result, result ∈ execute code state := by
  induction code generalizing state with
  | atom operation =>
    obtain ⟨result, hr⟩ := h
    exact ⟨result, by simp [execute, hr]⟩
  | sequence first second ihFirst ihSecond =>
    obtain ⟨middle, hm⟩ := ihFirst h.1
    obtain ⟨result, hr⟩ := ihSecond (h.2 middle hm)
    exact ⟨result, List.mem_flatMap.mpr ⟨middle, hm, hr⟩⟩
  | choice left right ihLeft _ =>
    obtain ⟨result, hr⟩ := ihLeft h.1
    exact ⟨result, List.mem_append_left _ hr⟩

theorem rawStep_keeps_events {operation : RawAtom} {next : RawState}
    (h : rawStep operation state = some next)
    (he : event ∈ state.observations) : event ∈ next.observations := by
  cases operation with
  | allocate destination =>
    simp [rawStep] at h
    subst next
    exact he
  | copy path destination =>
    cases hp : rawPath state path with
    | none => simp [rawStep, hp] at h
    | some pointer =>
      simp [rawStep, hp] at h
      subst next
      exact he
  | observe kind path =>
    cases hp : rawPath state path with
    | none => simp [rawStep, hp] at h
    | some pointer =>
      simp [rawStep, hp] at h
      subst next
      exact List.mem_cons_of_mem _ he
  | pairWrite left right =>
    cases hl : rawPath state left with
    | none => simp [rawStep, hl] at h
    | some l =>
      cases hr : rawPath state right with
      | none => simp [rawStep, hl, hr] at h
      | some r =>
        simp [rawStep, hl, hr] at h
        subst next
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he)
  | skip =>
    cases h
    exact he

theorem execute_keeps_events {code : Erased} (hr : result ∈ execute code state)
    (he : event ∈ state.observations) : event ∈ result.observations := by
  induction code generalizing state result with
  | atom operation =>
    have hs : rawStep operation state = some result := by simpa [execute] using hr
    exact rawStep_keeps_events hs he
  | sequence first second ihFirst ihSecond =>
    obtain ⟨middle, hm, hfinal⟩ := List.mem_flatMap.mp hr
    exact ihSecond hfinal (ihFirst hm he)
  | choice left right ihLeft ihRight =>
    rcases List.mem_append.mp hr with hr | hr
    · exact ihLeft hr he
    · exact ihRight hr he

/-- All finite operational prefixes, including branch/sequence intermediate states. -/
inductive Prefix : Erased → RawState → RawState → Prop where
  | start {code : Erased} {state : RawState} : Prefix code state state
  | atom {operation : RawAtom} {state next : RawState} :
      rawStep operation state = some next → Prefix (.atom operation) state next
  | sequenceFirst {first second : Erased} {state middle : RawState} :
      Prefix first state middle → Prefix (.sequence first second) state middle
  | sequenceSecond {first second : Erased} {state middle next : RawState} :
      middle ∈ execute first state → Prefix second middle next →
      Prefix (.sequence first second) state next
  | choiceLeft {left right : Erased} {state next : RawState} :
      Prefix left state next → Prefix (.choice left right) state next
  | choiceRight {left right : Erased} {state next : RawState} :
      Prefix right state next → Prefix (.choice left right) state next

theorem prefix_event_extends {code : Erased} {middle : RawState}
    (h : Prefix code state middle) (hf : FaultFree code state)
    (he : event ∈ middle.observations) :
    ∃ result ∈ execute code state, event ∈ result.observations := by
  induction h with
  | start =>
    obtain ⟨result, hr⟩ := hf.progress
    exact ⟨result, hr, execute_keeps_events hr he⟩
  | atom hr => exact ⟨_, by simp [execute, hr], he⟩
  | @sequenceFirst first second state middle _ ih =>
    obtain ⟨left, hl, hevent⟩ := ih hf.1 he
    obtain ⟨result, hr⟩ := (hf.2 left hl).progress
    exact ⟨result, List.mem_flatMap.mpr ⟨left, hl, hr⟩, execute_keeps_events hr hevent⟩
  | @sequenceSecond first second state middle next hm _ ih =>
    obtain ⟨result, hr, hevent⟩ := ih (hf.2 middle hm) he
    exact ⟨result, List.mem_flatMap.mpr ⟨middle, hm, hr⟩, hevent⟩
  | choiceLeft _ ih =>
    obtain ⟨result, hr, hevent⟩ := ih hf.1 he
    exact ⟨result, List.mem_append_left _ hr, hevent⟩
  | choiceRight _ ih =>
    obtain ⟨result, hr, hevent⟩ := ih hf.2 he
    exact ⟨result, List.mem_append_right _ hr, hevent⟩

theorem source_progress (h : check program = .ok analysis) :
    ∃ result, result ∈ sourceExecute program initialWorld.raw := by
  rw [lower_correct]
  exact (infer_faultFree (check_infer h).1).progress

theorem every_prefix_authorized (h : check program = .ok analysis)
    {middle : RawState}
    (hp : Prefix (erase (lower program)) initialWorld.raw middle)
    (he : event ∈ middle.observations) :
    event.pointer.source ∈ analysis.origins ∧
      ∃ evidence, evidence.observation = event ∧ authorized evidence = true := by
  obtain ⟨result, hr, hevent⟩ := prefix_event_extends hp (infer_faultFree (check_infer h).1) he
  rw [← lower_correct] at hr
  exact access_and_provenance h hr hevent

theorem checkAtom_grants (h : checkAtom operation w = .ok next) :
    next.grants = expectedGrants w operation := by
  unfold checkAtom at h
  split at h
  · contradiction
  · split at h
    · rename_i hg
      cases h
      have hh : (certified next = true ∧ rawStep (eraseAtom operation) w.raw = some next.raw) ∧
          next.grants = expectedGrants w operation := by
        simpa only [Bool.and_eq_true, decide_eq_true_eq] using hg
      exact hh.2
    · contradiction

theorem atomic_grant_origin (h : checkAtom operation w = .ok next) (hg : grant ∈ next.grants) :
    grant ∈ w.grants ∨ (grant.source, grant.declared, grant.schema) ∈ atomDeclarations operation := by
  rw [checkAtom_grants h] at hg
  cases operation <;> simp only [expectedGrants] at hg
  all_goals first
    | exact Or.inl hg
    | (rcases List.mem_cons.mp hg with rfl | hg
       · exact Or.inr (by simp [atomDeclarations])
       · exact Or.inl hg)

theorem infer_grant_origin (h : infer code w = .ok worlds) (hm : result ∈ worlds)
    (hg : grant ∈ result.grants) :
    grant ∈ w.grants ∨ (grant.source, grant.declared, grant.schema) ∈ declarations code := by
  induction code generalizing w worlds result with
  | atom operation =>
    cases hc : checkAtom operation w with
    | error error => simp [infer, hc] at h
    | ok next =>
      simp only [infer, hc, except_bind_ok, except_pure, Except.ok.injEq] at h
      subst worlds
      simp only [List.mem_singleton] at hm
      subst result
      exact atomic_grant_origin hc hg
  | sequence first second ihFirst ihSecond =>
    cases hf : infer first w with
    | error error => simp [infer, hf] at h
    | ok front =>
      have htail : checkMany (infer second) front = .ok worlds := by simpa [infer, hf] using h
      obtain ⟨input, hi, tail, ht, hm⟩ := checkMany_outputs (infer second) htail hm
      rcases ihSecond ht hm hg with hprevious | hsecond
      · rcases ihFirst hf hi hprevious with hold | hfirst
        · exact Or.inl hold
        · exact Or.inr (List.mem_append_left _ hfirst)
      · exact Or.inr (List.mem_append_right _ hsecond)
  | choice left right ihLeft ihRight =>
    cases hl : infer left w with
    | error error => simp [infer, hl] at h
    | ok l =>
      cases hr : infer right w with
      | error error => simp [infer, hl, hr] at h
      | ok r =>
        simp only [infer, hl, hr, except_bind_ok, except_pure, Except.ok.injEq] at h
        subst worlds
        rcases List.mem_append.mp hm with hm | hm
        · rcases ihLeft hl hm hg with hold | hleft
          · exact Or.inl hold
          · exact Or.inr (List.mem_append_left _ hleft)
        · rcases ihRight hr hm hg with hold | hright
          · exact Or.inl hold
          · exact Or.inr (List.mem_append_right _ hright)

theorem certified_grant_member (h : certified world = true) (he : evidence ∈ world.evidence) :
    evidence.resolved.grant ∈ world.grants := by
  have hall : world.evidence.all (fun e => decide (e.resolved.grant ∈ world.grants)) = true := by
    simp only [certified, Bool.and_eq_true] at h
    exact h.2
  exact of_decide_eq_true (List.all_eq_true.mp hall evidence he)

/-- Each runtime write is backed by an actual mutable allocation declaration in
the checked syntax, not by a caller-provided grant or a forged snapshot. -/
theorem original_declaration_covered (h : check program = .ok analysis)
    (hr : state ∈ sourceExecute program initialWorld.raw) (he : event ∈ state.observations) :
    ∃ evidence, evidence.observation = event ∧ authorized evidence = true ∧
      (evidence.resolved.grant.source, evidence.resolved.grant.declared,
        evidence.resolved.grant.schema) ∈ declarations (lower program) := by
  have hi := (check_infer h).1
  rw [lower_correct] at hr
  obtain ⟨world, hm, hraw⟩ := infer_simulation hi hr
  obtain ⟨evidence, hem, heq, hsafe⟩ := certified_evidence (infer_certified hi hm)
    (by simpa [hraw] using he)
  have hg := certified_grant_member (infer_certified hi hm) hem
  rcases infer_grant_origin hi hm hg with hbad | hdeclared
  · simp [initialWorld] at hbad
  · exact ⟨evidence, heq, hsafe, hdeclared⟩

end RilAccess.Integrated
