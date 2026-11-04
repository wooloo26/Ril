import RilAccess.Access.Core

namespace RilAccess.Integrated

@[simp] theorem except_bind_ok (value : α) (f : α → Except ε β) :
    (Except.ok value >>= f) = f value := rfl
@[simp] theorem except_bind_error (error : ε) (f : α → Except ε β) :
    (Except.error error >>= f) = .error error := rfl
@[simp] theorem except_map_ok (value : α) (f : α → β) :
    f <$> (Except.ok value : Except ε α) = .ok (f value) := rfl
@[simp] theorem except_map_error (error : ε) (f : α → β) :
    f <$> (Except.error error : Except ε α) = .error error := rfl
@[simp] theorem except_pure (value : α) : (pure value : Except ε α) = .ok value := rfl

variable {w next : World} {atom : Atom} {code : Code} {worlds : List World}
  {program : Syntax} {analysis : Analysis} {state : RawState}

theorem authorization_local (h : authorized e = true) : authorizedLocal e = true := by
  have hh : authorizedLocal e = true ∧ originalPolicy e = true := by
    simpa only [authorized, Bool.and_eq_true] using h
  exact hh.1

theorem authorization_original (h : authorized e = true) : originalPolicy e = true := by
  have hh : authorizedLocal e = true ∧ originalPolicy e = true := by
    simpa only [authorized, Bool.and_eq_true] using h
  exact hh.2

theorem receiving_cannot_upgrade (h : receiving w r mode scope = true)
    (hw : mode.access.writes = true) :
    r.effective.writes = true ∧ r.grant.declared.writes = true ∧ noTemporary r = true := by
  cases mode with
  | mk replaceable access => cases access <;> simp_all [receiving, Access.writes]

theorem original_member_write_bound (h : authorized evidence = true)
    (hr : evidence.rule = .write) :
    ∃ members access parent replaceable object,
      traverse evidence.resolved.grant.schema [] evidence.resolved.grant.declared
        evidence.observation.pointer.fields = some (members, access, parent, replaceable, object) ∧
      access.writes = true := by
  have hp := authorization_original h
  cases ht : traverse evidence.resolved.grant.schema [] evidence.resolved.grant.declared
      evidence.observation.pointer.fields with
  | none => simp [originalPolicy, ht] at hp
  | some result =>
    obtain ⟨members, access, parent, replaceable, object⟩ := result
    simp only [originalPolicy, ht, hr, Bool.and_eq_true] at hp
    exact ⟨members, access, parent, replaceable, object, rfl, hp.2⟩

theorem checkAtom_certified (h : checkAtom atom w = .ok next) : certified next = true := by
  unfold checkAtom at h
  split at h
  · contradiction
  · split at h
    · rename_i hg
      cases h
      have hh : (certified next = true ∧
          decide (rawStep (eraseAtom atom) w.raw = some next.raw) = true) ∧
          decide (next.grants = expectedGrants w atom) = true := by
        simpa only [Bool.and_eq_true] using hg
      exact hh.1.1
    · contradiction

theorem checkAtom_erases (h : checkAtom atom w = .ok next) :
    rawStep (eraseAtom atom) w.raw = some next.raw := by
  unfold checkAtom at h
  split at h
  · contradiction
  · split at h
    · rename_i hg
      cases h
      have hh : (certified next = true ∧ rawStep (eraseAtom atom) w.raw = some next.raw) ∧
          next.grants = expectedGrants w atom := by
        simpa only [Bool.and_eq_true, decide_eq_true_eq] using hg
      exact hh.1.2
    · contradiction

theorem checkAtom_transfer (h : checkAtom atom w = .ok next) : transfer w atom = some next := by
  unfold checkAtom at h
  split at h
  · contradiction
  · rename_i ht
    split at h
    · cases h
      exact ht
    · contradiction

theorem checkMany_each (f : World → Except Error (List World))
    (h : checkMany f inputs = .ok outputs) (hm : input ∈ inputs) :
    ∃ front, f input = .ok front ∧ ∀ output ∈ front, output ∈ outputs := by
  induction inputs generalizing outputs with
  | nil => simp at hm
  | cons first rest ih =>
    cases hf : f first with
    | error error => simp [checkMany, hf] at h
    | ok front =>
      cases ht : checkMany f rest with
      | error error => simp [checkMany, hf, ht] at h
      | ok tail =>
        simp only [checkMany, hf, ht, except_bind_ok, except_pure, Except.ok.injEq] at h
        subst outputs
        rcases List.mem_cons.mp hm with rfl | hm
        · exact ⟨front, hf, fun output ho => List.mem_append_left _ ho⟩
        · obtain ⟨result, hr, hin⟩ := ih ht hm
          exact ⟨result, hr, fun output ho => List.mem_append_right _ (hin output ho)⟩

theorem checkMany_outputs (f : World → Except Error (List World))
    (h : checkMany f inputs = .ok outputs) (hm : output ∈ outputs) :
    ∃ input ∈ inputs, ∃ front, f input = .ok front ∧ output ∈ front := by
  induction inputs generalizing outputs with
  | nil => simp [checkMany] at h; subst outputs; simp at hm
  | cons first rest ih =>
    cases hf : f first with
    | error error => simp [checkMany, hf] at h
    | ok front =>
      cases ht : checkMany f rest with
      | error error => simp [checkMany, hf, ht] at h
      | ok tail =>
        simp only [checkMany, hf, ht, except_bind_ok, except_pure, Except.ok.injEq] at h
        subst outputs
        rcases List.mem_append.mp hm with hl | hr
        · exact ⟨first, by simp, front, hf, hl⟩
        · obtain ⟨input, hi, result, hf, ho⟩ := ih ht hr
          exact ⟨input, List.mem_cons_of_mem _ hi, result, hf, ho⟩

/-- Every erased execution is matched, even though it performs no mode checks. -/
theorem infer_simulation (h : infer code w = .ok worlds)
    (hr : state ∈ execute (erase code) w.raw) :
    ∃ result ∈ worlds, result.raw = state := by
  induction code generalizing w worlds state with
  | atom operation =>
    cases hc : checkAtom operation w with
    | error error => simp [infer, hc] at h
    | ok result =>
      simp only [infer, hc, except_bind_ok, except_pure, Except.ok.injEq] at h
      subst worlds
      have he := checkAtom_erases hc
      simp [erase, execute, he] at hr
      exact ⟨result, by simp, hr.symm⟩
  | sequence first second ihFirst ihSecond =>
    cases hf : infer first w with
    | error error => simp [infer, hf] at h
    | ok front =>
      have hm : checkMany (infer second) front = .ok worlds := by simpa [infer, hf] using h
      obtain ⟨middle, hmiddle, hfinal⟩ := List.mem_flatMap.mp hr
      obtain ⟨firstResult, hfirst, hraw⟩ := ihFirst hf hmiddle
      obtain ⟨tail, htail, hin⟩ := checkMany_each (infer second) hm hfirst
      rw [← hraw] at hfinal
      obtain ⟨result, hresult, heq⟩ := ihSecond htail hfinal
      exact ⟨result, hin result hresult, heq⟩
  | choice left right ihLeft ihRight =>
    cases hl : infer left w with
    | error error => simp [infer, hl] at h
    | ok l =>
      cases hr' : infer right w with
      | error error => simp [infer, hl, hr'] at h
      | ok r =>
        simp only [infer, hl, hr', except_bind_ok, except_pure, Except.ok.injEq] at h
        subst worlds
        rcases List.mem_append.mp hr with hleft | hright
        · obtain ⟨result, hm, heq⟩ := ihLeft hl hleft
          exact ⟨result, List.mem_append_left _ hm, heq⟩
        · obtain ⟨result, hm, heq⟩ := ihRight hr' hright
          exact ⟨result, List.mem_append_right _ hm, heq⟩

theorem infer_certified (h : infer code w = .ok worlds) (hm : result ∈ worlds) :
    certified result = true := by
  induction code generalizing w worlds with
  | atom operation =>
    cases hc : checkAtom operation w with
    | error error => simp [infer, hc] at h
    | ok next =>
      simp only [infer, hc, except_bind_ok, except_pure, Except.ok.injEq] at h
      subst worlds
      simp only [List.mem_singleton] at hm
      subst result
      exact checkAtom_certified hc
  | sequence first second _ ihSecond =>
    cases hf : infer first w with
    | error error => simp [infer, hf] at h
    | ok front =>
      have htail : checkMany (infer second) front = .ok worlds := by simpa [infer, hf] using h
      obtain ⟨input, _, output, hout, hm⟩ := checkMany_outputs (infer second) htail hm
      exact ihSecond hout hm
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
        · exact ihLeft hl hm
        · exact ihRight hr hm

theorem lower_correct (program : Syntax) (state : RawState) :
    sourceExecute program state = execute (erase (lower program)) state := by
  induction program generalizing state with
  | command operation => rfl
  | sequence first second ihFirst ihSecond =>
    simp only [sourceExecute, lower, erase, execute, ihFirst]
    congr 1
    funext middle
    exact ihSecond middle
  | branch left right ihLeft ihRight => simp [sourceExecute, lower, erase, execute, ihLeft, ihRight]
  | block body ih => simp [sourceExecute, lower, erase, execute, eraseAtom, rawStep, ih]
  | borrow path destination body ih =>
    simp only [sourceExecute, lower, erase, execute, eraseAtom, rawStep]
    cases hp : rawPath state path <;> simp [ih]

theorem check_infer (h : check program = .ok analysis) :
    infer (lower program) initialWorld = .ok analysis.worlds ∧
    analysis.origins = analysis.worlds.flatMap worldOrigins := by
  unfold check at h
  split at h <;> try contradiction
  cases hi : infer (lower program) initialWorld with
  | error error => simp [hi] at h
  | ok worlds =>
    simp only [hi, except_bind_ok] at h
    split at h
    · contradiction
    · split at h
      · contradiction
      · cases h
        exact ⟨rfl, rfl⟩

theorem check_reachable_uses (h : check program = .ok analysis)
    (hr : requirement ∈ analysis.worlds.flatMap World.requirements) :
    satisfiesUse (allUses analysis.worlds) requirement = true := by
  unfold check at h
  split at h <;> try contradiction
  cases hi : infer (lower program) initialWorld with
  | error error => simp [hi] at h
  | ok worlds =>
    simp only [hi, except_bind_ok] at h
    split at h
    · contradiction
    · split at h
      · contradiction
      · rename_i hnone
        cases h
        have hn := List.find?_eq_none.mp hnone requirement hr
        simpa using hn

theorem check_unique_declarations (h : check program = .ok analysis) :
    (binders (lower program)).Nodup := by
  apply of_decide_eq_true
  cases hn : decide (binders (lower program)).Nodup with
  | false => simp [check, hn] at h
  | true => rfl

theorem certified_evidence (h : certified world = true) (he : event ∈ world.raw.observations) :
    ∃ evidence ∈ world.evidence, evidence.observation = event ∧ authorized evidence = true := by
  have hs : (world.raw.observations = world.evidence.map Evidence.observation ∧
      world.evidence.all authorized = true) ∧
      world.evidence.all (fun e => decide (e.resolved.grant ∈ world.grants)) = true := by
    simpa only [certified, Bool.and_eq_true, decide_eq_true_eq] using h
  rw [hs.1.1] at he
  obtain ⟨evidence, hm, heq⟩ := List.mem_map.mp he
  exact ⟨evidence, hm, heq, List.all_eq_true.mp hs.1.2 evidence hm⟩

/-- End-to-end source theorem: no caller-supplied lowering or boundary facts. -/
theorem access_and_provenance (h : check program = .ok analysis)
    (hr : state ∈ sourceExecute program initialWorld.raw)
    (he : event ∈ state.observations) :
    event.pointer.source ∈ analysis.origins ∧
      ∃ evidence, evidence.observation = event ∧ authorized evidence = true := by
  obtain ⟨hi, horigins⟩ := check_infer h
  rw [lower_correct] at hr
  obtain ⟨world, hm, hraw⟩ := infer_simulation hi hr
  have hw : event ∈ world.raw.observations := by simpa [hraw] using he
  obtain ⟨evidence, _, heq, hsafe⟩ := certified_evidence (infer_certified hi hm) hw
  refine ⟨?_, evidence, heq, hsafe⟩
  rw [horigins]
  exact List.mem_flatMap.mpr ⟨world, hm,
    List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨event, hw, rfl⟩))⟩

theorem storage_origin_coverage (h : check program = .ok analysis)
    (hr : state ∈ sourceExecute program initialWorld.raw) (hb : binding ∈ state.roots) :
    binding.2.source ∈ analysis.origins := by
  obtain ⟨hi, horigins⟩ := check_infer h
  rw [lower_correct] at hr
  obtain ⟨world, hm, hraw⟩ := infer_simulation hi hr
  have hw : binding ∈ world.raw.roots := by simpa [hraw] using hb
  rw [horigins]
  exact List.mem_flatMap.mpr ⟨world, hm,
    List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨binding, hw, rfl⟩))⟩

theorem authorized_interior_write (h : authorized evidence = true)
    (hr : evidence.rule = .write) :
    evidence.resolved.effective.writes = true ∧
    evidence.resolved.grant.declared.writes = true ∧
    live evidence.resolved = true ∧ noLoanConflict evidence.resolved evidence.loans = true := by
  have h := authorization_local h
  simp only [authorizedLocal, hr, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.2.1.2, h.2.2, h.1.1.1.1.2, h.1.1.1.2⟩

theorem authorized_write_path (h : authorized evidence = true)
    (hr : evidence.rule = .write) :
    evidence.resolved.permission.mode.access.writes = true ∧
      ∀ access ∈ evidence.resolved.members, access.writes = true := by
  have hw := (authorized_interior_write h hr).1
  have hpath : evidence.resolved.effective =
      pathAccess evidence.resolved.permission.mode.access evidence.resolved.members := by
    have h := authorization_local h
    simp only [authorizedLocal, hr, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.2
  rw [hpath] at hw
  exact ⟨path_write_requires_root hw, path_write_requires_members hw⟩

theorem authorized_scalar_replacement (h : authorized evidence = true)
    (hr : evidence.rule = .replaceScalar) :
    evidence.resolved.object = false ∧ evidence.resolved.replaceable = true ∧
    evidence.resolved.parentAccess.writes = true := by
  have h := authorization_local h
  simp_all [authorizedLocal]

theorem authorized_retention (h : authorized evidence = true)
    (hr : evidence.rule = .retain) : noTemporary evidence.resolved = true := by
  have h := authorization_local h
  simp_all [authorizedLocal]

theorem active_dependency_required (h : live r = true) (ht : token ∈ r.tokens) :
    token.active = true := by
  simp only [live, Bool.and_eq_true] at h
  have hall := List.all_eq_true.mp h.1.2 token ht
  have hh : token.active = true ∧ contains token.region r.pointer = true := by
    simpa only [Bool.and_eq_true] using hall
  exact hh.1

theorem independent_loan_blocks (h : noLoanConflict r loans = true) (hl : loan ∈ loans)
    (hoverlap : overlaps loan.region r.pointer = true)
    (hactive : loan.active = true)
    (hindependent : loan.token ∉ r.authorityOrigins) : False := by
  have hall := List.all_eq_true.mp h loan hl
  simp [hoverlap, hactive, hindependent] at hall

theorem simultaneous_participants_separated (h : authorized evidence = true)
    (hp : peer ∈ evidence.peers) : overlaps peer evidence.resolved.pointer = false := by
  have hall : evidence.peers.all (fun peer => !overlaps peer evidence.resolved.pointer) = true := by
    have h := authorization_local h
    simp_all [authorizedLocal]
  have hf := List.all_eq_true.mp hall peer hp
  simpa using hf

end RilAccess.Integrated
