import Std

/-! A finite, executable Horn solver. No semantic safety assumption is used here. -/
namespace RilAccess

structure Rule (α : Type) where
  premises : List α
  conclusion : α
  deriving Repr, DecidableEq

variable {α : Type} {rules : List (Rule α)} {known facts : List α} {x : α}

inductive Derives (rules : List (Rule α)) : α → Prop where
  | rule (r) : r ∈ rules → (∀ x ∈ r.premises, Derives rules x) →
      Derives rules r.conclusion

def Closed (rules : List (Rule α)) (facts : List α) : Prop :=
  ∀ r ∈ rules, (∀ x ∈ r.premises, x ∈ facts) → r.conclusion ∈ facts

def Grounded (rules : List (Rule α)) (facts : List α) : Prop :=
  ∀ x ∈ facts, Derives rules x

def enabled [DecidableEq α] (rules : List (Rule α)) (known : List α) (x : α) : Bool :=
  rules.any fun r => decide (r.conclusion = x) && r.premises.all (fun y => decide (y ∈ known))

theorem enabled_iff [DecidableEq α] : enabled rules known x = true ↔
    ∃ r ∈ rules, r.conclusion = x ∧ ∀ y ∈ r.premises, y ∈ known := by
  simp [enabled, List.any_eq_true, List.all_eq_true]

/-- Each recursive call removes an enabled fact from a finite pending list. -/
def solveAux [DecidableEq α] (rules : List (Rule α)) (known pending : List α) : List α :=
  match _h : pending.find? (enabled rules known) with
  | none => known
  | some x => solveAux rules (x :: known) (pending.erase x)
termination_by pending.length
decreasing_by
  have hm := List.mem_of_find?_eq_some _h
  have he := List.length_erase_of_mem hm
  have hp := List.length_pos_of_mem hm
  omega

theorem solveAux_spec [DecidableEq α] (rules : List (Rule α)) (known pending : List α)
    (ground : Grounded rules known)
    (covers : ∀ r ∈ rules, r.conclusion ∈ known ∨ r.conclusion ∈ pending) :
    Grounded rules (solveAux rules known pending) ∧
    Closed rules (solveAux rules known pending) ∧
    (∀ x ∈ known, x ∈ solveAux rules known pending) := by
  induction hn : pending.length using Nat.strongRecOn generalizing known pending with
  | ind n ih =>
    cases hf : pending.find? (enabled rules known) with
    | none =>
      have eq : solveAux rules known pending = known := by rw [solveAux, hf]
      rw [eq]
      refine ⟨ground, ?_, fun _ hx => hx⟩
      intro r hr hp
      rcases covers r hr with hk | ht
      · exact hk
      · have en : enabled rules known r.conclusion = true :=
          enabled_iff.mpr ⟨r, hr, rfl, hp⟩
        have no := List.find?_eq_none.mp hf r.conclusion ht
        simp [en] at no
    | some x =>
      have hx := List.mem_of_find?_eq_some hf
      have en := List.find?_some hf
      have gx : Derives rules x := by
        obtain ⟨r, hr, he, hp⟩ := enabled_iff.mp en
        rw [← he]
        exact .rule r hr (fun y hy => ground y (hp y hy))
      have shorter : (pending.erase x).length < n := by
        have he := List.length_erase_of_mem hx
        have hp := List.length_pos_of_mem hx
        omega
      have gnext : Grounded rules (x :: known) := by
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact gx
        · exact ground y hy
      have cnext : ∀ r ∈ rules,
          r.conclusion ∈ x :: known ∨ r.conclusion ∈ pending.erase x := by
        intro r hr
        rcases covers r hr with hk | ht
        · exact Or.inl (List.mem_cons_of_mem _ hk)
        · by_cases he : r.conclusion = x
          · exact Or.inl (by simp [he])
          · exact Or.inr (List.mem_erase_of_ne he |>.mpr ht)
      have result := ih _ shorter (x :: known) (pending.erase x) gnext cnext rfl
      have eq : solveAux rules known pending = solveAux rules (x :: known) (pending.erase x) := by
        rw [solveAux, hf]
      rw [eq]
      exact ⟨result.1, result.2.1, fun y hy => result.2.2 y (List.mem_cons_of_mem _ hy)⟩

def solve [DecidableEq α] (rules : List (Rule α)) : List α :=
  solveAux rules [] (rules.map Rule.conclusion).eraseDups

theorem deduplicated_domain_nodup [DecidableEq α] (values : List α) : values.eraseDups.Nodup := by
  induction hn : values.length using Nat.strongRecOn generalizing values with
  | ind n ih =>
    cases values with
    | nil => simp
    | cons first rest =>
      rw [List.eraseDups_cons]
      apply List.nodup_cons.mpr
      refine ⟨?_, ?_⟩
      · intro hm
        have hp := (List.mem_filter.mp (List.mem_eraseDups.mp hm)).2
        simp at hp
      · apply ih _ ?_ _ rfl
        have hf := List.length_filter_le (fun value => !(value == first)) rest
        simp only [List.length_cons] at hn
        omega

theorem solveAux_nodup [DecidableEq α] (rules : List (Rule α)) (known pending : List α)
    (hk : known.Nodup) (hp : pending.Nodup) (hd : ∀ x ∈ pending, x ∉ known) :
    (solveAux rules known pending).Nodup := by
  induction hn : pending.length using Nat.strongRecOn generalizing known pending with
  | ind n ih =>
    cases hf : pending.find? (enabled rules known) with
    | none => rw [solveAux, hf]; exact hk
    | some x =>
      have hx := List.mem_of_find?_eq_some hf
      have shorter : (pending.erase x).length < n := by
        have he := List.length_erase_of_mem hx
        have hpos := List.length_pos_of_mem hx
        omega
      have hknown : (x :: known).Nodup := List.nodup_cons.mpr ⟨hd x hx, hk⟩
      have hdisjoint : ∀ y ∈ pending.erase x, y ∉ x :: known := by
        intro y hy hm
        rcases List.mem_cons.mp hm with he | hknown
        · exact (hp.mem_erase_iff.mp hy).1 he
        · exact hd y (List.mem_of_mem_erase hy) hknown
      rw [solveAux, hf]
      exact ih _ shorter (x :: known) (pending.erase x) hknown (hp.erase x) hdisjoint rfl

theorem solve_nodup [DecidableEq α] : (solve rules).Nodup :=
  solveAux_nodup rules [] (rules.map Rule.conclusion).eraseDups (by simp)
    (deduplicated_domain_nodup _) (by simp)

theorem solve_grounded [DecidableEq α] : Grounded rules (solve rules) := by
  apply (solveAux_spec rules [] (rules.map Rule.conclusion).eraseDups ?_ ?_).1
  · simp [Grounded]
  · intro r hr
    exact Or.inr (List.mem_eraseDups.mpr (List.mem_map.mpr ⟨r, hr, rfl⟩))

theorem solve_closed [DecidableEq α] : Closed rules (solve rules) := by
  apply (solveAux_spec rules [] (rules.map Rule.conclusion).eraseDups ?_ ?_).2.1
  · simp [Grounded]
  · intro r hr
    exact Or.inr (List.mem_eraseDups.mpr (List.mem_map.mpr ⟨r, hr, rfl⟩))

theorem derivation_in_closed (hc : Closed rules facts) (hd : Derives rules x) :
    x ∈ facts := by
  induction hd with
  | rule r hr _ ih => exact hc r hr ih

theorem solve_exact [DecidableEq α] : x ∈ solve rules ↔ Derives rules x :=
  ⟨solve_grounded x, derivation_in_closed solve_closed⟩

theorem solve_least [DecidableEq α] (hc : Closed rules facts) :
    ∀ x ∈ solve rules, x ∈ facts :=
  fun x hx => derivation_in_closed hc (solve_grounded x hx)

end RilAccess
