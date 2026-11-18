import RilAccess.Solver

namespace RilAccess.Provenance

/-- A demand-driven rule engine. A rule can depend on facts already discovered
    (for example, a return from a particular abstract call entry). -/
def saturate [DecidableEq α] (expand : List α → α → List α) : Nat → List α → Option (List α)
  | 0, _ => none
  | fuel + 1, facts =>
      let added := (facts.flatMap (expand facts)).filter fun x => decide (x ∉ facts)
      if added.isEmpty then some facts
      else saturate expand fuel (facts ++ added.eraseDups)

def Stable (expand : List α → α → List α) (facts : List α) : Prop :=
  ∀ x ∈ facts, ∀ y ∈ expand facts x, y ∈ facts

def Includes (left right : List α) : Prop := ∀ x ∈ left, x ∈ right

def MonotoneExpansion (expand : List α → α → List α) : Prop :=
  ∀ {left right}, Includes left right → ∀ x, Includes (expand left x) (expand right x)

theorem saturate_stable [DecidableEq α] {expand : List α → α → List α}
    (h : saturate expand fuel seed = some facts) : Includes seed facts ∧ Stable expand facts := by
  induction fuel generalizing seed with
  | zero => simp [saturate] at h
  | succ fuel ih =>
    rw [saturate] at h
    split at h
    · rename_i empty
      cases h
      refine ⟨fun _ hx => hx, ?_⟩
      intro x hx y hy
      by_cases hn : y ∈ facts
      · exact hn
      have hm : y ∈ (facts.flatMap (expand facts)).filter (fun x => decide (x ∉ facts)) :=
        List.mem_filter.mpr ⟨List.mem_flatMap.mpr ⟨x, hx, hy⟩, by simp [hn]⟩
      rw [List.isEmpty_iff.mp empty] at hm
      exact False.elim (List.not_mem_nil hm)
    · have hnext := ih h
      exact ⟨fun x hx => hnext.1 x (List.mem_append_left _ hx), hnext.2⟩

theorem saturate_least [DecidableEq α] {expand : List α → α → List α}
    (mono : MonotoneExpansion expand) (stable : Stable expand upper)
    (base : Includes seed upper) (h : saturate expand fuel seed = some facts) : Includes facts upper := by
  induction fuel generalizing seed with
  | zero => simp [saturate] at h
  | succ fuel ih =>
    rw [saturate] at h
    split at h
    · cases h
      exact base
    · apply ih ?_ h
      intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · exact base y hy
      · obtain ⟨x, hx, hy⟩ := List.mem_flatMap.mp (List.mem_filter.mp (List.mem_eraseDups.mp hy)).1
        exact stable x (base x hx) y (mono base x y hy)

end RilAccess.Provenance
