import RilAccess.Contracts

/-! A resumption handle carries an identity, never a copyable unused flag.
The central record consumes that identity before continuation execution. This
models the access boundary, not handler dispatch or continuation evaluation. -/
namespace RilAccess.CoreResumption

structure Context where
  arm : Nat
  callable : Nat
  task : Nat
  deriving Repr, DecidableEq

structure Slot where
  id : Nat
  context : Context
  temporary : List Nat
  deriving Repr, DecidableEq

structure State where
  slots : List Slot
  current : Context
  activeAuthority : List Nat
  committed : List Event
  consumed : List Nat := []
  deriving Repr, DecidableEq

def resume (state : State) (ticket : Nat) : Option State := do
  let slot ← state.slots.find? (fun slot => decide (slot.id = ticket))
  if decide (slot.context = state.current ∧ ticket ∉ state.consumed) then
    some { state with
      activeAuthority := state.activeAuthority.filter (fun id => decide (id ∉ slot.temporary)),
      consumed := ticket :: state.consumed }
  else none

theorem successful_resume (h : resume state ticket = some next) :
    ∃ slot ∈ state.slots, slot.id = ticket ∧ slot.context = state.current ∧
      ticket ∉ state.consumed ∧ next.consumed = ticket :: state.consumed ∧
      next.activeAuthority = state.activeAuthority.filter (fun id => decide (id ∉ slot.temporary)) ∧
      next.committed = state.committed := by
  cases hf : state.slots.find? (fun slot => decide (slot.id = ticket)) with
  | none => simp [resume, hf] at h
  | some slot =>
    have hm := List.mem_of_find?_eq_some hf
    have hi : slot.id = ticket := of_decide_eq_true
      (List.find?_some (p := fun candidate : Slot => decide (candidate.id = ticket)) hf)
    simp only [resume, hf] at h
    change (if decide (slot.context = state.current ∧ ticket ∉ state.consumed) then _ else _) = some next at h
    split at h
    · rename_i hc
      have hc := of_decide_eq_true hc
      cases h
      exact ⟨slot, hm, hi, hc.1, hc.2, rfl, rfl, rfl⟩
    · contradiction

theorem consumed_cannot_resume (hc : ticket ∈ state.consumed) : resume state ticket = none := by
  unfold resume
  cases hf : state.slots.find? (fun slot => decide (slot.id = ticket)) <;> simp [hc]

inductive Step : State → State → Prop where
  | invoke : resume state ticket = some next → Step state next
  | context : Step state { state with current := current }

inductive Trace : State → State → Prop where
  | refl : Trace state state
  | tail : Trace start middle → Step middle next → Trace start next

theorem consumed_persists (ht : Trace start finish) (hc : ticket ∈ start.consumed) :
    ticket ∈ finish.consumed := by
  induction ht with
  | refl => exact hc
  | tail _ hs ih =>
    cases hs with
    | context => exact ih
    | invoke h =>
      obtain ⟨_, _, _, _, _, consumed, _, _⟩ := successful_resume h
      rw [consumed]
      exact List.mem_cons_of_mem _ ih

theorem aliases_cannot_resume_twice (h : resume state ticket = some next)
    (ht : Trace next finish) : resume finish ticket = none := by
  obtain ⟨_, _, _, _, _, consumed, _, _⟩ := successful_resume h
  exact consumed_cannot_resume (consumed_persists ht (by simp [consumed]))

theorem operation_authority_ends (h : resume state ticket = some next) :
    ∃ slot ∈ state.slots, slot.id = ticket ∧
      (∀ authority ∈ slot.temporary, authority ∉ next.activeAuthority) ∧
      (∀ authority ∈ state.activeAuthority, authority ∉ slot.temporary → authority ∈ next.activeAuthority) := by
  obtain ⟨slot, hm, hi, _, _, _, ha, _⟩ := successful_resume h
  refine ⟨slot, hm, hi, ?_, ?_⟩
  · intro authority ht hn
    rw [ha] at hn
    have noTemporary := of_decide_eq_true (List.mem_filter.mp hn).2
    exact noTemporary ht
  · intro authority hin hout
    rw [ha]
    exact List.mem_filter.mpr ⟨hin, decide_eq_true hout⟩

theorem resume_keeps_committed_state (ht : Trace start finish) : finish.committed = start.committed := by
  induction ht with
  | refl => rfl
  | tail _ hs ih =>
    cases hs with
    | context => exact ih
    | invoke h =>
      obtain ⟨_, _, _, _, _, _, _, kept⟩ := successful_resume h
      exact kept.trans ih

theorem escaped_context_cannot_resume
    (hc : ∀ slot ∈ state.slots, slot.id = ticket → slot.context ≠ state.current) :
    resume state ticket = none := by
  cases hr : resume state ticket with
  | none => rfl
  | some next =>
    obtain ⟨slot, hm, hi, context, _⟩ := successful_resume hr
    exact False.elim (hc slot hm hi context)

end RilAccess.CoreResumption
