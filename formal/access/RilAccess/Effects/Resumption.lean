import RilAccess.Access.Lifetime

/-! An affine operation record over the actual token/loan ledger. Context/scope
truthfulness is an explicit operation-call correspondence obligation. -/
namespace RilAccess.CoreResumption

open Integrated

structure Context where
  arm : Nat
  callable : Nat
  task : Nat
  deriving Repr, DecidableEq

structure Slot where
  id : Nat
  context : Context
  scope : Nat
  deriving Repr, DecidableEq

structure State where
  slots : List Slot
  current : Context
  authority : World
  committed : List Event
  consumed : List Nat := []

def State.activeAuthority (state : State) : List Nat :=
  (state.authority.tokens.filter Token.active).map Token.id

def resume (state : State) (ticket : Nat) : Option State := do
  let slot ← state.slots.find? (fun slot => decide (slot.id = ticket))
  let after := endBoundary state.authority (temporaryWrites state.authority slot.scope)
  if decide (slot.context = state.current ∧ slot.scope = state.authority.scope ∧ ticket ∉ state.consumed) &&
      (ledgerValid state.authority && ledgerValid after) then
    some { state with
      authority := endBoundary state.authority (temporaryWrites state.authority slot.scope),
      consumed := ticket :: state.consumed }
  else none

variable {state next finish : State} {slot : Slot} {ticket id : Nat} {dependencies : List Nat}

structure ResumeFacts (state : State) (ticket : Nat) (next : State) : Prop where
  slot : ∃ slot ∈ state.slots, slot.id = ticket ∧ slot.context = state.current ∧
    slot.scope = state.authority.scope ∧
    next.authority = endBoundary state.authority (temporaryWrites state.authority slot.scope)
  unused : ticket ∉ state.consumed
  consumed : next.consumed = ticket :: state.consumed
  committed : next.committed = state.committed
  ledger : WorldInvariant state.authority
  afterLedger : WorldInvariant next.authority

theorem successful_resume (h : resume state ticket = some next) : ResumeFacts state ticket next := by
  cases hf : state.slots.find? (fun slot => decide (slot.id = ticket)) with
  | none => simp [resume, hf] at h
  | some slot =>
    have hm := List.mem_of_find?_eq_some hf
    have hi : slot.id = ticket := of_decide_eq_true
      (List.find?_some (p := fun candidate : Slot => decide (candidate.id = ticket)) hf)
    simp only [resume, hf] at h
    change (if _ then _ else _) = some next at h
    split at h
    · rename_i hc
      have checks : (slot.context = state.current ∧ slot.scope = state.authority.scope ∧ ticket ∉ state.consumed) ∧
          (ledgerValid state.authority = true ∧
            ledgerValid (endBoundary state.authority (temporaryWrites state.authority slot.scope)) = true) := by
        simpa only [Bool.and_eq_true, decide_eq_true_eq] using hc
      cases h
      exact ⟨⟨slot, hm, hi, checks.1.1, checks.1.2.1, rfl⟩,
        checks.1.2.2, rfl, rfl, ledger_facts checks.2.1, ledger_facts checks.2.2⟩
    · contradiction

theorem consumed_cannot_resume (hc : ticket ∈ state.consumed) : resume state ticket = none := by
  cases hr : resume state ticket with
  | none => rfl
  | some next => exact False.elim ((successful_resume hr).unused hc)

inductive Step : State → State → Prop where
  | invoke {state next : State} {ticket : Nat} : resume state ticket = some next → Step state next
  | context {state : State} {current : Context} : Step state { state with current := current }

inductive Trace : State → State → Prop where
  | refl {state : State} : Trace state state
  | tail {start middle next : State} : Trace start middle → Step middle next → Trace start next

theorem consumed_persists (ht : Trace start finish) (hc : ticket ∈ start.consumed) :
    ticket ∈ finish.consumed := by
  induction ht with
  | refl => exact hc
  | tail _ hs ih =>
    cases hs with
    | context => exact ih
    | invoke h => rw [(successful_resume h).consumed]; exact List.mem_cons_of_mem _ ih

theorem aliases_cannot_resume_twice (h : resume state ticket = some next)
    (ht : Trace next finish) : resume finish ticket = none :=
  consumed_cannot_resume (consumed_persists ht (by simp [(successful_resume h).consumed]))

theorem operation_dependency_ends (h : resume state ticket = some next)
    (hi : id ∈ temporaryWrites state.authority state.authority.scope) (hd : id ∈ dependencies) :
    lifetimeEnabled next.authority dependencies = false := by
  obtain ⟨slot, _, _, _, scope, he⟩ := (successful_resume h).slot
  rw [he, scope]
  exact dependency_ends_access hi hd

theorem independent_view_survives (h : resume state ticket = some next)
    (hl : lifetimeEnabled state.authority dependencies = true)
    (hd : ∀ id ∈ dependencies, id ∉ temporaryWrites state.authority state.authority.scope) :
    lifetimeEnabled next.authority dependencies = true := by
  obtain ⟨slot, _, _, _, scope, he⟩ := (successful_resume h).slot
  rw [he, scope]
  exact independent_access_survives hl hd

theorem derived_access_ends (h : resume state ticket = some next)
    (hr : resolve next.authority path = some resolved)
    (hi : id ∈ temporaryWrites state.authority state.authority.scope)
    (hd : id ∈ resolved.permission.dependencies) : live resolved = false := by
  cases hl : live resolved with
  | false => rfl
  | true =>
    have enabled := resolved_live_dependencies (successful_resume h).afterLedger hr hl
    have ended := operation_dependency_ends h hi hd
    simp [ended] at enabled

theorem retained_authority_survives (h : resume state ticket = some next)
    (hr : lookupToken state.authority id = some token) (ht : token.retained = true) :
    lookupToken next.authority id = some token := by
  obtain ⟨slot, _, _, _, scope, he⟩ := (successful_resume h).slot
  rw [he, scope, unrelated_lookup (retained_not_temporary hr ht)]
  exact hr

theorem outer_authority_survives (h : resume state ticket = some next)
    (hr : lookupToken state.authority id = some token) (hs : token.scope ≠ state.authority.scope) :
    lookupToken next.authority id = some token := by
  obtain ⟨slot, _, _, _, scope, he⟩ := (successful_resume h).slot
  rw [he, scope, unrelated_lookup (other_scope_not_temporary hr hs)]
  exact hr

theorem ended_operation_loan (h : resume state ticket = some next)
    (hl : loan ∈ next.authority.loans)
    (hi : loan.token ∈ temporaryWrites state.authority state.authority.scope) : loan.active = false := by
  obtain ⟨slot, _, _, _, scope, he⟩ := (successful_resume h).slot
  rw [he, scope] at hl
  exact ended_loan_inactive hl hi

theorem dependent_operation_loan (h : resume state ticket = some next)
    (hl : loan ∈ next.authority.loans)
    (hi : loan.token ∈ lifetimeClosure state.authority
      (temporaryWrites state.authority state.authority.scope)) : loan.active = false := by
  obtain ⟨slot, _, _, _, scope, he⟩ := (successful_resume h).slot
  rw [he, scope] at hl
  exact dependent_loan_inactive hl hi

theorem resume_keeps_committed_state (ht : Trace start finish) : finish.committed = start.committed := by
  induction ht with
  | refl => rfl
  | tail _ hs ih =>
    cases hs with
    | context => exact ih
    | invoke h => exact (successful_resume h).committed.trans ih

/-- A source operation must account for its actual mutable temporary roots. The
kernel computes its snapshot; this named premise relates it to source execution. -/
def OperationConforms (state : State) (actualTemporary : Nat → Prop) : Prop :=
  ∀ id, actualTemporary id ↔ id ∈ temporaryWrites state.authority state.authority.scope

theorem conforming_operation_revokes (h : resume state ticket = some next)
    (conforms : OperationConforms state actualTemporary) (hi : actualTemporary id) (hd : id ∈ dependencies) :
    lifetimeEnabled next.authority dependencies = false :=
  operation_dependency_ends h ((conforms id).mp hi) hd

end RilAccess.CoreResumption
