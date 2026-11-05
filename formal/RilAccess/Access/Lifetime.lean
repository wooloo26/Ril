import RilAccess.Access.Progress
import RilAccess.Graph.Identity

/-! Lifetimes are checked against the current ledger. Token.parents records
origin ancestry and is deliberately not used as a lifetime dependency. -/
namespace RilAccess.Integrated

variable {world : World} {id scope : Nat} {ids dependencies : List Nat} {token : Token}
  {loan : Loan} {path : Path} {resolved : Resolved}

def Pointer.regionKey (pointer : Pointer) : Identity.RegionKey := (pointer.object, pointer.fields)

theorem region_ignores_source_labels (left right : Pointer) (a b : Source) :
    overlaps { left with source := a } { right with source := b } = overlaps left right := rfl

def lifetimeClosure (world : World) (ids : List Nat) : List Nat :=
  solve (ids.map (fun id => Rule.mk [] id) ++ world.tokens.flatMap (fun token =>
    token.dependencies.map (fun dependency => Rule.mk [dependency] token.id)))

theorem lifetimeClosure_root (hi : id ∈ ids) : id ∈ lifetimeClosure world ids := by
  apply solve_closed ⟨[], id⟩ (List.mem_append_left _ (List.mem_map.mpr ⟨id, hi, rfl⟩))
  simp

def endBoundary (world : World) (ids : List Nat) : World :=
  { endTokens world ids with
    loans := world.loans.map (fun loan =>
      if loan.token ∈ lifetimeClosure world ids then { loan with active := false } else loan) }

def lifetimeEnabled (world : World) (dependencies : List Nat) : Bool :=
  !dependencies.isEmpty && dependencies.all (fun id => (lookupToken world id).any Token.active)

/-- A scope snapshot is supplied by the operation-call correspondence. Ordinary
readonly observations and retained parameters are not mutable temporary roots. -/
def temporaryWrites (world : World) (scope : Nat) : List Nat :=
  world.loans.filterMap fun loan =>
    match lookupToken world loan.token with
    | none => none
    | some token =>
      if loan.writes && token.temporary && !token.retained && decide (token.scope = scope)
      then some loan.token else none

theorem lookup_token (h : lookupToken world id = some token) :
    token ∈ world.tokens ∧ token.id = id :=
  ⟨List.mem_of_find?_eq_some h,
    of_decide_eq_true (List.find?_some (p := fun token : Token => decide (token.id = id)) h)⟩

theorem lookup_ended :
    lookupToken (endBoundary world ids) id =
      (lookupToken world id).map (fun token =>
        if token.id ∈ ids then { token with active := false, qualified := false } else token) := by
  unfold lookupToken endBoundary endTokens
  change (world.tokens.map _).find? _ = (world.tokens.find? _).map _
  rw [List.find?_map]
  have keepId : ∀ token : Token,
      (if token.id ∈ ids then { token with active := false, qualified := false } else token).id = token.id := by
    intro token; split <;> rfl
  simp only [Function.comp_def, keepId]

theorem ended_not_active (hi : id ∈ ids) :
    (lookupToken (endBoundary world ids) id).any Token.active = false := by
  rw [lookup_ended]
  cases hm : lookupToken world id with
  | none => rfl
  | some token =>
    have he := (lookup_token hm).2
    simp [he, hi]

theorem unrelated_lookup (hi : id ∉ ids) :
    lookupToken (endBoundary world ids) id = lookupToken world id := by
  rw [lookup_ended]
  cases hm : lookupToken world id with
  | none => rfl
  | some token => simp [(lookup_token hm).2, hi]

theorem dependency_ends_access (hi : id ∈ ids) (hd : id ∈ dependencies) :
    lifetimeEnabled (endBoundary world ids) dependencies = false := by
  cases he : lifetimeEnabled (endBoundary world ids) dependencies with
  | false => rfl
  | true =>
    have hall := he
    simp only [lifetimeEnabled, Bool.and_eq_true] at hall
    have active := List.all_eq_true.mp hall.2 id hd
    simp [ended_not_active hi] at active

theorem independent_access_survives (hl : lifetimeEnabled world dependencies = true)
    (hd : ∀ id ∈ dependencies, id ∉ ids) :
    lifetimeEnabled (endBoundary world ids) dependencies = true := by
  simp only [lifetimeEnabled, Bool.and_eq_true] at hl ⊢
  refine ⟨hl.1, List.all_eq_true.mpr ?_⟩
  intro id hi
  rw [unrelated_lookup (hd id hi)]
  exact List.all_eq_true.mp hl.2 id hi

theorem dependent_loan_inactive (hl : loan ∈ (endBoundary world ids).loans) (hi : loan.token ∈ lifetimeClosure world ids) :
    loan.active = false := by
  obtain ⟨before, _, he⟩ := List.mem_map.mp hl
  by_cases ended : before.token ∈ lifetimeClosure world ids
  · rw [if_pos ended] at he
    cases he; rfl
  · rw [if_neg ended] at he
    cases he; contradiction

theorem ended_loan_inactive (hl : loan ∈ (endBoundary world ids).loans) (hi : loan.token ∈ ids) :
    loan.active = false := dependent_loan_inactive hl (lifetimeClosure_root hi)

theorem selected_temporary (hi : id ∈ temporaryWrites world scope) :
    ∃ token, lookupToken world id = some token ∧ token.temporary = true ∧ token.retained = false ∧ token.scope = scope := by
  obtain ⟨loan, _, he⟩ := List.mem_filterMap.mp hi
  cases hm : lookupToken world loan.token with
  | none => simp [hm] at he
  | some token =>
    simp only [hm] at he
    split at he
    · rename_i flags
      cases he
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at flags
      exact ⟨token, hm, flags.1.1.2, flags.1.2, flags.2⟩
    · contradiction

theorem retained_not_temporary (hr : lookupToken world id = some token) (ht : token.retained = true) :
    id ∉ temporaryWrites world scope := by
  intro hi
  obtain ⟨selected, hs, _, hn, _⟩ := selected_temporary hi
  have eq : token = selected := Option.some.inj (hr.symm.trans hs)
  cases eq
  simp [ht] at hn

theorem other_scope_not_temporary (hr : lookupToken world id = some token) (hs : token.scope ≠ scope) :
    id ∉ temporaryWrites world scope := by
  intro hi
  obtain ⟨selected, ht, _, _, hc⟩ := selected_temporary hi
  have eq : token = selected := Option.some.inj (hr.symm.trans ht)
  cases eq
  exact hs hc

/-- Resolve creates a fresh snapshot of the current ledger, not an authority
grant obtained by reusing an earlier successful observation. -/
structure ResolutionFacts (world : World) (path : Path) (resolved : Resolved) : Prop where
  permission : lookupPermission world path.register = some resolved.permission
  root : ∃ root, rawLookup world.raw path.register = some root ∧
    resolved.pointer = { root with fields := root.fields ++ path.fields }
  tokens : resolved.tokens = resolved.permission.dependencies.filterMap (lookupToken world)

theorem resolution_facts (h : resolve world path = some resolved) : ResolutionFacts world path resolved := by
  unfold resolve at h
  cases hp : lookupPermission world path.register with
  | none => simp [hp] at h
  | some permission =>
    cases hr : rawLookup world.raw path.register with
    | none => simp [hp, hr] at h
    | some root =>
      cases hg : world.grants.find? (fun grant => decide (grant.object = root.object)) with
      | none => simp [hp, hr, hg] at h
      | some grant =>
        cases ht : traverse grant.schema root.fields permission.mode.access path.fields with
        | none => simp [hp, hr, hg, ht] at h
        | some result =>
          obtain ⟨members, effective, parent, replaceable, object⟩ := result
          simp [hp, hr, hg, ht] at h
          cases h
          exact ⟨hp, ⟨root, hr, rfl⟩, rfl⟩

theorem resolved_tokens (h : resolve world path = some resolved) :
    lookupPermission world path.register = some resolved.permission ∧
      resolved.tokens = resolved.permission.dependencies.filterMap (lookupToken world) :=
  ⟨(resolution_facts h).permission, (resolution_facts h).tokens⟩

theorem resolved_live_dependencies (hw : WorldInvariant world) (hr : resolve world path = some resolved)
    (hl : live resolved = true) : lifetimeEnabled world resolved.permission.dependencies = true := by
  obtain ⟨permission, tokens⟩ := resolved_tokens hr
  simp only [live, Bool.and_eq_true] at hl
  unfold lifetimeEnabled
  simp only [Bool.and_eq_true]
  refine ⟨hl.1.1.1.2, ?_⟩
  apply List.all_eq_true.mpr
  intro id hi
  have known := hw.dependenciesKnown _ (List.mem_of_find?_eq_some permission) id hi
  cases ht : lookupToken world id with
  | none => simp [ht] at known
  | some token =>
    have member : token ∈ resolved.tokens := by
      rw [tokens]
      exact List.mem_filterMap.mpr ⟨id, hi, ht⟩
    have active := List.all_eq_true.mp hl.1.2 token member
    have pair : token.active = true ∧ contains token.region resolved.pointer = true := by
      simpa only [Bool.and_eq_true] using active
    exact pair.1

end RilAccess.Integrated
