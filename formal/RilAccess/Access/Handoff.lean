import RilAccess.Access.Scope

namespace RilAccess.Integrated

variable {world next : World} {source destination id : Nat} {resolved derived : Resolved}
  {path : Path} {token : Token}

theorem handoff_facts (h : checkAtom (.handoff source destination) world = .ok next) :
    ∃ resolved, resolve world ⟨source, []⟩ = some resolved ∧ eligibleHandoff world resolved = true ∧
      next.tokens =
        ⟨world.nextToken, resolved.pointer, true, false, true, false, world.scope, resolved.binding.dependencies, []⟩ ::
          (endTokens world resolved.binding.dependencies).tokens ∧
      rawLookup next.raw destination = some resolved.pointer := by
  have executed := (checked_atom_facts h).executed
  cases hr : resolve world ⟨source, []⟩ with
  | none => simp [transfer, hr] at executed
  | some resolved =>
    obtain ⟨root, lookup, pointer⟩ := (resolution_facts hr).root
    simp only [List.append_nil] at pointer
    have raw : rawStep (eraseAtom (.handoff source destination)) world.raw =
        some (putRaw world.raw destination resolved.pointer) := by
      simp [eraseAtom, rawStep, rawPath, lookup, pointer]
    simp only [transfer, raw, hr] at executed
    change (if unused world destination && eligibleHandoff world resolved then _ else _) = some next at executed
    split at executed
    · rename_i permitted
      have flags : unused world destination = true ∧ eligibleHandoff world resolved = true := by
        simpa only [Bool.and_eq_true] using permitted
      cases executed
      refine ⟨resolved, rfl, flags.2, rfl, ?_⟩
      simp [install, addRequirement, markUse, putBinding, rawLookup, putRaw]
    · contradiction

theorem moved_lookup (h : checkAtom (.handoff source destination) world = .ok next)
    (hr : resolve world ⟨source, []⟩ = some resolved) (old : id < world.nextToken) :
    lookupToken next id =
      (lookupToken world id).map (fun token =>
        if token.id ∈ resolved.binding.dependencies then { token with active := false, qualified := false } else token) := by
  obtain ⟨actual, resolvedAt, _, table, _⟩ := handoff_facts h
  have eq : actual = resolved := Option.some.inj (resolvedAt.symm.trans hr)
  subst actual
  unfold lookupToken
  rw [table]
  have different : world.nextToken ≠ id := by omega
  rw [List.find?_cons]
  simp only [show decide (world.nextToken = id) = false by simp [different]]
  exact lookup_ended (world := world) (ids := resolved.binding.dependencies) (id := id)

theorem handoff_preserves_identity (h : checkAtom (.handoff source destination) world = .ok next) :
    ∃ resolved, resolve world ⟨source, []⟩ = some resolved ∧
      rawLookup next.raw destination = some resolved.pointer := by
  obtain ⟨resolved, hr, _, _, target⟩ := handoff_facts h
  exact ⟨resolved, hr, target⟩

theorem handoff_revokes_dependency (h : checkAtom (.handoff source destination) world = .ok next)
    (hr : resolve world ⟨source, []⟩ = some resolved) (hd : id ∈ resolved.binding.dependencies) :
    (lookupToken next id).any Token.active = false := by
  have known := (checked_atom_facts h).beforeLedger.dependenciesKnown _
    (List.mem_of_find?_eq_some (resolution_facts hr).binding) id hd
  cases ht : lookupToken world id with
  | none => simp [ht] at known
  | some token =>
    have htId := (lookup_token ht).2
    have bound := (checked_atom_facts h).beforeLedger.tokenBound token (lookup_token ht).1
    rw [htId] at bound
    rw [moved_lookup h hr bound, ht]
    simp [htId, hd]

theorem handoff_ends_derived_access (h : checkAtom (.handoff source destination) world = .ok next)
    (hr : resolve world ⟨source, []⟩ = some resolved)
    (current : resolve next path = some derived)
    (dependency : id ∈ derived.binding.dependencies) (old : id ∈ resolved.binding.dependencies) :
    live derived = false := by
  cases hl : live derived with
  | false => rfl
  | true =>
    have enabled := resolved_live_dependencies (checked_atom_facts h).afterLedger current hl
    simp only [scopeEnabled, Bool.and_eq_true] at enabled
    have active := List.all_eq_true.mp enabled.2 id dependency
    simp [handoff_revokes_dependency h hr old] at active

theorem handoff_preserves_unrelated_token (h : checkAtom (.handoff source destination) world = .ok next)
    (hr : resolve world ⟨source, []⟩ = some resolved) (ht : lookupToken world id = some token)
    (independent : id ∉ resolved.binding.dependencies) : lookupToken next id = some token := by
  have htId := (lookup_token ht).2
  have bound := (checked_atom_facts h).beforeLedger.tokenBound token (lookup_token ht).1
  rw [htId] at bound
  rw [moved_lookup h hr bound, ht]
  simp [htId, independent]

end RilAccess.Integrated
