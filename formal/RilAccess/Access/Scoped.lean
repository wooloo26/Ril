import RilAccess.Access.Handoff

/-! Scoped `use` resource bindings (`use` / `use mut`) and foreign
`.d.ril` `opaque type` affine handles:
- `.d.ril` `opaque type` handles forbid plain immutable snapshot freezing, `^mut`
  sharing, `var mut` overwrite, and `.retain`, while permitting `new` handoff and
  scoped `mut`/`ref` borrows without imposing mandatory `E0721` consumption.
- `use` bindings forbid slot replacement (`E0532`), local rebinding, `new`
  handoff (blocking early manual `close(new r)` double-close), and `.retain` escape
  (`E0604`), and are deterministically deactivated at lexical `.leaveScope`. -/
namespace RilAccess.Integrated

variable {world next : World} {source destination id : Nat} {resolved : Resolved}

theorem resource_rejects_plain_and_shared_receiving
    {mode : MemberMode} {scope : Nat}
    (hres : resolved.grant.resource = true)
    (hmode : mode.access = .immutable ∨ mode.access = .shared) :
    receiving world resolved mode scope = false := by
  rcases hmode with hm | hm <;> simp [receiving, hm, hres]

theorem resource_cannot_retain {evidence : Evidence}
    (h : authorized evidence = true) (hr : evidence.rule = .retain) :
    evidence.resolved.grant.resource = false := by
  have hloc := authorization_local h
  simp_all [authorizedLocal]

theorem resource_handoff_transfers_exclusively
    (h : checkAtom (.move source destination) world = .ok next)
    (hr : resolve world ⟨source, []⟩ = some resolved) :
    (∀ dep ∈ resolved.permission.dependencies, (lookupToken next dep).any Token.active = false) ∧
      ∃ fresh, lookupToken next world.nextToken = some fresh ∧
        fresh.qualified = true ∧ fresh.active = true ∧ fresh.region = resolved.pointer := by
  refine ⟨fun dep hdep => handoff_revokes_dependency h hr hdep, ?_⟩
  obtain ⟨actual, resolvedAt, _, table, _⟩ := move_facts h
  have eq : actual = resolved := Option.some.inj (resolvedAt.symm.trans hr)
  subst actual
  refine ⟨⟨world.nextToken, resolved.pointer, true, false, true, false, world.scope,
    resolved.permission.dependencies, []⟩, ?_, rfl, rfl, rfl⟩
  unfold lookupToken
  rw [table, List.find?_cons]
  simp

theorem scoped_rejects_escape {mode : MemberMode} {scope : Nat}
    (hsc : resolved.permission.isScoped = true) :
    eligibleMove world resolved = false ∧
      receiving world resolved mode scope = false := by
  exact ⟨by simp [eligibleMove, hsc], by simp [receiving, hsc]⟩

theorem scoped_cannot_retain {evidence : Evidence}
    (h : authorized evidence = true) (hr : evidence.rule = .retain) :
    evidence.resolved.permission.isScoped = false := by
  have hloc := authorization_local h
  simp_all [authorizedLocal]

theorem scoped_rejects_reassignment {target : Permission}
    (hlook : lookupPermission world destination = some target)
    (hsc : target.isScoped = true) :
    transfer world (.assign ⟨source, []⟩ destination) = none := by
  unfold transfer
  cases hraw : rawStep (eraseAtom (.assign ⟨source, []⟩ destination)) world.raw with
  | none => rfl
  | some raw =>
    simp only [hlook]
    cases htp : resolve world ⟨destination, []⟩ with
    | none => rfl
    | some tp =>
      cases hrs : resolve world ⟨source, []⟩ with
      | none => rfl
      | some rs => simp [hsc]

theorem leaveScope_deactivates_inner_permission
    (h : checkAtom .leaveScope world = .ok next)
    {frame : Frame} (hframe : world.frames.head? = some frame)
    {perm : Permission} (hp : perm ∈ next.permissions)
    (hinner : frame.parentScope < perm.scope) :
    perm.alive = false := by
  have executed := (checked_atom_facts h).executed
  simp only [transfer, eraseAtom, rawStep, hframe] at executed
  cases executed
  obtain ⟨before, _, hmap⟩ := List.mem_map.mp hp
  by_cases hgt : before.scope > frame.parentScope
  · rw [if_pos hgt] at hmap
    cases hmap
    rfl
  · rw [if_neg hgt] at hmap
    cases hmap
    omega

structure ScopedCleanupContract where
  mode : ParameterMode
  returnsUnit : Bool := true
  hasFiberEffect : Bool := false
  writes : Bool := false
  retains : Bool := false
  captures : Bool := false
  deriving Repr, DecidableEq

/-- Signature of the resolved, single-parameter cleanup function (`E0541`, `E0616`). -/
def validScopedCleanupContract (contract : ScopedCleanupContract) : Bool :=
  let mode := contract.mode
  (decide (mode = .observe) || decide (mode = .mutable) || decide (mode = .construction)) &&
    contract.returnsUnit && !contract.hasFiberEffect &&
    decide (contract.writes = decide (mode = .mutable)) && !contract.retains && !contract.captures

theorem scoped_cleanup_contract_iff (contract : ScopedCleanupContract) :
    validScopedCleanupContract contract = true ↔
      (contract.mode = .observe ∨ contract.mode = .mutable ∨ contract.mode = .construction) ∧
      contract.returnsUnit = true ∧ contract.hasFiberEffect = false ∧
      contract.writes = decide (contract.mode = .mutable) ∧
      contract.retains = false ∧ contract.captures = false := by
  simp [validScopedCleanupContract, Bool.and_eq_true, Bool.or_eq_true, and_assoc, or_assoc]

end RilAccess.Integrated
