import RilAccess.Access.Handoff

/-! Lexical `defer` cleanup statements and foreign `.d.ril` `opaque type`
exclusive, must-consume host handles:
- `.d.ril` `opaque type` handles forbid plain immutable snapshot freezing, `^mut`
  sharing, `var mut` overwrite, and `.retain`, while permitting `new` handoff,
  scoped `mut`/`ref` access, and `defer` cleanup.
- Block-scoped reservations forbid slot replacement, aliasing/escape, and early
  conflicting handoff, and are deterministically deactivated at lexical `.leaveScope`.
- `defer` bodies must evaluate to `()` (`E0301`), forbid unhandled `ctl` (`E0616`),
  forbid escaping `return`/`break`/`continue`/`?` (`E0707`), and require covering
  handlers to precede the `defer` (`E0612`). -/
namespace RilAccess.Integrated

/-- A `var ref` may keep only sources whose lexical scopes enclose the slot.
Scope paths list enclosing declarations and blocks from outermost to innermost. -/
def refSourcesEnclose (anchors : List (List Nat)) (slot : List Nat) : Bool :=
  anchors.all fun anchor => anchor.isPrefixOf slot

variable {world next : World} {source destination id : Nat} {resolved : Resolved}

theorem resource_rejects_plain_and_shared_receiving
    {mode : MemberMode} {scope : Nat}
    (hres : resolved.grant.resource = true)
    (hmode : mode.access = .immutable ∨ mode.access = .shared) :
    receiving world resolved mode scope = false := by
  rcases hmode with hm | hm <;> simp [receiving, hm, hres]

theorem resource_cannot_retain {accessCheck : AccessCheck}
    (h : authorized accessCheck = true) (hr : accessCheck.rule = .retain) :
    accessCheck.resolved.grant.resource = false := by
  have hloc := authorization_local h
  simp_all [authorizedLocal]

theorem resource_handoff_transfers_exclusively
    (h : checkAtom (.handoff source destination) world = .ok next)
    (hr : resolve world ⟨source, []⟩ = some resolved) :
    (∀ dep ∈ resolved.binding.dependencies, (lookupToken next dep).any Token.active = false) ∧
      ∃ fresh, lookupToken next world.nextToken = some fresh ∧
        fresh.qualified = true ∧ fresh.active = true ∧ fresh.region = resolved.pointer := by
  refine ⟨fun dep hdep => handoff_revokes_dependency h hr hdep, ?_⟩
  obtain ⟨actual, resolvedAt, _, table, _⟩ := handoff_facts h
  have eq : actual = resolved := Option.some.inj (resolvedAt.symm.trans hr)
  subst actual
  refine ⟨⟨world.nextToken, resolved.pointer, true, false, true, false, world.scope,
    resolved.binding.dependencies, []⟩, ?_, rfl, rfl, rfl⟩
  unfold lookupToken
  rw [table, List.find?_cons]
  simp

theorem scoped_rejects_escape {mode : MemberMode} {scope : Nat}
    (hsc : resolved.binding.isScoped = true) :
    eligibleHandoff world resolved = false ∧
      receiving world resolved mode scope = false := by
  exact ⟨by simp [eligibleHandoff, hsc], by simp [receiving, hsc]⟩

theorem scoped_cannot_retain {accessCheck : AccessCheck}
    (h : authorized accessCheck = true) (hr : accessCheck.rule = .retain) :
    accessCheck.resolved.binding.isScoped = false := by
  have hloc := authorization_local h
  simp_all [authorizedLocal]

theorem scoped_rejects_reassignment {target : BindingAccess}
    (hlook : lookupBinding world destination = some target)
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

theorem leaveScope_deactivates_inner_binding
    (h : checkAtom .leaveScope world = .ok next)
    {frame : Frame} (hframe : world.frames.head? = some frame)
    {perm : BindingAccess} (hp : perm ∈ next.bindings)
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

structure DeferBodyContract where
  returnsUnit : Bool := true
  hasUnhandledCtl : Bool := false
  escapesControlFlow : Bool := false
  handlersPrecededDefer : Bool := true
  deriving Repr, DecidableEq

/-- Well-formedness of a lexical `defer` cleanup body (`E0301`, `E0616`, `E0707`, `E0612`). -/
def validDeferBody (body : DeferBodyContract) : Bool :=
  body.returnsUnit && !body.hasUnhandledCtl && !body.escapesControlFlow && body.handlersPrecededDefer

theorem defer_body_contract_iff (body : DeferBodyContract) :
    validDeferBody body = true ↔
      body.returnsUnit = true ∧ body.hasUnhandledCtl = false ∧
      body.escapesControlFlow = false ∧ body.handlersPrecededDefer = true := by
  simp [validDeferBody, Bool.and_eq_true, and_assoc]

end RilAccess.Integrated
