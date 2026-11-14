import RilAccess.Call.Proofs
import RilAccess.Access.Handoff

/-! Mandatory-consumption linear obligations over the integrated token ledger.
Linear allocations carry `linear = true` on their grant and single active owner
token; plain/shared/var-overwrite/retain reception is rejected, `move` transfers
the active obligation to a single fresh token, `destructure` discharges it while
recording reachable writable authority use, and scope/program completion rejects
any surviving active linear token across all control-flow branches. -/
namespace RilAccess.Integrated

variable {world next : World} {source destination id : Nat} {resolved derived : Resolved}
  {path : Path} {program : Syntax} {analysis : Analysis}

theorem no_active_linear_of_check_false {w : World} (h : hasUnconsumedLinear w = false)
    {token : Token} (ht : token ∈ w.tokens) (hlin : token.linear = true) :
    token.active = false := by
  cases hact : token.active with
  | false => rfl
  | true =>
    have hany : hasUnconsumedLinear w = true :=
      List.any_eq_true.mpr ⟨token, ht, by simp [hlin, hact]⟩
    simp [hany] at h

theorem checked_integrated_no_unconsumed_linear (h : check program = .ok analysis)
    {w : World} (hw : w ∈ analysis.worlds) {token : Token} (ht : token ∈ w.tokens)
    (hlin : token.linear = true) : token.active = false := by
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
      · rename_i hnoneLin
        split at h
        · contradiction
        · cases h
          have hwFalse : hasUnconsumedLinear w = false := by
            cases hc : hasUnconsumedLinear w with
            | false => rfl
            | true =>
              have hany : worlds.any hasUnconsumedLinear = true :=
                List.any_eq_true.mpr ⟨w, hw, hc⟩
              exact False.elim (hnoneLin hany)
          exact no_active_linear_of_check_false hwFalse ht hlin

theorem checked_calls_no_unconsumed_linear {callProgram : Calls.Syntax}
    (h : Calls.check callProgram = .ok analysis)
    {w : World} (hw : w ∈ analysis.worlds) {token : Token} (ht : token ∈ w.tokens)
    (hlin : token.linear = true) : token.active = false := by
  unfold Calls.check at h
  split at h <;> try contradiction
  cases hi : Calls.infer callProgram initialWorld with
  | error error => simp [hi] at h
  | ok worlds =>
    simp only [hi, except_bind_ok] at h
    split at h
    · contradiction
    · split at h
      · contradiction
      · rename_i hnoneLin
        split at h
        · contradiction
        · cases h
          have hwFalse : hasUnconsumedLinear w = false := by
            cases hc : hasUnconsumedLinear w with
            | false => rfl
            | true =>
              have hany : worlds.any hasUnconsumedLinear = true :=
                List.any_eq_true.mpr ⟨w, hw, hc⟩
              exact False.elim (hnoneLin hany)
          exact no_active_linear_of_check_false hwFalse ht hlin

theorem leaveScope_no_active_inner_linear (h : checkAtom .leaveScope world = .ok next)
    {frame : Frame} (hframe : world.frames.head? = some frame)
    {token : Token} (ht : token ∈ world.tokens) (hlin : token.linear = true)
    (hinner : frame.parentScope < token.scope) : token.active = false := by
  have executed := (checked_atom_facts h).executed
  simp only [transfer, eraseAtom, rawStep, hframe] at executed
  change (if hasUnconsumedLinearInScope world frame.parentScope then none else _) = some next at executed
  split at executed
  · contradiction
  · rename_i hnoInner
    cases hact : token.active with
    | false => rfl
    | true =>
      have hany : hasUnconsumedLinearInScope world frame.parentScope = true :=
        List.any_eq_true.mpr ⟨token, ht, by simp [hlin, hact, hinner]⟩
      exact False.elim (hnoInner hany)

theorem linear_rejects_plain_and_shared_receiving
    {mode : MemberMode} {scope : Nat}
    (hlin : resolved.grant.linear = true)
    (hmode : mode.access = .immutable ∨ mode.access = .shared) :
    receiving world resolved mode scope = false := by
  rcases hmode with hm | hm <;> simp [receiving, hm, hlin]

theorem linear_cannot_retain {evidence : Evidence}
    (h : authorized evidence = true) (hr : evidence.rule = .retain) :
    evidence.resolved.grant.linear = false := by
  have hloc := authorization_local h
  simp_all [authorizedLocal]

theorem linear_handoff_transfers_obligation
    (h : checkAtom (.move source destination) world = .ok next)
    (hr : resolve world ⟨source, []⟩ = some resolved)
    (hlin : resolved.grant.linear = true) :
    (∀ dep ∈ resolved.permission.dependencies, (lookupToken next dep).any Token.active = false) ∧
      ∃ fresh, lookupToken next world.nextToken = some fresh ∧
        fresh.linear = true ∧ fresh.active = true ∧ fresh.region = resolved.pointer := by
  refine ⟨fun dep hdep => handoff_revokes_dependency h hr hdep, ?_⟩
  obtain ⟨actual, resolvedAt, _, table, _⟩ := move_facts h
  have eq : actual = resolved := Option.some.inj (resolvedAt.symm.trans hr)
  subst actual
  refine ⟨⟨world.nextToken, resolved.pointer, true, false, true, false, world.scope,
    resolved.permission.dependencies, [], resolved.grant.linear⟩, ?_, hlin, rfl, rfl⟩
  unfold lookupToken
  rw [table, List.find?_cons]
  simp

theorem destructure_facts (h : checkAtom (.destructure source) world = .ok next) :
    ∃ resolved, resolve world ⟨source, []⟩ = some resolved ∧ eligibleMove world resolved = true ∧
      next.tokens = (endTokens world resolved.permission.dependencies).tokens ∧
      Use.mk source .writable ∈ next.uses := by
  have executed := (checked_atom_facts h).executed
  cases hr : resolve world ⟨source, []⟩ with
  | none => simp [transfer, eraseAtom, rawStep, hr] at executed
  | some resolved =>
    simp only [transfer, eraseAtom, rawStep, hr] at executed
    change (if eligibleMove world resolved then _ else _) = some next at executed
    split at executed
    · rename_i helig
      cases executed
      exact ⟨resolved, rfl, helig, rfl, by simp [markUse]⟩
    · contradiction

theorem destructure_revokes_dependency (h : checkAtom (.destructure source) world = .ok next)
    (hr : resolve world ⟨source, []⟩ = some resolved) (hd : id ∈ resolved.permission.dependencies) :
    (lookupToken next id).any Token.active = false := by
  obtain ⟨actual, resolvedAt, _, table, _⟩ := destructure_facts h
  have eq : actual = resolved := Option.some.inj (resolvedAt.symm.trans hr)
  subst actual
  have hlook : lookupToken next id = lookupToken (endBoundary world resolved.permission.dependencies) id := by
    unfold lookupToken endBoundary
    rw [table]
  rw [hlook]
  exact ended_not_active hd

theorem destructure_discharges_and_revokes
    (h : checkAtom (.destructure source) world = .ok next)
    (hr : resolve world ⟨source, []⟩ = some resolved) :
    Use.mk source .writable ∈ next.uses ∧
      (∀ dep ∈ resolved.permission.dependencies, (lookupToken next dep).any Token.active = false) ∧
      (∀ path derived dep, resolve next path = some derived →
        dep ∈ derived.permission.dependencies → dep ∈ resolved.permission.dependencies →
        live derived = false) := by
  obtain ⟨actual, resolvedAt, _, _, huse⟩ := destructure_facts h
  have eq : actual = resolved := Option.some.inj (resolvedAt.symm.trans hr)
  subst actual
  refine ⟨huse, fun dep hdep => destructure_revokes_dependency h hr hdep, ?_⟩
  intro path derived dep hcur hdep hold
  cases hl : live derived with
  | false => rfl
  | true =>
    have enabled := resolved_live_dependencies (checked_atom_facts h).afterLedger hcur hl
    simp only [lifetimeEnabled, Bool.and_eq_true] at enabled
    have active := List.all_eq_true.mp enabled.2 dep hdep
    simp [destructure_revokes_dependency h hr hold] at active

end RilAccess.Integrated
