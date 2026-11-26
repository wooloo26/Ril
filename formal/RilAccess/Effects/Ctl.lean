import RilAccess.Access.Scoped

/-! One-shot algebraic `ctl(...)` continuations, must-consume linearity (`E0625`),
projected/double invocation rejection (`E0548` / `E0549`), affine `&once` capture
restrictions (`E0625` / `E0720` / `E0549`), `^mut` downgrade prohibition across
unhandled effects (`E0523` / `E0524`), and `K-IFACE` `no_ctl_params` (`E0616`). -/
namespace RilAccess.CoreCtl

open Integrated

inductive LinearKind where
  | ctlContinuation | foreignHandle | opaqueMustConsume
  deriving Repr, DecidableEq

structure LinearEntry where
  id : Nat
  kind : LinearKind
  consumed : Bool := false
  armedDefer : Option Nat := none
  deriving Repr, DecidableEq

structure LinearState where
  boundary : Nat
  entries : List LinearEntry := []
  deriving Repr, DecidableEq

/-- Direct root consumption of a linear value (`k(...)`, `abort(new k)`, or
`close(new h)`). Projected paths (`obj.k()`) are rejected (`E0548`), and
already-consumed entries cannot be used a second time (`E0549`). -/
def consumeLinear (st : LinearState) (targetId : Nat) (projected : Bool) : Option LinearState :=
  if projected then none
  else
    match st.entries.find? (fun e => decide (e.id = targetId)) with
    | none => none
    | some entry =>
      if entry.consumed then none
      else
        some { st with
          entries := st.entries.map fun e =>
            if e.id = targetId then { e with consumed := true } else e }

/-- Arm a lexical `defer` at `deferScope` to manage a live must-consume value. -/
def armDefer (st : LinearState) (targetId deferScope : Nat) : Option LinearState :=
  match st.entries.find? (fun e => decide (e.id = targetId)) with
  | none => none
  | some entry =>
    if !entry.consumed && decide (st.boundary ≤ deferScope) then
      some { st with
        entries := st.entries.map fun e =>
          if e.id = targetId then { e with armedDefer := some deferScope } else e }
    else none

/-- Crossing an unhandled `ctl` operation requires every unconsumed must-consume
value to be managed by an armed `defer` inside the current `ctl` boundary (`E0625`). -/
def canCrossUnhandledCtl (st : LinearState) : Bool :=
  st.entries.all fun entry =>
    entry.consumed || entry.armedDefer.any (fun s => decide (st.boundary ≤ s))

/-- Executing armed `defer` actions at scope exit discharges their managed entries. -/
def runArmedDefers (st : LinearState) : LinearState :=
  { st with
    entries := st.entries.map fun e =>
      if e.armedDefer.isSome then { e with consumed := true } else e }

/-- Normal or unwinding scope exit requires all must-consume entries to be consumed (`E0625`). -/
def canExitLinearScope (st : LinearState) : Bool :=
  st.entries.all LinearEntry.consumed

theorem projected_ctl_invocation_rejected {st : LinearState} {targetId : Nat} :
    consumeLinear st targetId true = none := rfl

theorem double_ctl_consumption_rejected
    {st next : LinearState} {targetId : Nat} {anyProjected : Bool}
    (h : consumeLinear st targetId false = some next) :
    consumeLinear next targetId anyProjected = none := by
  unfold consumeLinear at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  cases hf : st.entries.find? (fun e => decide (e.id = targetId)) with
  | none => simp [hf] at h
  | some entry =>
    have hid : entry.id = targetId := of_decide_eq_true
      (List.find?_some (p := fun candidate : LinearEntry => decide (candidate.id = targetId)) hf)
    simp only [hf] at h
    cases hc : entry.consumed with
    | true => simp [hc] at h
    | false =>
      simp only [hc, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
      subst next
      cases anyProjected with
      | true => rfl
      | false =>
        unfold consumeLinear
        simp only [Bool.false_eq_true, ↓reduceIte]
        have hfindNext :
            ((st.entries.map fun e => if e.id = targetId then { e with consumed := true } else e).find?
              (fun e => decide (e.id = targetId))) = some { entry with consumed := true } := by
          rw [List.find?_map]
          have keepId : ∀ candidate : LinearEntry,
              (if candidate.id = targetId then { candidate with consumed := true } else candidate).id =
                candidate.id := by
            intro candidate; split <;> rfl
          simp only [Function.comp_def, keepId, hf, Option.map_some, hid, ↓reduceIte]
        simp [hfindNext]

theorem unarmed_must_consume_blocks_unhandled_ctl
    {st : LinearState} {entry : LinearEntry}
    (hm : entry ∈ st.entries) (hunc : entry.consumed = false) (hunarmed : entry.armedDefer = none) :
    canCrossUnhandledCtl st = false := by
  cases hc : canCrossUnhandledCtl st with
  | false => rfl
  | true =>
    have hall := List.all_eq_true.mp hc entry hm
    simp [hunc, hunarmed] at hall

theorem unconsumed_linear_blocks_exit
    {st : LinearState} {entry : LinearEntry}
    (hm : entry ∈ st.entries) (hunc : entry.consumed = false) :
    canExitLinearScope st = false := by
  cases hc : canExitLinearScope st with
  | false => rfl
  | true =>
    have hall := List.all_eq_true.mp hc entry hm
    simp [hunc] at hall

theorem armed_entries_discharged_on_exit {st : LinearState}
    (hcross : canCrossUnhandledCtl st = true) :
    canExitLinearScope (runArmedDefers st) = true := by
  simp only [canExitLinearScope, runArmedDefers, List.all_map, List.all_eq_true, Function.comp_def]
  intro entry hm
  have hEntry := List.all_eq_true.mp hcross entry hm
  simp only [Bool.or_eq_true] at hEntry
  rcases hEntry with hcons | harm
  · split <;> simp [hcons]
  · cases hd : entry.armedDefer with
    | none => simp [hd] at harm
    | some _ => simp

/-- Affine `&once` closures forbid capturing must-consume values (`E0625`) or
uninspected fallible results (`E0720`), while allowing single-use `new` handoff
of ordinary owned bindings (`E0549`). -/
def eligibleOnceCapture (world : World) (r : Resolved)
    (isMustConsume hasUninspectedResult : Bool) : Bool :=
  !isMustConsume && !hasUninspectedResult && eligibleHandoff world r

def onceCaptureHandoff (world : World) (source destination : Nat)
    (isMustConsume hasUninspectedResult : Bool) : Except Error World :=
  let handoff := Atom.handoff source destination
  if !isMustConsume && !hasUninspectedResult then checkAtom handoff world
  else .error (.rejected handoff)

theorem once_closure_rejects_must_consume_capture
    {world : World} {r : Resolved} {hasUninspectedResult : Bool} :
    eligibleOnceCapture world r true hasUninspectedResult = false := rfl

theorem once_handoff_ends_parent_path
    {world next : World} {source destination : Nat} {resolved : Resolved}
    (h : onceCaptureHandoff world source destination false false = .ok next)
    (hr : resolve world ⟨source, []⟩ = some resolved) :
    rawLookup next.raw destination = some resolved.pointer ∧
    (∀ dep ∈ resolved.binding.dependencies, (lookupToken next dep).any Token.active = false) ∧
    (∀ path derived dep, resolve next path = some derived →
      dep ∈ derived.binding.dependencies → dep ∈ resolved.binding.dependencies →
      live derived = false) := by
  have handed : checkAtom (.handoff source destination) world = .ok next := by
    simpa [onceCaptureHandoff] using h
  obtain ⟨actual, hres, hptr⟩ := handoff_preserves_identity handed
  have eq : actual = resolved := Option.some.inj (hres.symm.trans hr)
  subst actual
  exact ⟨hptr,
    fun dep hdep => handoff_revokes_dependency handed hr hdep,
    fun path derived dep hcur hdep hold => handoff_ends_derived_access handed hr hcur hdep hold⟩

/-- Across unhandled `ctl`, open `@`, or unhandled `@Eff`, a `^mut` shared writer
cannot downgrade to exclusive `mut` (`E0523`) or read-only `ref` (`E0524`). -/
def canPassSharedAs (argAccess : Access) (paramMode : ParameterMode)
    (mayPerformUnhandledEffect : Bool) : Bool :=
  !(decide (argAccess = .shared) && mayPerformUnhandledEffect &&
    (decide (paramMode = .mutable) || decide (paramMode = .observe)))

theorem shared_writer_forbids_downgrade_across_unhandled_effect
    {paramMode : ParameterMode}
    (hmode : paramMode = .mutable ∨ paramMode = .observe) :
    canPassSharedAs .shared paramMode true = false := by
  rcases hmode with rfl | rfl <;> rfl

/-- `K-IFACE` separate-compilation guard: an open-`@` callback parameter marked in
`no_ctl_params` (invoked inside `defer` or a `fn` handler arm) rejects any
argument that may perform an unhandled `ctl` effect (`E0616`). -/
def checkNoCtlCall (noCtlParams : List Nat) (argIdx : Nat) (argMayPerformCtl : Bool) : Bool :=
  !(noCtlParams.contains argIdx && argMayPerformCtl)

theorem no_ctl_param_rejects_ctl_callback {noCtlParams : List Nat} {argIdx : Nat}
    (hmem : argIdx ∈ noCtlParams) :
    checkNoCtlCall noCtlParams argIdx true = false := by
  simp [checkNoCtlCall, hmem]

end RilAccess.CoreCtl
