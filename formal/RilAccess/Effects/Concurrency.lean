import RilAccess.Access.Handoff
import RilAccess.Access.Linear
import RilAccess.Effects.Resumption

/-! Structured async concurrency (`@Scope`, `@Async`), cross-fiber capture isolation
(`E0601` / `E0549`), channel mutability-laundering prevention (`E0548`), nursery
region branding (`E0604`), mandatory task/result consumption (`E0720` / `E0721`),
and cancellation-checkpoint shielding (`Async::uncancellable`). -/
namespace RilAccess.CoreConcurrency

open Integrated

inductive CaptureFlavor where
  | sharedImmutable | singleShotMove
  deriving Repr, DecidableEq

/-- E0601 shared cross-fiber capture check: concurrent task closures may share only
non-linear, deeply immutable bindings with no conflicting active writes. -/
def eligibleSharedCapture (world : World) (r : Resolved) : Bool :=
  receiving world r ⟨false, .immutable⟩ world.scope

def spawnSharedCapture (world : World) (source : Path) (childDestination : Nat) : Except Error World :=
  checkAtom (.bind source childDestination ⟨false, .immutable⟩) world

/-- Single-shot task closures (`run`, `spawn`, `zip`, `try_zip`, `race`, `supervise`,
`timeout_ms`) may consume a qualified `new` / `linear` binding once via move handoff. -/
def spawnMoveCapture (world : World) (source childDestination : Nat) : Except Error World :=
  checkAtom (.move source childDestination) world

/-- E0548 channel send reception: writable-constituent or linear payloads require
exclusive `new` move handoff so `Channel::recv -> new ?T` cannot launder mutability. -/
def eligibleChannelSend (requiresMove : Bool) (world : World) (r : Resolved) : Bool :=
  if requiresMove then eligibleMove world r else eligibleSharedCapture world r

theorem cross_fiber_capture_rejects_mutable_or_linear {world : World} {r : Resolved}
    (h : eligibleSharedCapture world r = true) :
    r.grant.linear = false ∧ deepImmutable r = true ∧ live r = true := by
  simp only [eligibleSharedCapture, receiving, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact ⟨h.2.1, h.2.2, h.1.1.1⟩

theorem mutable_or_linear_rejected_by_shared_capture {world : World} {r : Resolved}
    (hbad : r.grant.linear = true ∨ (r.permission.immutableOrigin = false ∧ r.effective.writes = true)) :
    eligibleSharedCapture world r = false := by
  rcases hbad with hlin | ⟨hnoOrig, hw⟩
  · simp [eligibleSharedCapture, receiving, hlin]
  · have hnotImm : r.effective ≠ .immutable := by
      intro heq
      rw [heq] at hw
      simp [Access.writes] at hw
    simp [eligibleSharedCapture, receiving, deepImmutable, hnoOrig, hnotImm]

theorem traverse_immutable_stays_immutable {schema : Schema} {base fields : List Nat}
    {members : List Access} {effective parent : Access} {replaceable object : Bool}
    (ht : traverse schema base .immutable fields = some (members, effective, parent, replaceable, object)) :
    effective = .immutable ∧ parent = .immutable := by
  induction fields generalizing base members effective parent replaceable object with
  | nil =>
    simp [traverse] at ht
    exact ⟨ht.2.1.symm, ht.2.2.1.symm⟩
  | cons field rest ih =>
    unfold traverse at ht
    cases hf : schema.find? (fun member => decide (member.coordinate = base ++ [field])) with
    | none => simp [hf] at ht
    | some member =>
      by_cases hrem : rest.isEmpty = true
      · simp [hf, hrem, attenuate] at ht
        exact ⟨ht.2.1.symm, ht.2.2.1.symm⟩
      · by_cases hobj : member.object = true
        · simp [hf, hrem, hobj, attenuate] at ht
          cases hrec : traverse schema (base ++ [field]) .immutable rest with
          | none => simp [hrec] at ht
          | some res =>
            obtain ⟨ms, eff, par, rep, obj⟩ := res
            simp [hrec] at ht
            rcases ht with ⟨_, rfl, rfl, _, _⟩
            exact ih hrec
        · simp [hf, hrem, hobj] at ht

theorem shared_capture_forbids_authorized_writes {world : World} {path : Path} {e : Evidence}
    (hr : resolve world path = some e.resolved)
    (himm : e.resolved.permission.mode.access = .immutable)
    (hauth : authorized e = true) :
    e.rule = .read ∧ e.observation.kind = .read := by
  have htrav : e.resolved.effective = .immutable ∧ e.resolved.parentAccess = .immutable := by
    unfold resolve at hr
    cases hp : lookupPermission world path.register with
    | none => simp [hp] at hr
    | some perm =>
      cases hroot : rawLookup world.raw path.register with
      | none => simp [hp, hroot] at hr
      | some root =>
        cases hg : world.grants.find? (fun grant => decide (grant.object = root.object)) with
        | none => simp [hp, hroot, hg] at hr
        | some grant =>
          cases ht : traverse grant.schema root.fields perm.mode.access path.fields with
          | none => simp [hp, hroot, hg, ht] at hr
          | some res =>
            obtain ⟨ms, eff, par, rep, obj⟩ := res
            simp [hp, hroot, hg, ht] at hr
            have hperm : perm.mode.access = .immutable := by
              rw [← hr] at himm
              exact himm
            rw [hperm] at ht
            have ⟨heff, hpar⟩ := traverse_immutable_stays_immutable ht
            rw [← hr]
            exact ⟨heff, hpar⟩
  have hloc := authorization_local hauth
  cases hrule : e.rule with
  | read =>
    simp only [authorizedLocal, hrule, Bool.and_eq_true, decide_eq_true_eq] at hloc
    exact ⟨rfl, hloc.2⟩
  | write =>
    have hw := (authorized_interior_write hauth hrule).1
    simp [htrav.1, Access.writes] at hw
  | replaceScalar =>
    have hw := (authorized_scalar_replacement hauth hrule).2.2
    simp [htrav.2, Access.writes] at hw
  | retain =>
    simp [authorizedLocal, hrule, htrav.1, Access.writes] at hloc

theorem spawned_move_disjoint_from_parent_live_permissions
    {world next : World} {source childDestination : Nat} {resolved : Resolved}
    (h : spawnMoveCapture world source childDestination = .ok next)
    (hr : resolve world ⟨source, []⟩ = some resolved) :
    rawLookup next.raw childDestination = some resolved.pointer ∧
    (∀ dep ∈ resolved.permission.dependencies, (lookupToken next dep).any Token.active = false) ∧
    (∀ path derived dep, resolve next path = some derived →
      dep ∈ derived.permission.dependencies → dep ∈ resolved.permission.dependencies →
      live derived = false) := by
  obtain ⟨actual, hres, hptr⟩ := handoff_preserves_identity h
  have eq : actual = resolved := Option.some.inj (hres.symm.trans hr)
  subst actual
  exact ⟨hptr,
    fun dep hdep => handoff_revokes_dependency h hr hdep,
    fun path derived dep hcur hdep hold => handoff_ends_derived_access h hr hcur hdep hold⟩

theorem frozen_object_cannot_launder_mutability_via_channel
    {world : World} {r : Resolved} (hfrozen : r.effective = .immutable) :
    eligibleChannelSend true world r = false := by
  simp [eligibleChannelSend, eligibleMove, hfrozen, Access.writes]

inductive TaskMode where
  | sharedImmutable | exclusiveSingleShot
  deriving Repr, DecidableEq

structure TaskEntry where
  id : Nat
  regionSigma : Nat
  mode : TaskMode
  linearResult : Bool := false
  fallibleResult : Bool := false
  consumed : Bool := false
  settled : Bool := false
  deriving Repr, DecidableEq

structure NurseryState where
  activeSigma : Nat
  tasks : List TaskEntry := []
  deriving Repr, DecidableEq

/-- `Scope::join`: `asMove = true` models `join(new task)` on exclusive/linear handles;
`asMove = false` models idempotent memoized `join(task)` on plain `let` handles. -/
def joinTask (nursery : NurseryState) (taskId taskSigma : Nat) (asMove : Bool) : Option NurseryState := do
  let entry ← nursery.tasks.find? (fun t => decide (t.id = taskId))
  if decide (taskSigma = nursery.activeSigma ∧ entry.regionSigma = nursery.activeSigma) && !entry.consumed then
    if asMove then
      if decide (entry.mode = .exclusiveSingleShot) then
        some { nursery with
          tasks := nursery.tasks.map fun t =>
            if t.id = taskId then { t with consumed := true, settled := true } else t }
      else none
    else
      if decide (entry.mode = .sharedImmutable) && !entry.linearResult then
        some { nursery with
          tasks := nursery.tasks.map fun t =>
            if t.id = taskId then { t with settled := true } else t }
      else none
  else none

/-- `Scope::cancel(new task)`: requires matching nursery region `σ`, an unconsumed
exclusive handle, and a non-linear task result (`where T is ~Linear`). -/
def cancelTask (nursery : NurseryState) (taskId taskSigma : Nat) : Option NurseryState := do
  let entry ← nursery.tasks.find? (fun t => decide (t.id = taskId))
  if decide (taskSigma = nursery.activeSigma ∧ entry.regionSigma = nursery.activeSigma) &&
      decide (entry.mode = .exclusiveSingleShot) && !entry.consumed && !entry.linearResult then
    some { nursery with
      tasks := nursery.tasks.map fun t =>
        if t.id = taskId then { t with consumed := true, settled := true } else t }
  else none

def canExitScope (nursery : NurseryState) : Bool :=
  nursery.tasks.all fun t => t.settled && (!t.linearResult || t.consumed)

/-- Normal `scope` / `Ok` exit barrier: rejects unconsumed linear tasks (`E0721`) and
uninspected `Result` tasks (`E0720`), then awaits/settles remaining plain tasks. -/
def drainPlainTasks (nursery : NurseryState) : Option NurseryState :=
  if nursery.tasks.any (fun t => (t.linearResult && !t.consumed) || (t.fallibleResult && !t.settled)) then
    none
  else
    some { nursery with tasks := nursery.tasks.map fun t => { t with settled := true } }

theorem cross_scope_task_rejected {nursery : NurseryState} {taskId taskSigma : Nat} {asMove : Bool}
    (hcross : taskSigma ≠ nursery.activeSigma) :
    joinTask nursery taskId taskSigma asMove = none ∧
      cancelTask nursery taskId taskSigma = none := by
  unfold joinTask cancelTask
  cases hf : nursery.tasks.find? (fun t => decide (t.id = taskId)) with
  | none => simp
  | some entry => simp [hcross]

theorem duplicate_exclusive_task_consumption_rejected
    {nursery next : NurseryState} {taskId taskSigma nextSigma : Nat} {anyMove : Bool}
    (h : joinTask nursery taskId taskSigma true = some next) :
    joinTask next taskId nextSigma anyMove = none ∧
      cancelTask next taskId nextSigma = none := by
  unfold joinTask at h
  cases hf : nursery.tasks.find? (fun t => decide (t.id = taskId)) with
  | none => simp [hf] at h
  | some entry =>
    have hid : entry.id = taskId := of_decide_eq_true
      (List.find?_some (p := fun candidate : TaskEntry => decide (candidate.id = taskId)) hf)
    simp only [hf, ↓reduceIte] at h
    change (if _ then if _ then _ else _ else _) = some next at h
    split at h
    · split at h
      · cases h
        have hfindNext : nextSigma = nextSigma ∧
            ((nursery.tasks.map fun t =>
              if t.id = taskId then { t with consumed := true, settled := true } else t).find?
              (fun t => decide (t.id = taskId))) =
              some { entry with consumed := true, settled := true } := by
          refine ⟨rfl, ?_⟩
          rw [List.find?_map]
          have keepId : ∀ candidate : TaskEntry,
              (if candidate.id = taskId then { candidate with consumed := true, settled := true }
               else candidate).id = candidate.id := by
            intro candidate; split <;> rfl
          simp only [Function.comp_def, keepId, hf, Option.map_some, hid, ↓reduceIte]
        unfold joinTask cancelTask
        simp [hfindNext.2]
      · contradiction
    · contradiction

theorem linear_task_cannot_cancel_or_leak
    {nursery : NurseryState} {taskId sigma : Nat} {entry : TaskEntry}
    (hfind : nursery.tasks.find? (fun t => decide (t.id = taskId)) = some entry)
    (hlin : entry.linearResult = true) :
    cancelTask nursery taskId sigma = none ∧
      (entry.consumed = false → canExitScope nursery = false ∧ drainPlainTasks nursery = none) := by
  refine ⟨?_, ?_⟩
  · unfold cancelTask
    simp [hfind, hlin]
  · intro hunconsumed
    have hm := List.mem_of_find?_eq_some hfind
    have hnotExit : canExitScope nursery = false := by
      cases hc : canExitScope nursery with
      | false => rfl
      | true =>
        have hall := List.all_eq_true.mp hc entry hm
        simp [hlin, hunconsumed] at hall
    have hany : (nursery.tasks.any fun t =>
        (t.linearResult && !t.consumed) || (t.fallibleResult && !t.settled)) = true :=
      List.any_eq_true.mpr ⟨entry, hm, by simp [hlin, hunconsumed]⟩
    exact ⟨hnotExit, by simp [drainPlainTasks, hany]⟩

theorem unsettled_fallible_task_blocks_scope_exit
    {nursery : NurseryState} {entry : TaskEntry}
    (hm : entry ∈ nursery.tasks) (hfallible : entry.fallibleResult = true)
    (hunsettled : entry.settled = false) :
    canExitScope nursery = false ∧ drainPlainTasks nursery = none := by
  have hnotExit : canExitScope nursery = false := by
    cases hc : canExitScope nursery with
    | false => rfl
    | true =>
      have hall := List.all_eq_true.mp hc entry hm
      simp [hunsettled] at hall
  have hany : (nursery.tasks.any fun t =>
      (t.linearResult && !t.consumed) || (t.fallibleResult && !t.settled)) = true :=
    List.any_eq_true.mpr ⟨entry, hm, by simp [hfallible, hunsettled]⟩
  exact ⟨hnotExit, by simp [drainPlainTasks, hany]⟩

theorem drainPlainTasks_enables_scope_exit {nursery drained : NurseryState}
    (h : drainPlainTasks nursery = some drained) :
    canExitScope drained = true := by
  unfold drainPlainTasks at h
  split at h
  · contradiction
  · rename_i hnoBad
    cases h
    simp only [canExitScope, List.all_map]
    apply List.all_eq_true.mpr
    intro t ht
    have hnotBad : ((t.linearResult && !t.consumed) || (t.fallibleResult && !t.settled)) = false := by
      cases hb : (t.linearResult && !t.consumed) || (t.fallibleResult && !t.settled) with
      | false => rfl
      | true => exact False.elim (hnoBad (List.any_eq_true.mpr ⟨t, ht, hb⟩))
    cases hlin : t.linearResult <;> cases hcons : t.consumed <;> simp_all

/-- E0721 async cancellation checkpoint guard: unshielded `@Async` suspension points
cannot be crossed while an active linear token resides inside the cancellable scope;
`Async::uncancellable` (`uncancellable = true`) shields cancellation unwinding. -/
def canSuspendAsync (uncancellable : Bool) (delimiterScope : Nat) (authority : World) : Bool :=
  uncancellable || CoreResumption.canSuspendEffect delimiterScope authority

theorem unshielded_async_blocks_active_linear
    {delimiterScope : Nat} {authority : World} {token : Token}
    (hm : token ∈ authority.tokens) (hlin : token.linear = true) (hact : token.active = true)
    (hinner : delimiterScope < token.scope) :
    canSuspendAsync false delimiterScope authority = false ∧
      canSuspendAsync true delimiterScope authority = true := by
  have ⟨hblock, _⟩ := CoreResumption.active_inner_linear_blocks_suspension hm hlin hact hinner
  exact ⟨by simp [canSuspendAsync, hblock], by simp [canSuspendAsync]⟩

end RilAccess.CoreConcurrency
