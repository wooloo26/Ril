import RilAccess.Access.Scoped

/-! Structured fiber concurrency (`Fiber::Scope`, `Fiber::Task<T>`, `@fiber`),
cross-fiber capture isolation (`E0601` / `E0549`), channel mutability-laundering
prevention (`E0548`), nursery region branding (`E0604`), and mandatory fallible
`Result` task inspection (`E0720`). -/
namespace RilAccess.CoreConcurrency

open Integrated

inductive CaptureFlavor where
  | sharedImmutable | singleShotHandoff
  deriving Repr, DecidableEq

private def sendableMember (access : Access) : Bool :=
  access != .ref && access != .shared

/-- The data fragment of Sendable represented by the binding-access ledger. -/
def sendableData (r : Resolved) : Bool :=
  !r.grant.resource && r.grant.schema.all fun field =>
    !(r.pointer.fields.isPrefixOf field.coordinate && r.pointer.fields != field.coordinate) ||
      sendableMember field.mode.access

/-- E0601 permits shared capture of pinned deeply immutable bindings. -/
def eligibleSharedCapture (world : World) (r : Resolved) : Bool :=
  receiving world r ⟨false, .immutable⟩ world.scope &&
    !r.binding.mode.replaceable && (r.binding.mode.access == .immutable) &&
    r.members.all sendableMember && sendableData r

def spawnSharedCapture (world : World) (source : Path) (childDestination : Nat) : Except Error World :=
  let bind := Atom.bind source childDestination ⟨false, .immutable⟩
  if (resolve world source).any (eligibleSharedCapture world) then checkAtom bind world
  else .error (.rejected bind)

/-- Single-shot task closures (`run`, `spawn`, `zip`, `try_zip`, `race`, `supervise`,
`timeout_ms`) may hand off a `new`-qualified binding once (`E0549`). -/
def spawnHandoffCapture (world : World) (source childDestination : Nat) : Except Error World :=
  let handoff := Atom.handoff source childDestination
  if (resolve world ⟨source, []⟩).any sendableData then checkAtom handoff world
  else .error (.rejected handoff)

/-- E0548 channel send reception: writable-constituent payloads require single-use
`new` handoff so `Channel::recv -> new ?T` cannot launder mutability. -/
def eligibleChannelSend (requiresHandoff : Bool) (world : World) (r : Resolved) : Bool :=
  sendableData r &&
    (if requiresHandoff then eligibleHandoff world r else receiving world r ⟨false, .immutable⟩ world.scope)

theorem cross_fiber_capture_rejects_mutable_scoped_or_resource {world : World} {r : Resolved}
    (h : eligibleSharedCapture world r = true) :
    r.grant.resource = false ∧ r.binding.isScoped = false ∧
      deepImmutable r = true ∧ live r = true ∧
      r.binding.mode.replaceable = false ∧ r.binding.mode.access = .immutable ∧
      sendableData r = true := by
  simp only [eligibleSharedCapture, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨⟨⟨received, pinned⟩, mode⟩, _⟩, sendable⟩ := h
  simp only [receiving, Bool.and_eq_true, Bool.not_eq_true'] at received
  exact ⟨received.2.1, received.1.1.1.2, received.2.2, received.1.1.1.1,
    pinned, mode, sendable⟩

theorem mutable_scoped_or_resource_rejected_by_shared_capture {world : World} {r : Resolved}
    (hbad : r.grant.resource = true ∨ r.binding.isScoped = true ∨
      (r.binding.immutableSource = false ∧ r.effective.writes = true)) :
    eligibleSharedCapture world r = false := by
  rcases hbad with hres | hsc | ⟨hnoOrig, hw⟩
  · simp [eligibleSharedCapture, receiving, hres]
  · simp [eligibleSharedCapture, receiving, hsc]
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

theorem shared_capture_forbids_authorized_writes {world : World} {path : Path} {e : AccessCheck}
    (hr : resolve world path = some e.resolved)
    (himm : e.resolved.binding.mode.access = .immutable)
    (hauth : authorized e = true) :
    e.rule = .read ∧ e.observation.kind = .read := by
  have htrav : e.resolved.effective = .immutable ∧ e.resolved.parentAccess = .immutable := by
    unfold resolve at hr
    cases hp : lookupBinding world path.register with
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

theorem spawned_handoff_disjoint_from_parent_live_bindings
    {world next : World} {source childDestination : Nat} {resolved : Resolved}
    (h : spawnHandoffCapture world source childDestination = .ok next)
    (hr : resolve world ⟨source, []⟩ = some resolved) :
    sendableData resolved = true ∧
    rawLookup next.raw childDestination = some resolved.pointer ∧
    (∀ dep ∈ resolved.binding.dependencies, (lookupToken next dep).any Token.active = false) ∧
    (∀ path derived dep, resolve next path = some derived →
      dep ∈ derived.binding.dependencies → dep ∈ resolved.binding.dependencies →
      live derived = false) := by
  have sendable : sendableData resolved = true := by
    by_cases hs : sendableData resolved = true
    · exact hs
    · simp [spawnHandoffCapture, hr, hs] at h
  have handed : checkAtom (.handoff source childDestination) world = .ok next := by
    simpa [spawnHandoffCapture, hr, sendable] using h
  obtain ⟨actual, hres, hptr⟩ := handoff_preserves_identity handed
  have eq : actual = resolved := Option.some.inj (hres.symm.trans hr)
  subst actual
  exact ⟨sendable, hptr,
    fun dep hdep => handoff_revokes_dependency handed hr hdep,
    fun path derived dep hcur hdep hold => handoff_ends_derived_access handed hr hcur hdep hold⟩

theorem frozen_object_cannot_launder_mutability_via_channel
    {world : World} {r : Resolved} (hfrozen : r.effective = .immutable) :
    eligibleChannelSend true world r = false := by
  simp [eligibleChannelSend, eligibleHandoff, hfrozen, Access.writes]

inductive TaskMode where
  | sharedImmutable | exclusiveSingleShot
  deriving Repr, DecidableEq

structure TaskEntry where
  id : Nat
  regionSigma : Nat
  mode : TaskMode
  fallibleResult : Bool := false
  handedOff : Bool := false
  settled : Bool := false
  pendingInspections : Nat := 0
  deriving Repr, DecidableEq

structure ScopeState where
  activeSigma : Nat
  tasks : List TaskEntry := []
  deriving Repr, DecidableEq

private def TaskEntry.joined (entry : TaskEntry) (asHandoff : Bool) : TaskEntry :=
  { entry with
    handedOff := asHandoff
    settled := true
    pendingInspections := entry.pendingInspections + entry.fallibleResult.toNat }

/-- `Fiber::join(mut s, via task)`: `asMove = true` models `join(mut s, new task)`
on exclusive handles; `asMove = false` models idempotent memoized `join(mut s, task)`
on plain `let` handles. Inspection of the returned Result is a separate action. -/
def joinTask (taskScope : ScopeState) (taskId taskSigma : Nat) (asHandoff : Bool) : Option ScopeState := do
  let entry ← taskScope.tasks.find? (fun t => decide (t.id = taskId))
  let mode := if asHandoff then TaskMode.exclusiveSingleShot else .sharedImmutable
  if decide (taskSigma = taskScope.activeSigma ∧ entry.regionSigma = taskScope.activeSigma) &&
      !entry.handedOff && decide (entry.mode = mode) then
    some { taskScope with tasks := taskScope.tasks.map fun t =>
      if t.id = taskId then t.joined asHandoff else t }
  else none

/-- `Fiber::cancel(mut s, new task)`: requires matching task scope identity (`E0604`)
and an un-handed-off exclusive handle (`E0549`). -/
def cancelTask (taskScope : ScopeState) (taskId taskSigma : Nat) : Option ScopeState := do
  let entry ← taskScope.tasks.find? (fun t => decide (t.id = taskId))
  if decide (taskSigma = taskScope.activeSigma ∧ entry.regionSigma = taskScope.activeSigma) &&
      decide (entry.mode = .exclusiveSingleShot) && !entry.handedOff then
    some { taskScope with
      tasks := taskScope.tasks.map fun t =>
        if t.id = taskId then { t with handedOff := true, settled := true } else t }
  else none

/-- Record the inspection of the Result produced by a successful join. -/
def inspectJoinedResult (taskScope : ScopeState) (taskId taskSigma : Nat) : Option ScopeState := do
  let entry ← taskScope.tasks.find? (fun t => decide (t.id = taskId))
  if decide (taskSigma = taskScope.activeSigma ∧ entry.regionSigma = taskScope.activeSigma) &&
      entry.fallibleResult && entry.settled && decide (entry.pendingInspections > 0) then
    some { taskScope with tasks := taskScope.tasks.map fun t =>
      if t.id = taskId then { t with pendingInspections := t.pendingInspections - 1 } else t }
  else none

def TaskEntry.pendingResult (entry : TaskEntry) : Bool :=
  entry.fallibleResult && !(entry.settled && decide (entry.pendingInspections = 0))

def canExitScope (taskScope : ScopeState) : Bool :=
  taskScope.tasks.all fun entry => entry.settled && !entry.pendingResult

/-- Static normal-exit barrier (`E0720`). Once Result obligations are handled,
implicit awaits can settle the remaining plain tasks. -/
def drainPlainTasks (taskScope : ScopeState) : Option ScopeState :=
  if taskScope.tasks.any TaskEntry.pendingResult then
    none
  else
    some { taskScope with tasks := taskScope.tasks.map fun t => { t with settled := true } }

theorem cross_scope_task_rejected {taskScope : ScopeState} {taskId taskSigma : Nat} {asHandoff : Bool}
    (hcross : taskSigma ≠ taskScope.activeSigma) :
    joinTask taskScope taskId taskSigma asHandoff = none ∧
      cancelTask taskScope taskId taskSigma = none := by
  unfold joinTask cancelTask
  cases hf : taskScope.tasks.find? (fun t => decide (t.id = taskId)) with
  | none => simp
  | some entry => simp [hcross]

theorem duplicate_exclusive_task_handoff_rejected
    {taskScope next : ScopeState} {taskId taskSigma nextSigma : Nat} {anyHandoff : Bool}
    (h : joinTask taskScope taskId taskSigma true = some next) :
    joinTask next taskId nextSigma anyHandoff = none ∧
      cancelTask next taskId nextSigma = none := by
  unfold joinTask at h
  cases hf : taskScope.tasks.find? (fun t => decide (t.id = taskId)) with
  | none => simp [hf] at h
  | some entry =>
    have hid : entry.id = taskId := of_decide_eq_true
      (List.find?_some (p := fun candidate : TaskEntry => decide (candidate.id = taskId)) hf)
    simp only [hf, ↓reduceIte] at h
    change (if _ then _ else _) = some next at h
    split at h
    · cases h
      have hfindNext :
          ((taskScope.tasks.map fun t => if t.id = taskId then t.joined true else t).find?
            (fun t => decide (t.id = taskId))) = some (entry.joined true) := by
        rw [List.find?_map]
        have keepId : ∀ candidate : TaskEntry,
            (if candidate.id = taskId then candidate.joined true else candidate).id = candidate.id := by
          intro candidate; split <;> rfl
        simp only [Function.comp_def, keepId, hf, Option.map_some, hid, ↓reduceIte]
      unfold joinTask cancelTask
      simp only [hfindNext]
      simp [TaskEntry.joined]
    · contradiction

theorem pending_result_blocks_scope_exit
    {taskScope : ScopeState} {entry : TaskEntry}
    (hm : entry ∈ taskScope.tasks) (hpending : entry.pendingResult = true) :
    canExitScope taskScope = false ∧ drainPlainTasks taskScope = none := by
  have hnotExit : canExitScope taskScope = false := by
    cases hc : canExitScope taskScope with
    | false => rfl
    | true =>
      have hall := List.all_eq_true.mp hc entry hm
      simp [hpending] at hall
  have hany : taskScope.tasks.any TaskEntry.pendingResult = true :=
    List.any_eq_true.mpr ⟨entry, hm, hpending⟩
  exact ⟨hnotExit, by simp [drainPlainTasks, hany]⟩

theorem drainPlainTasks_enables_scope_exit {taskScope drained : ScopeState}
    (h : drainPlainTasks taskScope = some drained) :
    canExitScope drained = true := by
  unfold drainPlainTasks at h
  split at h
  · contradiction
  · rename_i clear
    cases h
    simp only [canExitScope, List.all_map, List.all_eq_true, Function.comp_def, Bool.true_and]
    intro entry member
    have pending : entry.pendingResult = false := by
      cases hp : entry.pendingResult
      · rfl
      · exact False.elim (clear (List.any_eq_true.mpr ⟨entry, member, hp⟩))
    by_cases fallible : entry.fallibleResult = true
    · have completed : entry.settled = true ∧ entry.pendingInspections = 0 := by
        simpa [TaskEntry.pendingResult, fallible, Bool.and_eq_true] using pending
      simp [TaskEntry.pendingResult, completed.2]
    · simp [TaskEntry.pendingResult, fallible]

end RilAccess.CoreConcurrency
