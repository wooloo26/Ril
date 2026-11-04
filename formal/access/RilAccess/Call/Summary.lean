import RilAccess.Call.Entry

/-! Call-summary references have roles independent of SourceKind. A saved
allocation-origin capture is concrete; it is not a new callee allocation.
Only explicitly marked formal and fresh references may be substituted. -/
namespace RilAccess.CoreSummary

inductive Reference where
  | concrete (origin : Origin)
  | parameter (formal selection : Nat)
  | fresh (source : Source) (serial : Nat)
  deriving Repr, DecidableEq

structure Template where
  rootReturn : List Reference := []
  contained : List Reference := []
  writes : List Reference := []
  retained : List Reference := []
  createdEnvironments : List Reference := []
  namedReads : List Reference := []
  effects : List Nat := []
  deriving Repr, DecidableEq

structure CallInstance where
  parameter : Nat → Nat → Origin
  existingObjects : List Nat
  activation : Nat
  task : Nat
  scope : Nat

def resolve (actual : CallInstance) : Reference → Origin
  | .concrete origin => origin
  | .parameter formal selection => actual.parameter formal selection
  | .fresh source serial =>
    ⟨source, actual.activation, freshObject actual.existingObjects serial, actual.task, actual.scope⟩

def references (summary : Template) : List Reference :=
  summary.rootReturn ++ summary.contained ++ summary.writes ++ summary.retained ++
    summary.createdEnvironments ++ summary.namedReads

def origins (summary : Summary) : List Origin :=
  summary.rootReturn ++ summary.contained ++ summary.writes ++ summary.retained ++
    summary.createdEnvironments ++ summary.namedReads

def instantiate (actual : CallInstance) (summary : Template) : Summary :=
  ⟨summary.rootReturn.map (resolve actual), summary.contained.map (resolve actual), summary.writes.map (resolve actual),
    summary.retained.map (resolve actual), summary.createdEnvironments.map (resolve actual),
    summary.namedReads.map (resolve actual), summary.effects⟩

def referenceValid (actual : CallInstance) (entries : List CoreEntry.Snapshot) : Reference → Bool
  | .concrete origin => decide (origin.object ∈ actual.existingObjects) &&
      !owned actual.activation actual.task actual.scope origin
  | .parameter formal selection => (entries.any (fun entry =>
      decide (entry.formal = formal ∧ actual.parameter formal selection ∈ entry.origins))) &&
      !owned actual.activation actual.task actual.scope (actual.parameter formal selection)
  | .fresh source _ => decide (source.kind = .allocation)

def freshReferences (summary : Template) : List (Source × Nat) :=
  ((references summary).filterMap (fun reference => match reference with
    | .fresh source serial => some (source, serial) | _ => none)).eraseDups

def distinctFreshSerials (summary : Template) : Bool :=
  (freshReferences summary).all fun left => (freshReferences summary).all fun right =>
    decide (left = right ∨ left.2 ≠ right.2)

def valid (actual : CallInstance) (entries : List CoreEntry.Snapshot) (summary : Template) : Bool :=
  decide ((entries.map CoreEntry.Snapshot.formal).Nodup) &&
  distinctFreshSerials summary &&
  entries.all (fun entry => entry.origins.all (fun origin => decide (origin.object ∈ actual.existingObjects) &&
    !owned actual.activation actual.task actual.scope origin)) &&
  (references summary).all (referenceValid actual entries)

inductive Error where
  | invalidEntryOrSubstitution
  deriving Repr, DecidableEq

def check (actual : CallInstance) (entries : List CoreEntry.Snapshot) (summary : Template) : Except Error Summary :=
  if valid actual entries summary then .ok (instantiate actual summary) else .error .invalidEntryOrSubstitution

/-- Use the graph at call entry and already evaluated argument values. Do not
re-read argument slots or capture a graph after the callee has changed it. -/
def checkAtEntry (actual : CallInstance) (heapAtEntry : List HeapEdge)
    (arguments : List (Nat × List Origin)) (summary : Template) : Except Error Summary :=
  check actual (CoreEntry.capturePrepared heapAtEntry arguments) summary

theorem checked_valid (h : check actual entries summary = .ok result) :
    valid actual entries summary = true ∧ result = instantiate actual summary := by
  unfold check at h
  split at h
  · rename_i hv
    cases h
    exact ⟨hv, rfl⟩
  · contradiction

theorem all_components_instantiated :
    origins (instantiate actual summary) = (references summary).map (resolve actual) := by
  simp only [origins, instantiate, references, List.map_append]

theorem every_concrete_identity_survives (he : Reference.concrete origin ∈ references summary) :
    origin ∈ origins (instantiate actual summary) := by
  rw [all_components_instantiated]
  exact List.mem_map.mpr ⟨.concrete origin, he, rfl⟩

theorem checked_parameter_uses_frozen_entry
    (h : check actual entries summary = .ok result)
    (hr : Reference.parameter formal selection ∈ references summary) :
    ∃ entry ∈ entries, entry.formal = formal ∧ actual.parameter formal selection ∈ entry.origins := by
  have hv := (checked_valid h).1
  simp only [valid, Bool.and_eq_true] at hv
  have hp := List.all_eq_true.mp hv.2 (.parameter formal selection) hr
  have hh : entries.any (fun entry => decide (entry.formal = formal ∧ actual.parameter formal selection ∈ entry.origins)) = true ∧
      (!owned actual.activation actual.task actual.scope (actual.parameter formal selection)) = true := by
    simpa only [referenceValid, Bool.and_eq_true] using hp
  simpa only [List.any_eq_true, decide_eq_true_eq] using hh.1

theorem checked_at_entry_parameter_is_reachable
    (h : checkAtEntry actual heap arguments summary = .ok result)
    (hr : Reference.parameter formal selection ∈ references summary) :
    ∃ savedRoots, (formal, savedRoots) ∈ arguments ∧
      ∃ root ∈ savedRoots, Reach heap root (actual.parameter formal selection) := by
  obtain ⟨entry, he, hf, ho⟩ := checked_parameter_uses_frozen_entry h hr
  obtain ⟨⟨name, savedRoots⟩, ha, heq⟩ := List.mem_map.mp he
  cases heq
  change name = formal at hf
  cases hf
  exact ⟨savedRoots, ha, CoreEntry.entry_capture_exact.mp ho⟩

theorem fresh_origin_excludes_existing (ho : object ∈ actual.existingObjects) :
    (resolve actual (.fresh source serial)).object ≠ object ∧ (resolve actual (.fresh source serial)).source = source := by
  have hb := below_allocation_bound ho
  simp only [resolve, freshObject]
  constructor
  · omega
  · trivial

theorem checked_fresh_origin_excludes_frozen_entry
    (h : check actual entries summary = .ok result) (he : entry ∈ entries) (ho : origin ∈ entry.origins) :
    (resolve actual (.fresh source serial)).object ≠ origin.object := by
  have hv := (checked_valid h).1
  simp only [valid, Bool.and_eq_true] at hv
  have hob : origin.object ∈ actual.existingObjects :=
    by
      have hp := List.all_eq_true.mp (List.all_eq_true.mp hv.1.2 entry he) origin ho
      have hh : origin.object ∈ actual.existingObjects ∧ owned actual.activation actual.task actual.scope origin = false := by
        simpa only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] using hp
      exact hh.1
  exact (fresh_origin_excludes_existing hob).1

theorem checked_existing_origin_is_not_callee_local
    (h : check actual entries summary = .ok result) (hr : reference ∈ references summary)
    (hn : ∀ source serial, reference ≠ .fresh source serial) :
    owned actual.activation actual.task actual.scope (resolve actual reference) = false := by
  have hv := (checked_valid h).1
  simp only [valid, Bool.and_eq_true] at hv
  have hp := List.all_eq_true.mp hv.2 reference hr
  cases reference with
  | fresh source serial => exact False.elim (hn source serial rfl)
  | concrete origin =>
    have hh : origin.object ∈ actual.existingObjects ∧ owned actual.activation actual.task actual.scope origin = false := by
      simpa only [referenceValid, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] using hp
    exact hh.2
  | parameter formal selection =>
    have hh : entries.any (fun entry => decide (entry.formal = formal ∧ actual.parameter formal selection ∈ entry.origins)) = true ∧
        owned actual.activation actual.task actual.scope (actual.parameter formal selection) = false := by
      simpa only [referenceValid, Bool.and_eq_true, Bool.not_eq_true'] using hp
    exact hh.2

theorem checked_distinct_fresh_objects
    (h : check actual entries summary = .ok result)
    (hl : Reference.fresh leftSource leftSerial ∈ references summary)
    (hr : Reference.fresh rightSource rightSerial ∈ references summary)
    (hne : (leftSource, leftSerial) ≠ (rightSource, rightSerial)) :
    (resolve actual (.fresh leftSource leftSerial)).object ≠
      (resolve actual (.fresh rightSource rightSerial)).object := by
  have hv := (checked_valid h).1
  simp only [valid, Bool.and_eq_true] at hv
  have leftMem : (leftSource, leftSerial) ∈ freshReferences summary :=
    List.mem_eraseDups.mpr (List.mem_filterMap.mpr ⟨.fresh leftSource leftSerial, hl, rfl⟩)
  have rightMem : (rightSource, rightSerial) ∈ freshReferences summary :=
    List.mem_eraseDups.mpr (List.mem_filterMap.mpr ⟨.fresh rightSource rightSerial, hr, rfl⟩)
  have hp := List.all_eq_true.mp (List.all_eq_true.mp hv.1.1.2 _ leftMem) _ rightMem
  have serials : leftSerial ≠ rightSerial := (of_decide_eq_true hp).resolve_left hne
  intro equalObjects
  exact serials (fresh_object_injective equalObjects)

end RilAccess.CoreSummary
