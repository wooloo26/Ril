import RilAccess.Call.Entry
import RilAccess.Signatures

namespace RilAccess.CoreSummary

inductive Reference where
  | concrete (srcInst : SourceInstance)
  | parameter (formal selection : Nat)
  | allocated (source : Source) (serial : Nat)
  deriving Repr, DecidableEq

abbrev Template := SummaryOf Reference

structure CallInstance where
  parameter : Nat → Nat → SourceInstance
  existingObjects : List Nat
  activation : Nat
  scope : Nat

def resolve (actual : CallInstance) : Reference → SourceInstance
  | .concrete srcInst => srcInst
  | .parameter formal selection => actual.parameter formal selection
  | .allocated source serial =>
    ⟨source, actual.activation, allocatedObject actual.existingObjects serial, actual.scope⟩

def references (summary : Template) : List Reference :=
  summary.references

def srcInsts (summary : Summary) : List SourceInstance :=
  summary.references

def instantiate (actual : CallInstance) (summary : Template) : Summary :=
  summary.map (resolve actual)

def referenceValid (actual : CallInstance) (frozen : CoreEntry.Frozen) : Reference → Bool
  | .concrete srcInst => decide (srcInst.object ∈ actual.existingObjects) &&
      !allocatedIn actual.activation actual.scope srcInst
  | .parameter formal selection => (frozen.snapshots.any (fun entry =>
      decide (entry.formal = formal ∧ actual.parameter formal selection ∈ entry.srcInsts))) &&
      !allocatedIn actual.activation actual.scope (actual.parameter formal selection)
  | .allocated source _ => decide (source.kind = .allocation)

def allocatedReferences (summary : Template) : List (Source × Nat) :=
  ((references summary).filterMap (fun reference => match reference with
    | .allocated source serial => some (source, serial) | _ => none)).eraseDups

def distinctAllocationSerials (summary : Template) : Bool :=
  (allocatedReferences summary).all fun left => (allocatedReferences summary).all fun right =>
    decide (left = right ∨ left.2 ≠ right.2)

def valid (actual : CallInstance) (frozen : CoreEntry.Frozen) (summary : Template) : Bool :=
  decide ((frozen.snapshots.map CoreEntry.Snapshot.formal).Nodup) &&
  distinctAllocationSerials summary &&
  frozen.snapshots.all (fun entry => entry.srcInsts.all (fun srcInst => decide (srcInst.object ∈ actual.existingObjects) &&
    !allocatedIn actual.activation actual.scope srcInst)) &&
  (references summary).all (referenceValid actual frozen)

inductive Error where
  | invalidEntryOrSubstitution
  | invalidEntryGraph (error : CoreEntry.Error)
  deriving Repr, DecidableEq

def check (actual : CallInstance) (frozen : CoreEntry.Frozen) (summary : Template) : Except Error Summary :=
  if valid actual frozen summary then .ok (instantiate actual summary) else .error .invalidEntryOrSubstitution

def checkAtEntry (actual : CallInstance) (heapAtEntry : List HeapEdge)
    (arguments : List (Nat × List SourceInstance)) (summary : Template) : Except Error Summary :=
  match CoreEntry.capturePrepared heapAtEntry arguments with
  | .error error => .error (.invalidEntryGraph error)
  | .ok frozen => check actual frozen summary

structure InputFacts (actual : CallInstance) (frozen : CoreEntry.Frozen) (summary : Template) : Prop where
  uniqueFormals : (frozen.snapshots.map CoreEntry.Snapshot.formal).Nodup
  allocationSerials : distinctAllocationSerials summary = true
  entries : ∀ entry ∈ frozen.snapshots, ∀ srcInst ∈ entry.srcInsts,
    srcInst.object ∈ actual.existingObjects ∧ allocatedIn actual.activation actual.scope srcInst = false
  references : ∀ reference ∈ CoreSummary.references summary, referenceValid actual frozen reference = true

theorem checked_valid (h : check actual frozen summary = .ok result) :
    valid actual frozen summary = true ∧ result = instantiate actual summary := by
  unfold check at h
  split at h
  · rename_i hv; cases h; exact ⟨hv, rfl⟩
  · contradiction

theorem checked_facts (h : check actual frozen summary = .ok result) : InputFacts actual frozen summary := by
  have hv := (checked_valid h).1
  simp only [valid, Bool.and_eq_true, decide_eq_true_eq] at hv
  refine ⟨hv.1.1.1, hv.1.1.2, ?_, List.all_eq_true.mp hv.2⟩
  intro entry he srcInst ho
  have hh := List.all_eq_true.mp (List.all_eq_true.mp hv.1.2 entry he) srcInst ho
  simpa only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] using hh

theorem all_components_instantiated :
    srcInsts (instantiate actual summary) = (references summary).map (resolve actual) := by
  simp only [srcInsts, instantiate, references, SummaryOf.references, SummaryOf.map, List.map_append]

theorem every_concrete_identity_survives (he : Reference.concrete srcInst ∈ references summary) :
    srcInst ∈ srcInsts (instantiate actual summary) := by
  rw [all_components_instantiated]
  exact List.mem_map.mpr ⟨.concrete srcInst, he, rfl⟩

theorem checked_parameter_uses_frozen_entry
    (h : check actual frozen summary = .ok result)
    (hr : Reference.parameter formal selection ∈ references summary) :
    ∃ entry ∈ frozen.snapshots, entry.formal = formal ∧ actual.parameter formal selection ∈ entry.srcInsts := by
  have hp := (checked_facts h).references _ hr
  have hh : frozen.snapshots.any (fun entry => decide (entry.formal = formal ∧ actual.parameter formal selection ∈ entry.srcInsts)) = true ∧
      (!allocatedIn actual.activation actual.scope (actual.parameter formal selection)) = true := by
    simpa only [referenceValid, Bool.and_eq_true] using hp
  simpa only [List.any_eq_true, decide_eq_true_eq] using hh.1

theorem checked_at_entry_parameter_is_reachable
    (h : checkAtEntry actual heap arguments summary = .ok result)
    (hr : Reference.parameter formal selection ∈ references summary) :
    ∃ savedRoots, (formal, savedRoots) ∈ arguments ∧
      ∃ root ∈ savedRoots, Identity.Reach heap root.object (actual.parameter formal selection).object := by
  cases hc : CoreEntry.capturePrepared heap arguments with
  | error error => simp [checkAtEntry, hc] at h
  | ok frozen =>
    have hs : check actual frozen summary = .ok result := by simpa [checkAtEntry, hc] using h
    obtain ⟨entry, he, hf, ho⟩ := checked_parameter_uses_frozen_entry hs hr
    have path := (CoreEntry.snapshot_instances he ho).2
    obtain ⟨⟨name, savedRoots⟩, ha, heq⟩ := List.mem_map.mp he
    cases heq
    change name = formal at hf
    cases hf
    have boundary := CoreEntry.captured_boundary hc
    exact ⟨savedRoots, by simpa [boundary.2] using ha, by simpa [boundary.1] using path⟩

theorem allocated_instance_excludes_existing (ho : object ∈ actual.existingObjects) :
    (resolve actual (.allocated source serial)).object ≠ object ∧ (resolve actual (.allocated source serial)).source = source := by
  have hb := below_allocation_bound ho
  simp only [resolve, allocatedObject]
  exact ⟨by omega, trivial⟩

theorem checked_allocated_instance_excludes_frozen_entry
    (h : check actual frozen summary = .ok result) (he : entry ∈ frozen.snapshots) (ho : srcInst ∈ entry.srcInsts) :
    (resolve actual (.allocated source serial)).object ≠ srcInst.object :=
  (allocated_instance_excludes_existing ((checked_facts h).entries entry he srcInst ho).1).1

theorem checked_existing_instance_is_not_callee_local
    (h : check actual frozen summary = .ok result) (hr : reference ∈ references summary)
    (hn : ∀ source serial, reference ≠ .allocated source serial) :
    allocatedIn actual.activation actual.scope (resolve actual reference) = false := by
  have hp := (checked_facts h).references _ hr
  cases reference with
  | allocated source serial => exact False.elim (hn source serial rfl)
  | concrete srcInst =>
    have hh : srcInst.object ∈ actual.existingObjects ∧ allocatedIn actual.activation actual.scope srcInst = false := by
      simpa only [referenceValid, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] using hp
    exact hh.2
  | parameter formal selection =>
    have hh : frozen.snapshots.any (fun entry => decide (entry.formal = formal ∧ actual.parameter formal selection ∈ entry.srcInsts)) = true ∧
        allocatedIn actual.activation actual.scope (actual.parameter formal selection) = false := by
      simpa only [referenceValid, Bool.and_eq_true, Bool.not_eq_true'] using hp
    exact hh.2

theorem checked_distinct_allocated_objects
    (h : check actual frozen summary = .ok result)
    (hl : Reference.allocated leftSource leftSerial ∈ references summary)
    (hr : Reference.allocated rightSource rightSerial ∈ references summary)
    (hne : (leftSource, leftSerial) ≠ (rightSource, rightSerial)) :
    (resolve actual (.allocated leftSource leftSerial)).object ≠
      (resolve actual (.allocated rightSource rightSerial)).object := by
  have leftMem : (leftSource, leftSerial) ∈ allocatedReferences summary :=
    List.mem_eraseDups.mpr (List.mem_filterMap.mpr ⟨.allocated leftSource leftSerial, hl, rfl⟩)
  have rightMem : (rightSource, rightSerial) ∈ allocatedReferences summary :=
    List.mem_eraseDups.mpr (List.mem_filterMap.mpr ⟨.allocated rightSource rightSerial, hr, rfl⟩)
  have hp := List.all_eq_true.mp (List.all_eq_true.mp (checked_facts h).allocationSerials _ leftMem) _ rightMem
  have serials : leftSerial ≠ rightSerial := (of_decide_eq_true hp).resolve_left hne
  intro equalObjects
  exact serials (allocated_object_injective equalObjects)

def Reference.isPure (pureSources : List Source) : Reference → Bool
  | .concrete srcInst => isPureInstance pureSources srcInst
  | .parameter _ _ | .allocated _ _ => false

theorem reference_pure_resolves_pure {pureSources : List Source} {r : Reference}
    (h : Reference.isPure pureSources r = true) (call : CallInstance) :
    isPureInstance pureSources (resolve call r) = true := by
  cases r <;> simp_all [Reference.isPure, resolve]

def Template.subsumes (pureSources : List Source) (expected actual : Template) : Bool :=
  SummaryOf.subsumesBy (Reference.isPure pureSources) expected actual

theorem template_subsumes_instantiate {pureSources : List Source} {expected actual : Template}
    (h : expected.subsumes pureSources actual = true) (call : CallInstance) :
    (instantiate call expected).subsumes pureSources (instantiate call actual) = true := by
  simp only [Template.subsumes, SummaryOf.subsumesBy, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨heff, hroot⟩, hcont⟩, hret⟩, hwr⟩, hreads⟩, henv⟩
  rw [summary_subsumes_iff]
  refine ⟨heff, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro o ho
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ho
    exact List.mem_map_of_mem (hroot r hr)
  · intro o ho
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ho
    exact List.mem_map_of_mem (hcont r hr)
  · intro o ho
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ho
    exact List.mem_map_of_mem (hret r hr)
  · intro o ho
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ho
    rcases hwr r hr with hw | hr'
    · exact Or.inl (List.mem_map_of_mem hw)
    · exact Or.inr (List.mem_map_of_mem hr')
  · intro o ho
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ho
    rcases hreads r hr with hp | hn | hw | hr'
    · exact Or.inl (reference_pure_resolves_pure hp call)
    · exact Or.inr (Or.inl (List.mem_map_of_mem hn))
    · exact Or.inr (Or.inr (Or.inl (List.mem_map_of_mem hw)))
    · exact Or.inr (Or.inr (Or.inr (List.mem_map_of_mem hr')))
  · intro o ho
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ho
    rcases henv r hr with hp | hc
    · exact Or.inl (reference_pure_resolves_pure hp call)
    · exact Or.inr (List.mem_map_of_mem hc)

end RilAccess.CoreSummary
