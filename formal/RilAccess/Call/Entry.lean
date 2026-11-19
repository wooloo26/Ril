import RilAccess.Graph.Identity
import RilAccess.Signatures

namespace RilAccess.CoreEntry

inductive Error where
  | conflictingContexts
  deriving Repr, DecidableEq

/-- One physical heap and one preparation boundary for every formal. No
arbitrary list of inferred sources can be supplied in place of this snapshot. -/
structure Frozen where
  heap : List HeapEdge
  arguments : List (Nat × List SourceInstance)
  consistent : Identity.coherent (Identity.labels heap (arguments.flatMap Prod.snd)) = true

structure Snapshot where
  formal : Nat
  roots : List SourceInstance
  objects : List Nat
  srcInsts : List SourceInstance
  deriving Repr, DecidableEq

def Frozen.snapshots (frozen : Frozen) : List Snapshot :=
  frozen.arguments.map fun (formal, roots) =>
    ⟨formal, roots, Identity.objects frozen.heap roots,
      Identity.srcInsts frozen.heap (frozen.arguments.flatMap Prod.snd) roots⟩

def capturePrepared (heap : List HeapEdge) (arguments : List (Nat × List SourceInstance)) : Except Error Frozen :=
  if h : Identity.coherent (Identity.labels heap (arguments.flatMap Prod.snd)) then
    .ok ⟨heap, arguments, h⟩
  else .error .conflictingContexts

variable {frozen : Frozen} {entry : Snapshot} {srcInst : SourceInstance} {object : Nat}

theorem captured_boundary (h : capturePrepared heap arguments = .ok frozen) :
    frozen.heap = heap ∧ frozen.arguments = arguments := by
  unfold capturePrepared at h
  split at h
  · cases h; exact ⟨rfl, rfl⟩
  · contradiction

theorem snapshot_instances (he : entry ∈ frozen.snapshots) (ho : srcInst ∈ entry.srcInsts) :
    srcInst ∈ Identity.labels frozen.heap (frozen.arguments.flatMap Prod.snd) ∧
      ∃ root ∈ entry.roots, Identity.Reach frozen.heap root.object srcInst.object := by
  obtain ⟨⟨formal, roots⟩, _, rfl⟩ := List.mem_map.mp he
  exact Identity.instances_exact.mp ho

theorem snapshot_objects (he : entry ∈ frozen.snapshots) :
    object ∈ entry.objects ↔ ∃ root ∈ entry.roots, Identity.Reach frozen.heap root.object object := by
  obtain ⟨⟨formal, roots⟩, _, rfl⟩ := List.mem_map.mp he
  exact Identity.objects_exact

theorem snapshot_sources_complete (he : entry ∈ frozen.snapshots)
    (hk : srcInst ∈ Identity.labels frozen.heap (frozen.arguments.flatMap Prod.snd))
    (hp : ∃ root ∈ entry.roots, Identity.Reach frozen.heap root.object srcInst.object) :
    srcInst ∈ entry.srcInsts := by
  obtain ⟨⟨formal, roots⟩, _, rfl⟩ := List.mem_map.mp he
  exact Identity.instances_exact.mpr ⟨hk, hp⟩

/-- False means separation has not been proved, including invalid allocation-context
metadata. Different source labels never disconnect physical edges. -/
def separated (heap : List HeapEdge) (left right : List SourceInstance) : Bool :=
  Identity.coherent (Identity.labels heap (left ++ right)) &&
    disjointUnknownSelections (Identity.objects heap left) (Identity.objects heap right)

theorem separated_paths_cannot_alias (hs : separated heap left right = true)
    (hl : leftRoot ∈ left) (pl : Identity.Reach heap leftRoot.object leftTarget)
    (hr : rightRoot ∈ right) (pr : Identity.Reach heap rightRoot.object rightTarget) :
    leftTarget ≠ rightTarget := by
  have hparts : Identity.coherent (Identity.labels heap (left ++ right)) = true ∧
      disjointUnknownSelections (Identity.objects heap left) (Identity.objects heap right) = true := by
    simpa only [separated, Bool.and_eq_true] using hs
  have noCommon := disjoint_check_sound hparts.2
  intro equal
  exact noCommon _ (Identity.path_covered hl pl) (equal.symm ▸ Identity.path_covered hr pr)

end RilAccess.CoreEntry
