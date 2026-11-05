import RilAccess.Graph.Identity

namespace RilAccess.CoreEntry

inductive Error where
  | conflictingOwners
  deriving Repr, DecidableEq

/-- One physical heap and one preparation boundary for every formal. No
arbitrary list of inferred sources can be supplied in place of this snapshot. -/
structure Frozen where
  heap : List HeapEdge
  arguments : List (Nat × List Origin)
  consistent : Identity.coherent (Identity.labels heap (arguments.flatMap Prod.snd)) = true

structure Snapshot where
  formal : Nat
  roots : List Origin
  objects : List Nat
  origins : List Origin
  deriving Repr, DecidableEq

def Frozen.snapshots (frozen : Frozen) : List Snapshot :=
  frozen.arguments.map fun (formal, roots) =>
    ⟨formal, roots, Identity.objects frozen.heap roots,
      Identity.origins frozen.heap (frozen.arguments.flatMap Prod.snd) roots⟩

def capturePrepared (heap : List HeapEdge) (arguments : List (Nat × List Origin)) : Except Error Frozen :=
  if h : Identity.coherent (Identity.labels heap (arguments.flatMap Prod.snd)) then
    .ok ⟨heap, arguments, h⟩
  else .error .conflictingOwners

variable {frozen : Frozen} {entry : Snapshot} {origin : Origin} {object : Nat}

theorem captured_boundary (h : capturePrepared heap arguments = .ok frozen) :
    frozen.heap = heap ∧ frozen.arguments = arguments := by
  unfold capturePrepared at h
  split at h
  · cases h; exact ⟨rfl, rfl⟩
  · contradiction

theorem snapshot_origins (he : entry ∈ frozen.snapshots) (ho : origin ∈ entry.origins) :
    origin ∈ Identity.labels frozen.heap (frozen.arguments.flatMap Prod.snd) ∧
      ∃ root ∈ entry.roots, Identity.Reach frozen.heap root.object origin.object := by
  obtain ⟨⟨formal, roots⟩, _, rfl⟩ := List.mem_map.mp he
  exact Identity.origins_exact.mp ho

theorem snapshot_objects (he : entry ∈ frozen.snapshots) :
    object ∈ entry.objects ↔ ∃ root ∈ entry.roots, Identity.Reach frozen.heap root.object object := by
  obtain ⟨⟨formal, roots⟩, _, rfl⟩ := List.mem_map.mp he
  exact Identity.objects_exact

theorem snapshot_sources_complete (he : entry ∈ frozen.snapshots)
    (hk : origin ∈ Identity.labels frozen.heap (frozen.arguments.flatMap Prod.snd))
    (hp : ∃ root ∈ entry.roots, Identity.Reach frozen.heap root.object origin.object) :
    origin ∈ entry.origins := by
  obtain ⟨⟨formal, roots⟩, _, rfl⟩ := List.mem_map.mp he
  exact Identity.origins_exact.mpr ⟨hk, hp⟩

/-- False means separation has not been proved, including invalid ownership
metadata. Different source labels never disconnect physical edges. -/
def separated (heap : List HeapEdge) (left right : List Origin) : Bool :=
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
