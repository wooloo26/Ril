import RilAccess.Graph.Reachability

/-! Physical reachability uses object IDs. Source labels are explanations and
must not split a physical object into distinct graph nodes. -/
namespace RilAccess.Identity

abbrev ObjectId := Nat

/-- Tree regions retain their coordinate; they are not flattened to allocation IDs. -/
abbrev RegionKey := ObjectId × List Nat

def allocationContext (srcInst : SourceInstance) : Nat × Nat :=
  (srcInst.activation, srcInst.scope)

def coherent (srcInsts : List SourceInstance) : Bool :=
  srcInsts.all fun left => srcInsts.all fun right =>
    decide (left.object ≠ right.object ∨ allocationContext left = allocationContext right)

def labels (heap : List HeapEdge) (roots : List SourceInstance) : List SourceInstance :=
  (roots ++ heap.flatMap (fun edge => [edge.parent, edge.child])).eraseDups

inductive Reach (heap : List HeapEdge) : ObjectId → ObjectId → Prop where
  | refl : Reach heap object object
  | cons : edge ∈ heap → Reach heap edge.child.object target → Reach heap edge.parent.object target

def objects (heap : List HeapEdge) (roots : List SourceInstance) : List ObjectId :=
  Heap.reachable (heap.map (HeapLink.map SourceInstance.object)) (roots.map SourceInstance.object)

def srcInsts (heap : List HeapEdge) (allRoots roots : List SourceInstance) : List SourceInstance :=
  (labels heap allRoots).filter (fun srcInst => decide (srcInst.object ∈ objects heap roots))

theorem same_context {knownInstances : List SourceInstance} (h : coherent knownInstances = true) (hl : left ∈ knownInstances)
    (hr : right ∈ knownInstances) (hi : left.object = right.object) : allocationContext left = allocationContext right := by
  have pair := List.all_eq_true.mp (List.all_eq_true.mp h left hl) right hr
  exact (of_decide_eq_true pair).resolve_left (not_not_intro hi)

theorem Reach.append (path : Reach heap root edge.parent.object) (present : edge ∈ heap) :
    Reach heap root edge.child.object := by
  generalize endpoint : edge.parent.object = target at path
  induction path with
  | refl =>
    rw [← endpoint]
    exact .cons present .refl
  | cons member _ ih =>
    exact .cons member (ih endpoint)

theorem Reach.extend (path : Reach heap root target)
    (base : Heap.Reaches (heap.map (HeapLink.map SourceInstance.object)) roots root) :
    Heap.Reaches (heap.map (HeapLink.map SourceInstance.object)) roots target := by
  induction path with
  | refl => exact base
  | @cons edge _ present _ ih =>
    exact ih (.edge (edge := edge.map SourceInstance.object) (List.mem_map_of_mem present) base)

theorem path_covered (hr : root ∈ roots) (hp : Reach heap root.object target) :
    target ∈ objects heap roots :=
  Heap.reachable_exact.mpr (hp.extend (.root (List.mem_map_of_mem hr)))

theorem object_has_path (ht : target ∈ objects heap roots) :
    ∃ root ∈ roots, Reach heap root.object target := by
  have walk := Heap.reachable_exact.mp ht
  clear ht
  induction walk with
  | root found =>
    obtain ⟨root, member, rfl⟩ := List.mem_map.mp found
    exact ⟨root, member, .refl⟩
  | edge present _ ih =>
    obtain ⟨edge, member, rfl⟩ := List.mem_map.mp present
    obtain ⟨root, initial, path⟩ := ih
    exact ⟨root, initial, path.append member⟩

theorem objects_exact : target ∈ objects heap roots ↔ ∃ root ∈ roots, Reach heap root.object target :=
  ⟨object_has_path, fun ⟨_, hr, hp⟩ => path_covered hr hp⟩

theorem instances_exact : srcInst ∈ srcInsts heap allRoots roots ↔
    srcInst ∈ labels heap allRoots ∧ ∃ root ∈ roots, Reach heap root.object srcInst.object := by
  simp only [srcInsts, List.mem_filter, decide_eq_true_eq, objects_exact]

/-- A caller still has to establish that this finite graph covers its actual
heap/roots. This predicate is a theorem premise, not an axiom or a safety flag. -/
def Represents (heap : List HeapEdge) (roots : List SourceInstance)
    (actualReach : ObjectId → ObjectId → Prop) : Prop :=
  ∀ root ∈ roots, ∀ target, actualReach root.object target → Reach heap root.object target

end RilAccess.Identity
