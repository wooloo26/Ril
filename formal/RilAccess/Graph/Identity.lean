import RilAccess.Graph.Authority

/-! Physical reachability uses object IDs. Source labels are explanations and
must not split a physical object into distinct graph nodes. -/
namespace RilAccess.Identity

abbrev ObjectId := Nat

/-- Tree regions retain their coordinate; they are not flattened to allocation IDs. -/
abbrev RegionKey := ObjectId × List Nat

def owner (origin : Origin) : Nat × Nat × Nat :=
  (origin.activation, origin.task, origin.scope)

def coherent (origins : List Origin) : Bool :=
  origins.all fun left => origins.all fun right =>
    decide (left.object ≠ right.object ∨ owner left = owner right)

def labels (heap : List HeapEdge) (roots : List Origin) : List Origin :=
  (roots ++ heap.flatMap (fun edge => [edge.parent, edge.child])).eraseDups

def graph (heap : List HeapEdge) (roots : List Origin) : GraphAuthority.Graph ObjectId :=
  ⟨roots.map (fun origin => ⟨0, origin.object, .ref⟩),
    heap.map (fun edge => ⟨edge.parent.object, edge.field, edge.child.object, ⟨false, .ref⟩, .ref⟩)⟩

inductive Reach (heap : List HeapEdge) : ObjectId → ObjectId → Prop where
  | refl : Reach heap object object
  | cons : edge ∈ heap → Reach heap edge.child.object target → Reach heap edge.parent.object target

def objects (heap : List HeapEdge) (roots : List Origin) : List ObjectId :=
  ((GraphAuthority.analyze (graph heap roots)).map GraphAuthority.Fact.object).eraseDups

def origins (heap : List HeapEdge) (allRoots roots : List Origin) : List Origin :=
  (labels heap allRoots).filter (fun origin => decide (origin.object ∈ objects heap roots))

theorem same_owner {knownOrigins : List Origin} (h : coherent knownOrigins = true) (hl : left ∈ knownOrigins)
    (hr : right ∈ knownOrigins) (hi : left.object = right.object) : owner left = owner right := by
  have pair := List.all_eq_true.mp (List.all_eq_true.mp h left hl) right hr
  exact (of_decide_eq_true pair).resolve_left (not_not_intro hi)

theorem source_reach (h : RilAccess.Reach heap root target) : Reach heap root.object target.object := by
  induction h with
  | refl => exact .refl
  | cons he _ ih => exact .cons he ih

theorem finite_path (h : Reach heap root target) :
    ∃ fields, GraphAuthority.Path (graph heap roots).edges root .ref fields target .ref := by
  induction h with
  | refl => exact ⟨[], .here⟩
  | @cons edge target he _ ih =>
    obtain ⟨fields, hp⟩ := ih
    exact ⟨edge.field :: fields, .next (List.mem_map.mpr ⟨edge, he, rfl⟩) hp⟩

theorem path_covered (hr : root ∈ roots) (hp : Reach heap root.object target) :
    target ∈ objects heap roots := by
  obtain ⟨fields, path⟩ := finite_path (roots := roots) hp
  have rootPresent : GraphAuthority.Root.mk 0 root.object .ref ∈ (graph heap roots).roots :=
    List.mem_map.mpr ⟨root, hr, rfl⟩
  apply List.mem_eraseDups.mpr
  exact List.mem_map.mpr ⟨⟨0, target, .ref⟩, GraphAuthority.path_covered rootPresent path, rfl⟩

theorem object_has_path (ht : target ∈ objects heap roots) :
    ∃ root ∈ roots, Reach heap root.object target := by
  obtain ⟨fact, hf, heq⟩ := List.mem_map.mp (List.mem_eraseDups.mp ht)
  have statement : ∀ fact, GraphAuthority.Granted (graph heap roots) fact →
      ∃ root ∈ roots, Reach heap root.object fact.object := by
    intro fact granted
    induction granted with
    | @root selected hr =>
      obtain ⟨origin, ho, he⟩ := List.mem_map.mp hr
      have hx : origin.object = selected.object := congrArg GraphAuthority.Root.object he
      refine ⟨origin, ho, ?_⟩
      rw [← hx]
      exact .refl
    | @edge root edge mode _ hedge _ ih =>
      obtain ⟨original, ho, he⟩ := List.mem_map.mp hedge
      cases he
      obtain ⟨start, hs, hp⟩ := ih
      have appendEdge : ∀ a b, Reach heap a b → ∀ edge ∈ heap, edge.parent.object = b →
          Reach heap a edge.child.object := by
        intro a b path
        induction path with
        | refl => intro edge hm he; cases he; exact .cons hm .refl
        | cons hm _ ih => intro edge heq hp; exact .cons hm (ih edge heq hp)
      exact ⟨start, hs, appendEdge _ _ hp original ho rfl⟩
  simpa only [heq] using statement fact (GraphAuthority.analyze_grounded hf)

theorem objects_exact : target ∈ objects heap roots ↔ ∃ root ∈ roots, Reach heap root.object target :=
  ⟨object_has_path, fun ⟨_, hr, hp⟩ => path_covered hr hp⟩

theorem origins_exact : origin ∈ origins heap allRoots roots ↔
    origin ∈ labels heap allRoots ∧ ∃ root ∈ roots, Reach heap root.object origin.object := by
  simp only [origins, List.mem_filter, decide_eq_true_eq, objects_exact]

/-- A caller still has to establish that this finite graph covers its actual
heap/roots. This predicate is a theorem premise, not an axiom or a safety flag. -/
def Represents (heap : List HeapEdge) (roots : List Origin)
    (actualReach : ObjectId → ObjectId → Prop) : Prop :=
  ∀ root ∈ roots, ∀ target, actualReach root.object target → Reach heap root.object target

end RilAccess.Identity
