import RilAccess.Model
import RilAccess.Solver

namespace RilAccess.Heap

inductive Reaches (heap : List (HeapLink Node)) (roots : List Node) : Node → Prop where
  | root : object ∈ roots → Reaches heap roots object
  | edge : edge ∈ heap → Reaches heap roots edge.parent → Reaches heap roots edge.child

def rules (edges : List (HeapLink Node)) (roots : List Node) : List (Rule Node) :=
  roots.map (Rule.mk []) ++ edges.map (fun edge => ⟨[edge.parent], edge.child⟩)

def reachable [DecidableEq Node] (edges : List (HeapLink Node)) (roots : List Node) : List Node :=
  solve (rules edges roots)

theorem reachable_exact {Node : Type} [DecidableEq Node] {heap : List (HeapLink Node)}
    {roots : List Node} {object : Node} :
    object ∈ reachable heap roots ↔ Reaches heap roots object := by
  rw [reachable, solve_exact]
  constructor
  · intro h
    induction h with
    | rule rule hr _ ih =>
      rcases List.mem_append.mp hr with hs | hs
      · obtain ⟨root, member, rfl⟩ := List.mem_map.mp hs
        exact .root member
      · obtain ⟨edge, member, rfl⟩ := List.mem_map.mp hs
        exact .edge member (ih edge.parent (by simp))
  · intro h
    induction h with
    | root hr =>
      exact .rule ⟨[], _⟩ (List.mem_append_left _ (List.mem_map.mpr ⟨_, hr, rfl⟩)) (by simp)
    | @edge edge hl _ ih =>
      apply Derives.rule ⟨[edge.parent], edge.child⟩
        (List.mem_append_right _ (List.mem_map.mpr ⟨edge, hl, rfl⟩))
      intro value h
      exact (List.mem_singleton.mp h).symm ▸ ih

theorem Reaches.map (f : α → β) (walk : Reaches heap roots object) :
    Reaches (heap.map (HeapLink.map f)) (roots.map f) (f object) := by
  induction walk with
  | root member => exact .root (List.mem_map_of_mem member)
  | @edge edge member _ ih => exact .edge (edge := edge.map f) (List.mem_map_of_mem member) ih

def separated [DecidableEq Node] (edges : List (HeapLink Node)) (left right : List Node) : Bool :=
  (reachable edges left).all (fun object => !(reachable edges right).contains object)

theorem separated_sound {Node : Type} [DecidableEq Node] {heap : List (HeapLink Node)}
    {left right : List Node} {object : Node}
    (h : separated heap left right = true)
    (hl : Reaches heap left object) (hr : Reaches heap right object) : False := by
  have test := List.all_eq_true.mp h _ (reachable_exact.mpr hl)
  have other := reachable_exact.mpr hr
  simp [other] at test

end RilAccess.Heap
