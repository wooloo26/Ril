import RilAccess.Graph.Authority

/-! Frozen, concrete call-entry sources and checked summary substitution. Entry
membership is computed from actual roots/edges, not a caller-supplied source tag.
The external existing-object list remains a separately stated coverage contract. -/
namespace RilAccess.CoreEntry

def graph (heap : List HeapEdge) (roots : List Origin) : GraphAuthority.Graph Origin :=
  ⟨roots.map (fun origin => ⟨0, origin, .ref⟩),
    heap.map (fun edge => ⟨edge.parent, edge.field, edge.child, ⟨false, .ref⟩, .ref⟩)⟩

structure Snapshot where
  formal : Nat
  origins : List Origin
  deriving Repr, DecidableEq

def capture (formal : Nat) (heap : List HeapEdge) (roots : List Origin) : Snapshot :=
  ⟨formal, ((GraphAuthority.analyze (graph heap roots)).map GraphAuthority.Fact.object).eraseDups⟩

def capturePrepared (heap : List HeapEdge) (arguments : List (Nat × List Origin)) : List Snapshot :=
  arguments.map (fun (formal, savedRoots) => capture formal heap savedRoots)

theorem finite_entry_path (h : Reach heap root target) :
    ∃ fields, GraphAuthority.Path (graph heap roots).edges root .ref fields target .ref := by
  induction h with
  | refl => exact ⟨[], .here⟩
  | @cons edge target he _ ih =>
    obtain ⟨fields, hp⟩ := ih
    exact ⟨edge.field :: fields, .next (List.mem_map.mpr ⟨edge, he, rfl⟩) hp⟩

theorem every_entry_origin_captured (hr : root ∈ roots) (hp : Reach heap root target) :
    target ∈ (capture formal heap roots).origins := by
  obtain ⟨fields, path⟩ := finite_entry_path (roots := roots) hp
  have rootPresent : GraphAuthority.Root.mk 0 root .ref ∈ (graph heap roots).roots :=
    List.mem_map.mpr ⟨root, hr, rfl⟩
  apply List.mem_eraseDups.mpr
  exact List.mem_map.mpr ⟨⟨0, target, .ref⟩, GraphAuthority.path_covered rootPresent path, rfl⟩

theorem captured_origin_has_entry_path (ht : target ∈ (capture formal heap roots).origins) :
    ∃ root ∈ roots, Reach heap root target := by
  obtain ⟨fact, hf, heq⟩ := List.mem_map.mp (List.mem_eraseDups.mp ht)
  have hg := GraphAuthority.analyze_grounded hf
  have statement : ∀ fact, GraphAuthority.Granted (graph heap roots) fact →
      ∃ root ∈ roots, Reach heap root fact.object := by
    intro fact granted
    induction granted with
    | @root selected hr =>
      obtain ⟨origin, ho, he⟩ := List.mem_map.mp hr
      have hx : origin = selected.object := congrArg GraphAuthority.Root.object he
      refine ⟨origin, ho, ?_⟩
      rw [← hx]
      exact .refl
    | @edge root edge mode hr hedge _ ih =>
      obtain ⟨original, ho, he⟩ := List.mem_map.mp hedge
      cases he
      obtain ⟨start, hs, hp⟩ := ih
      have appendEdge : ∀ a b, Reach heap a b → ∀ edge ∈ heap, edge.parent = b → Reach heap a edge.child := by
        intro a b path
        induction path with
        | refl => intro edge hm he; cases he; exact .cons hm .refl
        | cons hm _ ih => intro edge heq hp; exact .cons hm (ih edge heq hp)
      exact ⟨start, hs, appendEdge _ _ hp original ho rfl⟩
  simpa only [heq] using statement fact hg

theorem entry_capture_exact : target ∈ (capture formal heap roots).origins ↔
    ∃ root ∈ roots, Reach heap root target :=
  ⟨captured_origin_has_entry_path, fun ⟨_, hr, hp⟩ => every_entry_origin_captured hr hp⟩

/-- Compare complete reachable regions by allocation identity, including when
two paths describe an object with different provenance metadata. -/
def separated (heap : List HeapEdge) (left right : List Origin) : Bool :=
  disjointUnknownSelections ((capture 0 heap left).origins.map Origin.object)
    ((capture 0 heap right).origins.map Origin.object)

theorem separated_paths_cannot_alias
    (hs : separated heap left right = true)
    (hl : leftRoot ∈ left) (pl : Reach heap leftRoot leftTarget)
    (hr : rightRoot ∈ right) (pr : Reach heap rightRoot rightTarget) :
    leftTarget.object ≠ rightTarget.object := by
  have noCommon := disjoint_check_sound hs
  have lm : leftTarget.object ∈ (capture 0 heap left).origins.map Origin.object :=
    List.mem_map.mpr ⟨leftTarget, every_entry_origin_captured hl pl, rfl⟩
  have rm : rightTarget.object ∈ (capture 0 heap right).origins.map Origin.object :=
    List.mem_map.mpr ⟨rightTarget, every_entry_origin_captured hr pr, rfl⟩
  intro heq
  exact noCommon _ lm (heq.symm ▸ rm)

end RilAccess.CoreEntry
