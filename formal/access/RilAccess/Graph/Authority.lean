import RilAccess.Contracts

/-! Finite authority closure for shared, cyclic, mutable graphs. The closure is
for summaries: permission to use one path is checked on that particular path,
never inferred from another writable path to the same object. -/
namespace RilAccess.GraphAuthority

variable {Node : Type} [DecidableEq Node]

@[simp] theorem option_bind_some (value : α) (f : α → Option β) :
    (some value >>= f) = f value := rfl
@[simp] theorem option_bind_none (f : α → Option β) : (none >>= f) = none := rfl

def modes : List Access := [.immutable, .ref, .mut, .shared]

theorem mode_mem (mode : Access) : mode ∈ modes := by cases mode <;> simp [modes]

structure Root (Node : Type := Nat) where
  view : Nat
  object : Node
  access : Access
  deriving Repr, DecidableEq

structure Edge (Node : Type := Nat) where
  parent : Node
  field : Nat
  child : Node
  member : MemberMode
  held : Access
  deriving Repr, DecidableEq

structure RawEdge (Node : Type := Nat) where
  parent : Node
  field : Nat
  child : Node
  deriving Repr, DecidableEq

def eraseEdge (edge : Edge Node) : RawEdge Node := ⟨edge.parent, edge.field, edge.child⟩

def eraseEdges (edges : List (Edge Node)) : List (RawEdge Node) := edges.map eraseEdge

def traverseEdge (access : Access) (edge : Edge Node) : Access :=
  attenuate (attenuate access edge.member.access) edge.held

structure Fact (Node : Type := Nat) where
  view : Nat
  object : Node
  access : Access
  deriving Repr, DecidableEq

structure Graph (Node : Type := Nat) where
  roots : List (Root Node)
  edges : List (Edge Node)
  deriving Repr, DecidableEq

def rules (graph : Graph Node) : List (Rule (Fact Node)) :=
  (graph.roots.map fun root => ⟨[], ⟨root.view, root.object, root.access⟩⟩) ++
    graph.edges.flatMap fun edge => graph.roots.flatMap fun root => modes.map fun mode =>
      ⟨[⟨root.view, edge.parent, mode⟩], ⟨root.view, edge.child, traverseEdge mode edge⟩⟩

def analyze (graph : Graph Node) : List (Fact Node) := solve (rules graph)

inductive Granted (graph : Graph Node) : Fact Node → Prop where
  | root : root ∈ graph.roots → Granted graph ⟨root.view, root.object, root.access⟩
  | edge : root ∈ graph.roots → edge ∈ graph.edges → Granted graph ⟨root.view, edge.parent, mode⟩ →
      Granted graph ⟨root.view, edge.child, traverseEdge mode edge⟩

variable {graph : Graph Node} {root : Root Node} {edge : Edge Node} {fact : Fact Node}
  {edges : List (Edge Node)}

omit [DecidableEq Node] in
theorem root_rule (hr : root ∈ graph.roots) :
    Rule.mk [] ⟨root.view, root.object, root.access⟩ ∈ rules graph :=
  List.mem_append_left _ (List.mem_map.mpr ⟨root, hr, rfl⟩)

omit [DecidableEq Node] in
theorem edge_rule (hr : root ∈ graph.roots) (he : edge ∈ graph.edges) :
    Rule.mk [⟨root.view, edge.parent, mode⟩] ⟨root.view, edge.child, traverseEdge mode edge⟩ ∈
      rules graph := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨edge, he, List.mem_flatMap.mpr ⟨root, hr, ?_⟩⟩
  exact List.mem_map.mpr ⟨mode, mode_mem mode, rfl⟩

theorem granted_covered (h : Granted graph fact) : fact ∈ analyze graph := by
  induction h with
  | root hr => exact solve_closed _ (root_rule hr) (by simp)
  | edge hr he _ ih =>
    apply solve_closed _ (edge_rule hr he)
    intro fact hfact
    have heq := List.mem_singleton.mp hfact
    subst fact
    exact ih

theorem analyze_grounded (h : fact ∈ analyze graph) : Granted graph fact := by
  have hd : Derives (rules graph) fact := solve_exact.mp h
  clear h
  induction hd with
  | rule rule hr _ ih =>
    rcases List.mem_append.mp hr with hseed | hedge
    · obtain ⟨root, hselected, rfl⟩ := List.mem_map.mp hseed
      exact .root hselected
    · obtain ⟨edge, he, tail⟩ := List.mem_flatMap.mp hedge
      obtain ⟨root, hroot, tail⟩ := List.mem_flatMap.mp tail
      obtain ⟨mode, _, heq⟩ := List.mem_map.mp tail
      cases heq
      exact .edge hroot he (ih _ (by simp))

theorem analyze_exact : fact ∈ analyze graph ↔ Granted graph fact :=
  ⟨analyze_grounded, granted_covered⟩

omit [DecidableEq Node] in
theorem edge_write_bound (h : (traverseEdge mode edge).writes = true) :
    mode.writes = true ∧ edge.member.access.writes = true ∧ edge.held.writes = true := by
  obtain ⟨hparent, hheld⟩ := attenuate_write h
  obtain ⟨hmode, hmember⟩ := attenuate_write hparent
  exact ⟨hmode, hmember, hheld⟩

/-- A checked path retains its actual edge sequence, including a read-only alias
that happens to target the same object as a different writable path. -/
inductive Path (edges : List (Edge Node)) : Node → Access → List Nat → Node → Access → Prop where
  | here {object : Node} {access : Access} : Path edges object access [] object access
  | next {edge : Edge Node} {access : Access} {rest : List Nat} {object : Node} {mode : Access} : edge ∈ edges → Path edges edge.child (traverseEdge access edge) rest object mode →
      Path edges edge.parent access (edge.field :: rest) object mode

/-- The erased heap path has no access modes or static authority premises. -/
inductive RawPath (edges : List (RawEdge Node)) : Node → List Nat → Node → Prop where
  | here {object : Node} : RawPath edges object [] object
  | next {edge : RawEdge Node} {rest : List Nat} {object : Node} : edge ∈ edges → RawPath edges edge.child rest object →
      RawPath edges edge.parent (edge.field :: rest) object

omit [DecidableEq Node] in
theorem path_erases (h : Path edges start access fields object mode) :
    RawPath (eraseEdges edges) start fields object := by
  induction h with
  | here => exact .here
  | @next edge access rest object mode he _ ih =>
    exact .next (List.mem_map.mpr ⟨edge, he, rfl⟩) ih

omit [DecidableEq Node] in
theorem erased_path_has_bound (h : RawPath (eraseEdges edges) start fields object) (access : Access) :
    ∃ mode, Path edges start access fields object mode := by
  induction h generalizing access with
  | here => exact ⟨access, .here⟩
  | @next rawEdge rest object he _ ih =>
    obtain ⟨edge, hedge, heq⟩ := List.mem_map.mp he
    cases heq
    obtain ⟨mode, hp⟩ := ih (traverseEdge access edge)
    exact ⟨mode, .next hedge hp⟩

omit [DecidableEq Node] in
theorem path_writable_root (h : Path edges start access fields object mode)
    (hw : mode.writes = true) : access.writes = true := by
  induction h with
  | here => exact hw
  | next _ _ ih => exact (edge_write_bound (ih hw)).1

theorem path_covered (hr : root ∈ graph.roots)
    (h : Path graph.edges root.object root.access fields object mode) :
    Fact.mk root.view object mode ∈ analyze graph := by
  have lift (start access fields object mode) (hp : Path graph.edges start access fields object mode)
      (hg : Granted graph ⟨root.view, start, access⟩) : Granted graph ⟨root.view, object, mode⟩ := by
    induction hp with
    | here => exact hg
    | next he _ ih => exact ih (.edge hr he hg)
  exact granted_covered (lift _ _ _ _ _ h (.root hr))

def resolvePath (edges : List (Edge Node)) : Node → Access → List Nat → Option (Node × Access)
  | object, access, [] => some (object, access)
  | object, access, field :: rest => do
    let edge ← edges.find? fun edge => decide (edge.parent = object ∧ edge.field = field)
    resolvePath edges edge.child (traverseEdge access edge) rest

theorem resolve_path_sound (h : resolvePath edges start access fields = some (object, mode)) :
    Path edges start access fields object mode := by
  induction fields generalizing start access with
  | nil => simp [resolvePath] at h; obtain ⟨rfl, rfl⟩ := h; exact .here
  | cons field rest ih =>
    cases hf : edges.find? (fun edge => decide (edge.parent = start ∧ edge.field = field)) with
    | none => rw [resolvePath, hf] at h; contradiction
    | some edge =>
      have he := List.mem_of_find?_eq_some hf
      have hp : edge.parent = start ∧ edge.field = field := by
        have found := List.find?_some
          (p := fun candidate : Edge Node => decide (candidate.parent = start ∧ candidate.field = field)) hf
        exact of_decide_eq_true found
      have htail : resolvePath edges edge.child (traverseEdge access edge) rest = some (object, mode) := by
        rw [resolvePath, hf] at h
        exact h
      have path := Path.next he (ih htail)
      simpa [hp.1, hp.2] using path

def canWritePath (graph : Graph Node) (view : Nat) (fields : List Nat) : Bool :=
  match graph.roots.find? (fun root => decide (root.view = view)) with
  | none => false
  | some root =>
    match resolvePath graph.edges root.object root.access fields with
    | none => false
    | some (_, mode) => mode.writes

def resolveView (graph : Graph Node) (view : Nat) (fields : List Nat) : Option (Node × Access) := do
  let root ← graph.roots.find? fun root => decide (root.view = view)
  resolvePath graph.edges root.object root.access fields

def hasWriter (graph : Graph Node) (object : Node) : Bool :=
  (analyze graph).any fun fact => decide (fact.object = object) && fact.access.writes

def hasImmutable (graph : Graph Node) (object : Node) : Bool :=
  (analyze graph).any fun fact => decide (fact.object = object ∧ fact.access = .immutable)

def immutableConsistent (graph : Graph Node) : Bool :=
  (analyze graph).all fun fact =>
    !decide (fact.access = .immutable) || !hasWriter graph fact.object

theorem immutable_has_no_writer (h : immutableConsistent graph = true)
    (hi : immutable ∈ analyze graph) (hm : immutable.access = .immutable)
    (hw : writer ∈ analyze graph) (ho : writer.object = immutable.object)
    (hwrite : writer.access.writes = true) : False := by
  have hnone := List.all_eq_true.mp h immutable hi
  have hex : hasWriter graph immutable.object = true := by
    apply List.any_eq_true.mpr
    exact ⟨writer, hw, by simp [ho, hwrite]⟩
  simp [hm, hex] at hnone

/-- A raw edge update. Typed slot replacement below preserves its schema. -/
def putEdge (graph : Graph Node) (edge : Edge Node) : Graph Node :=
  { graph with edges := (edge :: graph.edges.filter (fun old =>
      decide (old.parent ≠ edge.parent ∨ old.field ≠ edge.field))) }

theorem replacement_present : edge ∈ (putEdge graph edge).edges := by simp [putEdge]

theorem unrelated_edge_preserved (he : old ∈ graph.edges)
    (hslot : old.parent ≠ edge.parent ∨ old.field ≠ edge.field) :
    old ∈ (putEdge graph edge).edges := by
  exact List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨he, by simpa using hslot⟩)

def replaceField (graph : Graph Node) (parent : Node) (field : Nat) (child : Node) (held : Access) : Option (Graph Node) := do
  let old ← graph.edges.find? fun old => decide (old.parent = parent ∧ old.field = field)
  if old.member.replaceable then some (putEdge graph { old with child, held }) else none

theorem replacement_preserves_schema
    (h : replaceField graph parent field child held = some next) :
    ∃ old ∈ graph.edges, old.parent = parent ∧ old.field = field ∧ old.member.replaceable = true ∧
      { old with child, held } ∈ next.edges := by
  cases hf : graph.edges.find? (fun old => decide (old.parent = parent ∧ old.field = field)) with
  | none => rw [replaceField, hf] at h; contradiction
  | some old =>
    have hm := List.mem_of_find?_eq_some hf
    have hslot : old.parent = parent ∧ old.field = field := by
      exact of_decide_eq_true (List.find?_some
        (p := fun candidate : Edge Node => decide (candidate.parent = parent ∧ candidate.field = field)) hf)
    rw [replaceField, hf] at h
    change (if old.member.replaceable then some (putEdge graph { old with child, held }) else none) =
      some next at h
    split at h
    · rename_i hr
      cases h
      exact ⟨old, hm, hslot.1, hslot.2, hr, replacement_present⟩
    · contradiction

/-- Existing writable storage needs an explicit shared receiving marker. This
permission component deliberately does not assert the missing lifetime proof. -/
def receiveStored (member source : Access) (sharedMarker : Bool) : Option Access :=
  match member with
  | .immutable => if !sharedMarker && decide (source = .immutable) then some .immutable else none
  | .ref => if !sharedMarker then some .ref else none
  | .mut | .shared => if sharedMarker && source.writes then some .shared else none

def checkedReplace (graph : Graph Node) (receiver : Nat) (parentPath : List Nat)
    (field source : Nat) (sourcePath : List Nat) (sharedMarker : Bool) : Option (Graph Node) := do
  let (parent, access) ← resolveView graph receiver parentPath
  let (child, sourceMode) ← resolveView graph source sourcePath
  let old ← graph.edges.find? fun edge => decide (edge.parent = parent ∧ edge.field = field)
  let held ← receiveStored old.member.access sourceMode sharedMarker
  if access.writes && old.member.replaceable && immutableConsistent graph then
    let next := putEdge graph { old with child, held }
    if immutableConsistent next then some next else none
  else none

theorem stored_writer_has_source (h : receiveStored member source marker = some held)
    (hw : held.writes = true) : source.writes = true ∧ marker = true := by
  cases member <;> cases source <;> cases held <;> cases marker <;>
    simp_all [receiveStored, Access.writes]

theorem stored_ref_cannot_write (h : receiveStored .ref source marker = some held) :
    held.writes = false := by
  simp only [receiveStored] at h
  split at h
  · cases h; rfl
  · contradiction

theorem checked_replacement_immutable_consistent
    (h : checkedReplace graph receiver parentPath field source sourcePath marker = some next) :
    immutableConsistent next = true := by
  cases hr : resolveView graph receiver parentPath with
  | none => rw [checkedReplace, hr] at h; contradiction
  | some result =>
    obtain ⟨parent, access⟩ := result
    cases hs : resolveView graph source sourcePath with
    | none => simp only [checkedReplace, hr, hs, option_bind_some, option_bind_none] at h; contradiction
    | some incoming =>
      obtain ⟨child, sourceMode⟩ := incoming
      cases hf : graph.edges.find?
          (fun edge => decide (edge.parent = parent ∧ edge.field = field)) with
      | none => simp only [checkedReplace, hr, hs, hf, option_bind_some, option_bind_none] at h; contradiction
      | some old =>
        cases hh : receiveStored old.member.access sourceMode marker with
        | none => simp only [checkedReplace, hr, hs, hf, hh, option_bind_some, option_bind_none] at h; contradiction
        | some held =>
          simp only [checkedReplace, hr, hs, hf, hh, option_bind_some] at h
          change (if access.writes && old.member.replaceable && immutableConsistent graph then
            if immutableConsistent (putEdge graph { old with child, held }) then
              some (putEdge graph { old with child, held }) else none else none) = some next at h
          split at h
          · split at h
            · cases h; assumption
            · contradiction
          · contradiction

theorem readonly_path_never_writes
    (h : resolvePath edges start .ref fields = some (object, mode)) : mode.writes = false := by
  have hp := resolve_path_sound h
  cases hw : mode.writes with
  | false => rfl
  | true =>
    have contradiction := path_writable_root hp hw
    simp [Access.writes] at contradiction

def entryObjects (graph : Graph Node) (view : Nat) : List Node :=
  ((analyze graph).filter (fun fact => decide (fact.view = view))).map (fun fact => fact.object)

theorem entry_object_covered (hr : root ∈ graph.roots)
    (hp : Path graph.edges root.object root.access fields object mode) :
    object ∈ entryObjects graph root.view := by
  apply List.mem_map.mpr
  exact ⟨⟨root.view, object, mode⟩, List.mem_filter.mpr ⟨path_covered hr hp, by simp⟩, rfl⟩

end RilAccess.GraphAuthority
