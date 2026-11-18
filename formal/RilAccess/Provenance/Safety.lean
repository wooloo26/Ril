import RilAccess.Provenance.Verified

namespace RilAccess.Provenance

inductive Reaches (heap : List Link) (roots : List Object) : Object → Prop where
  | root : object ∈ roots → Reaches heap roots object
  | edge : edge ∈ heap → Reaches heap roots edge.parent → Reaches heap roots edge.child

theorem reachable_exact : object ∈ reachable heap roots ↔ Reaches heap roots object := by
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
      have eq := List.mem_singleton.mp h
      subst value
      exact ih

theorem Reaches.abstract (run : Reaches heap roots object) :
    Reaches (heap.map Link.abstract) (roots.map Object.abstract) object.abstract := by
  induction run with
  | root member => exact .root (List.mem_map_of_mem member)
  | @edge edge member _ ih => exact .edge (edge := edge.abstract) (List.mem_map_of_mem member) ih

theorem separated_sound (h : separated (heap.map Link.abstract)
    (left.map Object.abstract) (right.map Object.abstract) = true)
    (hl : Reaches heap left object) (hr : Reaches heap right object) : False := by
  have test := List.all_eq_true.mp h _ (reachable_exact.mpr hl.abstract)
  have other := reachable_exact.mpr hr.abstract
  simp [other] at test

theorem Object.abstract_eq_self {object : Object} (h : object.singleton = true) :
    object.abstract = object := by
  cases object with
  | mk site occurrence =>
    cases occurrence <;> simp_all [Object.singleton, Object.abstract]

theorem Link.abstract_eq_self {edge : Link}
    (hp : edge.parent.singleton = true) (hc : edge.child.singleton = true) :
    edge.abstract = edge := by
  cases edge
  simp_all [Link.abstract, Object.abstract_eq_self]

theorem frozen_links {heap : List Link} (h : edge ∈ (heap.map Link.abstract).filter
    (fun edge => edge.parent.singleton && edge.child.singleton)) : edge ∈ heap := by
  obtain ⟨member, both⟩ := List.mem_filter.mp h
  obtain ⟨original, old, rfl⟩ := List.mem_map.mp member
  simp only [Bool.and_eq_true] at both
  change original.parent.abstract.singleton = true ∧ original.child.abstract.singleton = true at both
  simp only [Object.abstract_singleton] at both
  rw [Link.abstract_eq_self both.1 both.2]
  exact old

theorem Reaches.frozen {heap : List Link} {source : Object}
    (run : Reaches ((heap.map Link.abstract).filter
      (fun edge => edge.parent.singleton && edge.child.singleton)) [source.abstract] object)
    (precise : object.singleton = true) : Reaches heap [source] object := by
  induction run with
  | @root object member =>
    have eq := List.mem_singleton.mp member
    subst object
    rw [Object.abstract_singleton] at precise
    rw [Object.abstract_eq_self precise]
    exact .root (by simp)
  | edge member _ ih =>
    have both := (List.mem_filter.mp member).2
    simp only [Bool.and_eq_true] at both
    exact .edge (frozen_links member) (ih both.1)

/-- A positive frozen-entry query refers to a concrete object, even when
    other objects in the same frame have been summarized. -/
theorem entry_source_sound {entry : World} {frozen : RawFrame} {object : Object}
    (he : entry.raw = frozen.abstract)
    (h : entryContains entry formal object.abstract = true) :
    ∃ root, frozen.get formal = some root ∧ Reaches frozen.memory.heap [root] object := by
  unfold entryContains at h
  rw [he, RawFrame.get_abstract] at h
  cases hr : frozen.get formal with
  | none => simp [hr] at h
  | some root =>
    simp only [hr, Option.map_some, Option.any_some, Bool.and_eq_true] at h
    have precise := h.1
    rw [Object.abstract_singleton] at precise
    refine ⟨root, rfl, ?_⟩
    have inside := reachable_exact.mp (List.contains_iff_mem.mp h.2)
    have concrete := inside.frozen h.1
    rw [Object.abstract_eq_self precise] at concrete
    exact concrete

theorem view_available {world : World} {frame : RawFrame}
    (h : world.raw = frame.abstract) (hv : world.view register = some (object, view)) :
    ∃ concrete, frame.get register = some concrete ∧ object = concrete.abstract := by
  have raw := World.view_object hv
  rw [h, RawFrame.get_abstract] at raw
  cases hr : frame.get register with
  | none => simp [hr] at raw
  | some concrete =>
    exact ⟨concrete, rfl, (Option.some.inj (by simpa [hr] using raw)).symm⟩

theorem consumed_views {ended : World} (h : consume world source = .ok (object, moved, ended))
    (hv : getSlot ended.views register = some remaining) :
    register ≠ source ∧ source ∉ remaining.dependencies := by
  rw [consume_ends h] at hv
  obtain ⟨slot, found, rfl⟩ := Option.map_eq_some_iff.mp hv
  have key := List.find?_some found
  have live := (List.mem_filter.mp (List.mem_of_find?_eq_some found)).2
  simp only [beq_iff_eq] at key
  subst register
  simpa using live

theorem metadata_operands (h : metadata program action world = .ok (after, uses)) :
    ∀ register ∈ action.operands, (world.view register).isSome = true := by
  intro register member
  cases action <;> simp [Primitive.operands] at member
  case bind destination source mode =>
    subst register
    cases hv : world.view source <;> simp [metadata, hv, need] at h ⊢
  case move destination source =>
    subst register
    cases hv : world.view source <;> simp [metadata, consume, hv, need] at h ⊢
  case store parent field source moving =>
    cases hp : world.view parent
    · simp [metadata, hp, need] at h
    · cases hs : world.view source
      · simp [metadata, hp, hs, need] at h
      · rcases member with rfl | rfl <;> simp [hp, hs]
  case select destination parent field =>
    subst register
    cases hv : world.view parent <;> simp [metadata, hv, need] at h ⊢
  case read source =>
    subst register
    cases hv : world.view source <;> simp [metadata, hv, need] at h ⊢
  case write source =>
    subst register
    cases hv : world.view source <;> simp [metadata, hv, need] at h ⊢
  case publish source =>
    subst register
    cases hv : world.view source <;> simp [metadata, hv, need] at h ⊢

theorem primitive_metadata (h : primitive program action world = .ok (after, uses)) :
    ∃ edited, metadata program action world = .ok (edited, uses) ∧ after.views = edited.views := by
  unfold primitive at h
  cases hm : metadata program action world with
  | error error => simp [hm] at h
  | ok value =>
    obtain ⟨edited, log⟩ := value
    cases he : runPrim action.erase world.raw <;> simp [hm, he, need] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨edited, rfl, rfl⟩

theorem metadata_write (h : metadata program (.write register) world = .ok (after, uses)) :
    ∃ object view, world.view register = some (object, view) ∧ view.mode.writes = true := by
  cases hv : world.view register with
  | none => simp [metadata, hv, need] at h
  | some value =>
    obtain ⟨object, view⟩ := value
    cases hw : view.mode.writes
    · simp [metadata, hv, need, require, hw] at h
    · exact ⟨object, view, rfl, hw⟩

theorem metadata_store (h : metadata program (.store parent field source moving) world = .ok (after, uses)) :
    ∃ object view, world.view parent = some (object, view) ∧ view.mode.writes = true := by
  cases hv : world.view parent with
  | none => simp [metadata, hv, need] at h
  | some value =>
    obtain ⟨object, view⟩ := value
    cases hw : view.mode.writes
    · cases hs : world.view source <;> cases ho : object.singleton <;>
        simp [metadata, hv, need, hs, ho, require, hw] at h
    · exact ⟨object, view, rfl, hw⟩

theorem primitive_authorized {world : World} {frame : RawFrame}
    (h : primitive program action world = .ok (after, uses)) (hw : world.raw = frame.abstract)
    (writer : action.writer = some register) :
    ∃ object view, frame.get register = some object ∧
      world.view register = some (object.abstract, view) ∧ view.mode.writes = true := by
  obtain ⟨edited, hm, _⟩ := primitive_metadata h
  have evidence : ∃ object view, world.view register = some (object, view) ∧ view.mode.writes = true := by
    cases action <;> simp [Primitive.writer] at writer
    case store => subst register; exact metadata_store hm
    case write => subst register; exact metadata_write hm
  obtain ⟨_, view, hv, writable⟩ := evidence
  obtain ⟨object, present, rfl⟩ := view_available hw hv
  exact ⟨object, view, present, hv, writable⟩

def LocalSafety (facts : List Judgment) (entry : Entry) (pc : Nat) (frame : RawFrame)
    (action : Primitive) : Prop :=
  ∃ world, world.raw = frame.abstract ∧ Judgment.point entry pc world ∈ facts ∧
    (∀ register ∈ action.operands, ∃ object view, frame.get register = some object ∧
      world.view register = some (object.abstract, view)) ∧
    ∀ register, action.writer = some register →
      ∃ object view, frame.get register = some object ∧
        world.view register = some (object.abstract, view) ∧ view.mode.writes = true

theorem checked_step_ready (checked : Checked program facts)
    (covered : Covered program facts entry (.at pc frame))
    (hf : program.functions[entry.function]? = some function)
    (hi : function.code[pc]? = some (.step alternatives next)) (ha : action ∈ alternatives) :
    ∃ after,
      runPrim action.erase frame = some after ∧ Covered program facts entry (.at next after) ∧
      LocalSafety facts entry pc frame action := by
  obtain ⟨world, hw, member⟩ := covered
  obtain ⟨after, uses, hp, reached⟩ := checked.primitive member hf hi ha
  obtain ⟨runtime, ran, equivalent⟩ := primitive_refines hp hw
  obtain ⟨edited, operational, _⟩ := primitive_metadata hp
  refine ⟨runtime, ran, ⟨after, equivalent, reached⟩, world, hw, member, ?_, ?_⟩
  · intro register selected
    have live := metadata_operands operational register selected
    cases hv : world.view register with
    | none => simp [hv] at live
    | some value =>
      obtain ⟨o, v⟩ := value
      obtain ⟨object, present, rfl⟩ := view_available hw hv
      exact ⟨object, v, present, rfl⟩
  · exact fun _ writer => primitive_authorized hp hw writer

open Integrated (ParameterMode)

def argumentsAt (frame : RawFrame) (arguments : List Argument) : Option (List (Object × ParameterMode)) :=
  arguments.mapM fun arg => (frame.get arg.source).map (·, arg.marker)

def evaluatedModes (values : List Evaluated) : List (Object × ParameterMode) :=
  values.map (fun (object, _, mode) => (object, mode))

def abstractArgument (arg : Object × ParameterMode) : Object × ParameterMode :=
  (arg.1.abstract, arg.2)

theorem argumentsAt_abstract (frame : RawFrame) (arguments : List Argument) :
    argumentsAt frame.abstract arguments = (argumentsAt frame arguments).map (List.map abstractArgument) := by
  induction arguments with
  | nil => rfl
  | cons arg rest ih =>
    unfold argumentsAt at ih ⊢
    simp only [List.mapM_cons]
    rw [ih, RawFrame.get_abstract]
    cases hr : frame.get arg.source <;>
      cases ht : List.mapM (fun arg => (frame.get arg.source).map (·, arg.marker)) rest <;>
      simp [abstractArgument]

theorem evaluation_records_actuals (he : evaluateArguments world arguments = .ok (after, actuals)) :
    argumentsAt world.raw arguments = some (evaluatedModes actuals) := by
  induction arguments generalizing world after actuals with
  | nil => cases he; rfl
  | cons arg rest ih =>
    rw [evaluateArguments] at he
    cases hv : world.view arg.source with
    | none => simp [hv, need] at he
    | some data =>
      obtain ⟨object, view⟩ := data
      have saved := World.view_object hv
      cases hm : acceptsArgument view arg.marker <;> simp [hv, hm, need, require] at he
      split at he
      · cases hc : consume world arg.source with
        | error error => simp [hc, Except.map] at he
        | ok value =>
          obtain ⟨obj, v, ended⟩ := value
          cases hr : evaluateArguments ended rest with
          | error error => simp [hc, hr, Except.map] at he
          | ok result =>
            obtain ⟨last, values⟩ := result
            simp [hc, hr, Except.map] at he
            obtain ⟨rfl, rfl⟩ := he
            have recorded := ih hr
            rw [consume_raw hc] at recorded
            change List.mapM _ rest = _ at recorded
            simp [argumentsAt, saved, evaluatedModes, recorded]
      · cases hr : evaluateArguments world rest with
        | error error => simp [hr] at he
        | ok result =>
          obtain ⟨last, values⟩ := result
          simp [hr] at he
          obtain ⟨rfl, rfl⟩ := he
          have recorded := ih hr
          change List.mapM _ rest = _ at recorded
          simp [argumentsAt, saved, evaluatedModes, recorded]

theorem separateArguments_pairwise (h : separateArguments heap actuals = true) :
    (evaluatedModes actuals).Pairwise (fun left right =>
      pairConflict left.2 right.2 = true → separated heap [left.1] [right.1] = true) := by
  induction actuals with
  | nil => exact .nil
  | cons first rest ih =>
    obtain ⟨object, view, mode⟩ := first
    simp only [separateArguments, Bool.and_eq_true] at h
    apply List.Pairwise.cons _ (ih h.2)
    intro arg member conflict
    obtain ⟨candidate, listed, rfl⟩ := List.mem_map.mp member
    have pair := List.all_eq_true.mp h.1 candidate listed
    simp [conflict] at pair ⊢
    exact pair

def ConcreteSeparate (heap : List Link) (arguments : List (Object × ParameterMode)) : Prop :=
  arguments.Pairwise fun left right =>
    pairConflict left.2 right.2 = true → ∀ object,
      Reaches heap [left.1] object → Reaches heap [right.1] object → False

theorem prepare_separates {world : World} {frame : RawFrame}
    (h : prepare function world arguments = .ok prepared)
    (hw : world.raw = frame.abstract) :
    ∃ actuals, argumentsAt frame arguments = some actuals ∧ ConcreteSeparate frame.memory.heap actuals := by
  unfold prepare at h
  cases hm : decide (arguments.map Argument.marker = function.parameters) <;> simp [hm, require] at h
  cases he : evaluateArguments world arguments with
  | error error => simp [he] at h
  | ok pair =>
    obtain ⟨after, evaluated⟩ := pair
    cases hs : separateArguments world.raw.memory.heap evaluated <;> simp [he, hs] at h
    have evaluatedEq := evaluation_records_actuals he
    rw [hw, argumentsAt_abstract] at evaluatedEq
    cases ha : argumentsAt frame arguments with
    | none => simp [ha] at evaluatedEq
    | some actuals =>
      have eq := Option.some.inj (by simpa [ha] using evaluatedEq :
        some (actuals.map abstractArgument) = some (evaluatedModes evaluated))
      refine ⟨actuals, rfl, ?_⟩
      have safe := separateArguments_pairwise hs
      rw [← eq, List.pairwise_map] at safe
      apply safe.imp
      intro left right test conflict object hl hr
      have noOverlap := test conflict
      rw [hw] at noOverlap
      exact separated_sound (left := [left.1]) (right := [right.1]) noOverlap hl hr

/-- A reachable call has concrete arguments and satisfies physical disjointness
    for every pair whose modes require separation. -/
theorem checked_call_ready (checked : Checked program facts)
    (covered : Covered program facts entry (.at pc frame))
    (hf : program.functions[entry.function]? = some function)
    (hi : function.code[pc]? = some (.invoke callee arguments destination next)) :
    ∃ (prepared : Prepared) (actuals : List (Object × ParameterMode)) (entered : RawFrame),
      frame.prepare (arguments.map Argument.source) = some entered ∧
      argumentsAt frame arguments = some actuals ∧ ConcreteSeparate frame.memory.heap actuals ∧
      prepared.entered.raw = entered.abstract ∧
      Covered program facts ⟨callee, prepared.entered⟩ (.at 0 entered) := by
  obtain ⟨world, hw, member⟩ := covered
  obtain ⟨_, prepared, _, hp, entered, _⟩ := checked.call member hf hi
  obtain ⟨actuals, ha, separated⟩ := prepare_separates hp hw
  have raw := prepare_raw hp
  rw [hw, RawFrame.prepare_abstract] at raw
  cases hr : frame.prepare (arguments.map Argument.source) with
  | none => simp [hr] at raw
  | some runtime =>
    have eq : prepared.entered.raw = runtime.abstract := by simpa [hr] using raw.symm
    exact ⟨prepared, actuals, runtime, rfl, ha, separated, eq, prepared.entered, eq, entered⟩

end RilAccess.Provenance
