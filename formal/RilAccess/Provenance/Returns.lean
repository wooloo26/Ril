import RilAccess.Provenance.Safety

namespace RilAccess.Provenance

def FromEntry (frozen : RawFrame) (formal : Register) (object : Object) : Prop :=
  ∃ root, frozen.get formal = some root ∧ Reaches frozen.memory.heap [root] object

theorem slot_abstract (program : Program) (object : Object) (field : Field) :
    program.slot object.abstract field = program.slot object field := rfl

theorem newLinks_abstract (newSlots : List (Object × Field)) (heap : List Link) :
    (newLinks newSlots heap).map Link.abstract = newLinks newSlots (heap.map Link.abstract) := by
  simp [newLinks, List.filter_map, Function.comp_def, Link.abstract, HeapLink.map]

theorem isolated_sound {world : World} {frame : RawFrame}
    (hw : world.raw = frame.abstract)
    (h : isolated world root.abstract outside = true)
    (covers : Includes (concreteOutside.map Object.abstract) outside)
    (newObject : Reaches (newLinks world.newSlots frame.memory.heap) [root] object)
    (oldObject : Reaches frame.memory.heap concreteOutside object) : False := by
  have fresh := newObject.abstract
  rw [newLinks_abstract] at fresh
  have hf : object.abstract ∈ newRegion world root.abstract := by
    rw [newRegion, hw, raw_abstract_heap]
    exact reachable_exact.mpr fresh
  have outsideReach (value : Object)
      (path : Reaches (frame.memory.heap.map Link.abstract) (concreteOutside.map Object.abstract) value) :
      Reaches (frame.memory.heap.map Link.abstract) outside value := by
    induction path with
    | root found => exact .root (covers _ found)
    | edge link _ ih => exact .edge link ih
  have old := reachable_exact.mpr (outsideReach _ oldObject.abstract)
  have absent := List.all_eq_true.mp h _ hf
  rw [hw, raw_abstract_heap] at absent
  simp [old] at absent

/-- Shared proof for exclusive transfers, including a resolved single-shot
    `&once` or `new` handoff supplied with its live parent footprint. -/
theorem handoff_subgraph_isolated {world ended : World} {frame : RawFrame}
    (h : takeHandoff world register = .ok (object, handed, ended))
    (hw : world.raw = frame.abstract)
    (covers : Includes (outside.map Object.abstract) (ended.liveObjects ++ ended.outsideVisible)) :
    ∃ root, frame.get register = some root ∧
      ∀ target, Reaches (newLinks world.newSlots frame.memory.heap) [root] target →
        Reaches frame.memory.heap outside target → False := by
  obtain ⟨⟨original, live⟩, _, safe⟩ := handoff_conditions h
  obtain ⟨root, present, rfl⟩ := view_available hw live
  exact ⟨root, present, fun _ own outsideVisible => isolated_sound hw safe covers own outsideVisible⟩

theorem mapM_covers {f : α → Option β} (h : List.mapM f xs = some ys) (hx : x ∈ xs) :
    ∃ y ∈ ys, f x = some y := by
  induction xs generalizing ys with
  | nil => simp at hx
  | cons a rest ih =>
    simp only [List.mapM_cons] at h
    cases hf : f a <;> cases hm : List.mapM f rest <;> simp [hf, hm] at h
    subst ys
    rename_i lead tail
    rcases List.mem_cons.mp hx with rfl | member
    · exact ⟨lead, by simp, hf⟩
    · obtain ⟨y, hy, lookup⟩ := ih hm member
      exact ⟨y, by simp [hy], lookup⟩

theorem inferOld_sound {entry : World} {function : Function} {object : Object}
    (hf : entry.raw = frozen.abstract)
    (h : inferOld function entry (object.abstract, mode) = some source) :
    source.mode = mode ∧ formalMaySource function source.formal mode = true ∧
      FromEntry frozen source.formal object := by
  cases found : function.parameters.zipIdx.find? (fun pair =>
      formalMaySource function pair.2 mode && entryContains entry pair.2 object.abstract) with
  | some pair =>
    obtain ⟨parameter, formal⟩ := pair
    simp [inferOld, found] at h
    subst source
    have test := List.find?_some found
    simp only [Bool.and_eq_true] at test
    exact ⟨rfl, test.1, entry_source_sound hf test.2⟩
  | none => simp [inferOld, found] at h

theorem boundary_found {world : World} {frame : RawFrame}
    (hw : world.raw = frame.abstract)
    (edge : Link) (present : edge ∈ frame.memory.heap)
    (inside : Reaches (newLinks world.newSlots frame.memory.heap) [root] edge.parent)
    (schema : program.slot edge.parent edge.field = some member)
    (old : (edge.parent.abstract, edge.field) ∉ world.newSlots) :
    (edge.child.abstract, member.access) ∈ boundaries program world root.abstract := by
  have path := inside.abstract
  rw [newLinks_abstract] at path
  have inNew : edge.parent.abstract ∈ newRegion world root.abstract := by
    rw [newRegion, hw, raw_abstract_heap]
    exact reachable_exact.mpr path
  unfold boundaries
  refine List.mem_eraseDups.mpr (List.mem_filterMap.mpr ⟨edge.abstract, ?_, ?_⟩)
  · rw [hw, raw_abstract_heap]
    exact List.mem_map_of_mem present
  · simp [Link.abstract, HeapLink.map, inNew, slot_abstract, schema, old]

def ReturnGuarantee (program : Program) (function : Function) (frozen frame : RawFrame)
    (world : World) (source : Option Register) (value : Returned) : Prop :=
  match function.signature.result with
  | .unit => source = none
  | mode =>
    ∃ register object view, source = some register ∧ frame.get register = some object ∧
      world.view register = some (object.abstract, view) ∧
      match mode with
      | .plain => view.mode = .immutable
      | .observe formals => view.mode = .ref ∧ ∃ formal ∈ formals, FromEntry frozen formal object
      | .retained formal => view.mode = .shared ∧ view.scopedHold = false ∧ FromEntry frozen formal object
      | .construction =>
        view.qualified = true ∧
        (∀ outside, Includes (outside.map Object.abstract) world.outsideVisible →
          ∀ target, Reaches (newLinks world.newSlots frame.memory.heap) [object] target →
            Reaches frame.memory.heap outside target → False) ∧
        ∀ edge ∈ frame.memory.heap,
          Reaches (newLinks world.newSlots frame.memory.heap) [object] edge.parent →
          ∀ member, program.slot edge.parent edge.field = some member →
          (edge.parent.abstract, edge.field) ∉ world.newSlots →
          ∃ old ∈ value.contained, old.mode = member.access ∧
            formalMaySource function old.formal old.mode = true ∧ FromEntry frozen old.formal edge.child
      | .unit => False

theorem checked_return_sound {entry world : World} {frozen frame : RawFrame}
    (hf : entry.raw = frozen.abstract) (hw : world.raw = frame.abstract)
    (h : checkReturn program function entry world source = .ok value) :
    ReturnGuarantee program function frozen frame world source value := by
  unfold ReturnGuarantee
  cases hc : function.signature.result with
  | unit =>
    cases source <;> simp_all [checkReturn]
  | plain =>
    cases source with
    | none => simp [checkReturn, hc] at h
    | some register =>
      cases hv : world.view register with
      | none => simp [checkReturn, hc, hv, need] at h
      | some data =>
        obtain ⟨_, view⟩ := data
        have ⟨object, hr, he⟩ := view_available hw hv
        subst he
        cases hm : view.mode <;> simp [checkReturn, hc, hv, need, require, hm] at h
        exact ⟨register, object, view, rfl, hr, hv, hm⟩
  | observe formals =>
    cases source with
    | none => simp [checkReturn, hc] at h
    | some register =>
      cases hv : world.view register with
      | none => simp [checkReturn, hc, hv, need] at h
      | some data =>
        obtain ⟨_, view⟩ := data
        obtain ⟨object, hr, rfl⟩ := view_available hw hv
        simp [checkReturn, hc, hv, need, require] at h
        split at h
        · rename_i valid
          refine ⟨register, object, view, rfl, hr, hv, valid.1.1, ?_⟩
          obtain ⟨formal, member, _, fromEntry⟩ := valid.2
          exact ⟨formal, member, entry_source_sound hf fromEntry⟩
        · simp at h
  | retained formal =>
    cases source with
    | none => simp [checkReturn, hc] at h
    | some register =>
      cases hv : world.view register with
      | none => simp [checkReturn, hc, hv, need] at h
      | some data =>
        obtain ⟨_, view⟩ := data
        obtain ⟨object, hr, rfl⟩ := view_available hw hv
        simp [checkReturn, hc, hv, need, require] at h
        split at h
        · rename_i valid
          exact ⟨register, object, view, rfl, hr, hv,
            valid.1.1.1, valid.1.1.2, entry_source_sound hf valid.2⟩
        · simp at h
  | construction =>
    cases source with
    | none => simp [checkReturn, hc] at h
    | some register =>
      cases hv : world.view register with
      | none => simp [checkReturn, hc, hv, need] at h
      | some data =>
        obtain ⟨_, view⟩ := data
        obtain ⟨object, hr, rfl⟩ := view_available hw hv
        simp [checkReturn, hc, hv, need, require] at h
        split at h
        · rename_i valid
          cases hm : (boundaries program world object.abstract).mapM (inferOld function entry) with
          | none => simp [hm] at h
          | some old =>
            simp [hm] at h
            subst value
            refine ⟨register, object, view, rfl, hr, hv, valid.1, ?_, ?_⟩
            · intro outside covers target inside outsideVisible
              exact isolated_sound hw valid.2 covers inside outsideVisible
            · intro edge present inside member schema oldMode
              have boundary := boundary_found hw edge present inside schema oldMode
              obtain ⟨srcInst, contains, inferred⟩ := mapM_covers hm boundary
              have ⟨mode, permits, actual⟩ := inferOld_sound hf inferred
              exact ⟨srcInst, contains, mode, mode ▸ permits, actual⟩
        · simp at h

theorem checked_return_ready (checked : Checked program facts inputs) {frozen frame : RawFrame}
    (hfrozen : entry.world.raw = frozen.abstract)
    (covered : Covered program facts entry (.at pc frame))
    (hf : program.functions[entry.function]? = some function)
    (hi : function.code[pc]? = some (.ret source)) :
    ∃ world value returned, frame.returnValue source = some returned ∧
      ReturnGuarantee program function frozen frame world source value ∧
      Covered program facts entry (.returned source frame) := by
  obtain ⟨world, hw, member⟩ := covered
  obtain ⟨value, hv, result⟩ := checked.ret member hf hi
  have safe := checked_return_sound hfrozen hw hv
  have progress : ∃ returned, frame.returnValue source = some returned := by
    unfold ReturnGuarantee at safe
    split at safe
    · subst source
      exact ⟨none, rfl⟩
    · obtain ⟨register, object, _, rfl, present, _, _⟩ := safe
      exact ⟨some object, by simp [RawFrame.returnValue, Option.mapM, present]⟩
  obtain ⟨returned, hr⟩ := progress
  exact ⟨world, value, returned, hr, safe, world, value, function, hw, result, hf, hv⟩

end RilAccess.Provenance
