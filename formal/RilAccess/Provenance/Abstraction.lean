import RilAccess.Provenance.Kernel
import RilAccess.Access.Proofs
import RilAccess.Graph.Authority

namespace RilAccess.Provenance

@[simp] theorem Object.abstract_singleton (object : Object) :
    object.abstract.singleton = object.singleton := by
  cases object with | mk site occurrence => cases occurrence <;> rfl

theorem Object.eq_of_singleton_abstract {left right : Object} (h : left.abstract = right.abstract)
    (hs : right.singleton = true) : left = right := by
  cases left with
  | mk ls lo =>
    cases right with
    | mk rs ro =>
      cases ro with
      | some x => simp [Object.singleton] at hs
      | none =>
        cases lo <;> simp [Object.abstract] at h ⊢
        exact h

@[simp] theorem Object.abstract_idem (object : Object) :
    object.abstract.abstract = object.abstract := by
  cases object with | mk site occurrence => cases occurrence <;> rfl

@[simp] theorem Link.abstract_idem (link : Link) : link.abstract.abstract = link.abstract := by
  cases link
  simp [Link.abstract]

@[simp] theorem Memory.abstract_idem (memory : Memory) : memory.abstract.abstract = memory.abstract := by
  cases memory
  simp [Memory.abstract, List.map_map, Function.comp_def]

@[simp] theorem RawFrame.abstract_idem (frame : RawFrame) : frame.abstract.abstract = frame.abstract := by
  cases frame
  simp [RawFrame.abstract, List.map_map, Function.comp_def]

theorem getSlot_map (slots : List (Nat × α)) (r : Register) (f : α → β) :
    getSlot (slots.map (fun (key, value) => (key, f value))) r = (getSlot slots r).map f := by
  induction slots with
  | nil => rfl
  | cons slot slots ih =>
    obtain ⟨key, value⟩ := slot
    simp only [getSlot, List.map_cons, List.find?_cons]
    split <;> simp_all [getSlot]

theorem putSlot_map (slots : List (Nat × α)) (r : Register) (value : α) (f : α → β) :
    (putSlot slots r value).map (fun (key, item) => (key, f item)) =
      putSlot (slots.map (fun (key, item) => (key, f item))) r (f value) := by
  simp [putSlot, List.filter_map, Function.comp_def]

@[simp] theorem RawFrame.get_abstract (frame : RawFrame) (r : Register) :
    frame.abstract.get r = (frame.get r).map Object.abstract :=
  getSlot_map frame.registers r Object.abstract

@[simp] theorem RawFrame.put_abstract (frame : RawFrame) (r : Register) (object : Object) :
    (frame.put r object).abstract = frame.abstract.put r object.abstract := by
  simp [RawFrame.put, RawFrame.abstract, putSlot_map]

theorem Link.atSlot_abstract (link : Link) (parent : Object) (field : Field)
    (h : parent.singleton = true) :
    link.abstract.atSlot parent.abstract field = link.atSlot parent field := by
  have eq : (link.parent.abstract = parent.abstract) = (link.parent = parent) :=
    propext ⟨fun he => Object.eq_of_singleton_abstract he h, congrArg Object.abstract⟩
  simp [Link.atSlot, Link.abstract, eq]

@[simp] theorem raw_abstract_sites (frame : RawFrame) :
    frame.abstract.memory.sites = frame.memory.sites := rfl

@[simp] theorem raw_abstract_clock (frame : RawFrame) : frame.abstract.memory.clock = 0 := rfl

@[simp] theorem raw_abstract_heap (frame : RawFrame) :
    frame.abstract.memory.heap = frame.memory.heap.map Link.abstract := rfl

theorem abstract_filter_slot (heap : List Link) (owner : Object) (field : Field)
    (hs : owner.singleton = true) :
    (heap.filter (!Link.atSlot owner field ·)).map Link.abstract =
      (heap.map Link.abstract).filter (!Link.atSlot owner.abstract field ·) := by
  induction heap with
  | nil => rfl
  | cons link heap ih =>
    simp only [List.filter_cons, List.map_cons, Link.atSlot_abstract link owner field hs]
    split <;> simp [ih]

theorem abstract_find_slot (heap : List Link) (owner : Object) (field : Field)
    (hs : owner.singleton = true) :
    (heap.find? (Link.atSlot owner field)).map Link.abstract =
      (heap.map Link.abstract).find? (Link.atSlot owner.abstract field) := by
  induction heap with
  | nil => rfl
  | cons link heap ih =>
    simp only [List.find?_cons, List.map_cons, Link.atSlot_abstract link owner field hs]
    split <;> simp [ih]

def PreciseOwner (frame : RawFrame) : Prim → Prop
  | .store parent _ _ | .select _ parent _ =>
      ∀ object, frame.get parent = some object → object.singleton = true
  | _ => True

theorem runPrim_abstract (frame : RawFrame) (action : Prim)
    (h : PreciseOwner frame action) :
    (runPrim action frame).map RawFrame.abstract =
      (runPrim action frame.abstract).map RawFrame.abstract := by
  cases action with
  | alloc destination site =>
    have registers (value : Object) :
        ((frame.put destination value).registers.map (fun (r, o) => (r, o.abstract))) =
          (frame.abstract.put destination value.abstract).registers :=
      congrArg RawFrame.registers (RawFrame.put_abstract frame destination value)
    have normalized (value : Object) :
        ((frame.abstract.put destination value).registers.map (fun (r, o) => (r, o.abstract))) =
          (frame.abstract.put destination value.abstract).registers := by
      have he := congrArg RawFrame.registers (RawFrame.put_abstract frame.abstract destination value)
      rw [RawFrame.abstract_idem] at he
      exact he
    have alloc (repeated : Bool) :
        (frame.allocateAt destination site repeated).abstract =
          (frame.abstract.allocateAt destination site repeated).abstract := by
      cases repeated <;>
        simp only [RawFrame.allocateAt, raw_abstract_clock, raw_abstract_heap, raw_abstract_sites,
          Bool.false_eq_true, if_false, if_true]
      all_goals
        change RawFrame.mk _ (Memory.mk _ _ _) = RawFrame.mk _ (Memory.mk _ _ _)
        rw [registers, normalized]
        simp only [List.map_map, Function.comp_def, Link.abstract_idem]
        try rfl
    simpa [runPrim, RawFrame.allocate] using alloc (frame.memory.sites.contains site)
  | copy destination source =>
    cases he : frame.get source <;>
      simp [runPrim, he, RawFrame.put_abstract]
  | read register | write register | publish register =>
    cases he : frame.get register <;> simp [runPrim, he]
  | store parent field source =>
    cases hp : frame.get parent with
    | none => simp [runPrim, hp]
    | some owner =>
      have hs := h owner hp
      cases he : frame.get source
      · simp [runPrim, hp, he]
      · simp only [runPrim, RawFrame.get_abstract, hp, he, Option.map_some, Option.bind_some,
          Option.some.injEq]
        simp [RawFrame.store, RawFrame.abstract, Memory.abstract, abstract_filter_slot _ _ _ hs,
          List.map_map, Function.comp_def, Link.abstract, Object.abstract_idem]
        rw [List.filter_map, List.map_map]
        simp [Function.comp_def]
  | select destination parent field =>
    cases hp : frame.get parent with
    | none => simp [runPrim, hp]
    | some owner =>
      have hs := h owner hp
      have hf := abstract_find_slot frame.memory.heap owner field hs
      simp only [runPrim, raw_abstract_heap, RawFrame.get_abstract, hp, Option.map_some, Option.bind_some, ← hf]
      cases he : frame.memory.heap.find? (Link.atSlot owner field) <;>
        simp [RawFrame.put_abstract, Link.abstract]

theorem World.view_object {world : World} {register : Register} {object : Object} {view : View}
    (h : world.view register = some (object, view)) :
    world.raw.get register = some object := by
  unfold World.view at h
  cases hr : world.raw.get register <;> cases hv : getSlot world.views register <;> simp_all

theorem metadata_precise (h : metadata program action world = .ok (edited, uses))
    (hw : world.raw = frame.abstract) : PreciseOwner frame action.erase := by
  cases action <;> try trivial
  case store parent field source moving =>
    intro object ho
    unfold metadata at h
    cases hv : world.view parent with
    | none => simp [hv, need] at h
    | some pair =>
      obtain ⟨owner, view⟩ := pair
      have hs : owner.singleton = true := by
        cases hv' : world.view source <;> cases hb : owner.singleton <;>
          simp_all [need, require]
      have eq : owner = object.abstract := by
        have := World.view_object hv
        simp [hw, ho] at this
        exact this.symm
      simpa [eq] using hs
  case select destination parent field =>
    intro object ho
    unfold metadata at h
    cases hv : world.view parent with
    | none => simp [hv, need] at h
    | some pair =>
      obtain ⟨owner, view⟩ := pair
      have hs : owner.singleton = true := by
        cases hb : owner.singleton <;> simp_all [need, require]
      have eq : owner = object.abstract := by
        have := World.view_object hv
        simp [hw, ho] at this
        exact this.symm
      simpa [eq] using hs

theorem primitive_refines (h : primitive program action world = .ok (after, uses))
    (hw : world.raw = frame.abstract) :
    ∃ raw, runPrim action.erase frame = some raw ∧ after.raw = raw.abstract := by
  unfold primitive at h
  cases hm : metadata program action world with
  | error error => simp [hm] at h
  | ok value =>
    obtain ⟨edited, emitted⟩ := value
    cases he : runPrim action.erase world.raw with
    | none => simp [hm, he, need] at h
    | some next =>
      have commutes := runPrim_abstract frame action.erase (metadata_precise hm hw)
      rw [← hw, he] at commutes
      cases hr : runPrim action.erase frame with
      | none => simp [hr] at commutes
      | some raw =>
        simp [hm, he, need] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨raw, rfl, (by simpa [hr] using commutes.symm)⟩

theorem mapM_arguments (arguments : List Register) (frame : RawFrame) :
    List.mapM frame.abstract.get arguments =
      (List.mapM frame.get arguments).map (List.map Object.abstract) := by
  induction arguments with
  | nil => rfl
  | cons register rest ih =>
    simp only [List.mapM_cons, RawFrame.get_abstract]
    cases hr : frame.get register <;> cases ht : List.mapM frame.get rest <;>
      simp [ih, ht]

theorem RawFrame.prepare_abstract (caller : RawFrame) (arguments : List Register) :
    caller.abstract.prepare arguments = (caller.prepare arguments).map RawFrame.abstract := by
  unfold RawFrame.prepare
  rw [mapM_arguments]
  cases h : List.mapM caller.get arguments
  · rfl
  · rename_i values
    simp [RawFrame.abstract, List.zipIdx_map, List.map_map, Function.comp_def]

theorem RawFrame.resume_abstract (caller : RawFrame) (memory : Memory) (dest : Option Register)
    (value : Option Object) :
    caller.abstract.resume memory.abstract dest (value.map Object.abstract) =
      (caller.resume memory dest value).map RawFrame.abstract := by
  cases dest with
  | none => cases value <;> rfl
  | some register =>
    cases value with
    | none => rfl
    | some object =>
      exact congrArg some (RawFrame.put_abstract { caller with memory } register object).symm

theorem RawFrame.return_abstract (frame : RawFrame) (source : Option Register) :
    frame.abstract.returnValue source =
      (frame.returnValue source).map (Option.map Object.abstract) := by
  cases source with
  | none => rfl
  | some register =>
    unfold RawFrame.returnValue
    simp [Option.mapM, RawFrame.get_abstract, Function.comp_def]

theorem prepare_raw (h : prepare function world arguments = .ok prepared) :
    world.raw.prepare (arguments.map Argument.source) = some prepared.entered.raw := by
  unfold prepare at h
  cases ha : decide (arguments.map Argument.marker = function.parameters) <;> simp [ha, require] at h
  cases he : evaluateArguments world arguments with
  | error error => simp [he] at h
  | ok data =>
    obtain ⟨after, actuals⟩ := data
    cases hs : separateArguments world.raw.memory.heap actuals <;> simp [he, hs] at h
    cases hr : world.raw.prepare (arguments.map Argument.source) <;> simp [hr, need] at h
    cases h
    rfl

theorem consume_ends (h : consume world register = .ok (object, view, ended)) :
    ended = world.endPath register := by
  unfold consume at h
  cases hv : world.view register with
  | none => simp [hv, need] at h
  | some data =>
    obtain ⟨obj, v⟩ := data
    simp [hv, need, require] at h
    split at h
    · simp at h
      obtain ⟨_, _, rfl⟩ := h
      rfl
    · simp at h

theorem consume_raw (h : consume world register = .ok (object, view, ended)) :
    ended.raw = world.raw := by
  rw [consume_ends h]
  rfl

theorem evaluated_raw (h : evaluateArguments world arguments = .ok (ended, evaluated)) :
    ended.raw = world.raw := by
  induction arguments generalizing world evaluated with
  | nil => cases h; rfl
  | cons argument rest ih =>
    rw [evaluateArguments] at h
    cases hv : world.view argument.source with
    | none => simp [hv, need] at h
    | some data =>
      obtain ⟨object, view⟩ := data
      cases hm : acceptsArgument view argument.marker <;> simp [hv, hm, need, require] at h
      split at h
      · cases hc : consume world argument.source with
        | error error => simp [hc, Except.map] at h
        | ok transfer =>
          obtain ⟨obj, v, after⟩ := transfer
          cases he : evaluateArguments after rest with
          | error error => simp [hc, Except.map, he] at h
          | ok result =>
            obtain ⟨last, actuals⟩ := result
            simp [hc, Except.map, he] at h
            obtain ⟨rfl, _⟩ := h
            exact (ih he).trans (consume_raw hc)
      · cases he : evaluateArguments world rest with
        | error error => simp [he] at h
        | ok result =>
          obtain ⟨last, actuals⟩ := result
          simp [he] at h
          obtain ⟨rfl, _⟩ := h
          exact ih he

theorem prepared_caller_raw (h : prepare function world arguments = .ok prepared) :
    prepared.caller.raw = world.raw := by
  unfold prepare at h
  cases ha : decide (arguments.map Argument.marker = function.parameters) <;> simp [ha, require] at h
  cases he : evaluateArguments world arguments with
  | error error => simp [he] at h
  | ok data =>
    obtain ⟨after, actuals⟩ := data
    cases hs : separateArguments world.raw.memory.heap actuals <;> simp [he, hs] at h
    cases hr : world.raw.prepare (arguments.map Argument.source) <;> simp [hr, need] at h
    cases h
    exact evaluated_raw he

@[simp] theorem rawInstruction_erase (program : Program) (function pc : Nat) :
    rawInstruction program.erase function pc = (program.instruction function pc).map Instruction.erase := by
  unfold rawInstruction Program.erase Program.instruction
  cases h : program.functions[function]? <;> simp [h]

theorem resume_raw (h : resume program prepared exited source checked destination = .ok after)
    (hv : exited.raw.returnValue source = some result) :
    prepared.caller.raw.resume exited.raw.memory (destination.map Prod.fst) result = some after.raw := by
  unfold resume at h
  cases hr : prepared.caller.raw.resume exited.raw.memory (destination.map Prod.fst) result with
  | none => simp [hv, hr, need] at h
  | some raw =>
    cases he : receiveResult program prepared exited checked destination result with
    | error error => simp [hv, hr, he, need] at h
    | ok world =>
      simp [hv, hr, he, need] at h
      subst after
      rfl

end RilAccess.Provenance
