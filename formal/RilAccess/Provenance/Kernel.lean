import RilAccess.Provenance.Checking

namespace RilAccess.Provenance

structure Entry where
  function : Nat
  world : World
  deriving Repr, DecidableEq

inductive Judgment where
  | point (entry : Entry) (pc : Nat) (world : World)
  | returned (entry : Entry) (source : Option Register) (world : World) (value : Returned)
  | aborted (entry : Entry) (world : World)
  | use (entry : Entry) (use : Use)
  | writesObject (entry : Entry) (object : Object)
  | publication (entry : Entry)
  | rejected (function pc : Nat) (error : Error)
  deriving Repr, DecidableEq

def record (entry : Entry) (uses : List Use) : List Judgment :=
  uses.map (.use entry)

def useActual (prepared : Prepared) (use : Use) : List Use :=
  match prepared.actuals[use.1]? with
  | none => []
  | some (_, view, _) =>
    match use.2 with
    | .rootRetain | .retain => []
    | kind => used view kind

def propagate (program : Program) (entry callee : Entry) (pc next : Nat) (prepared : Prepared)
    (destination : Option (Register × Access)) : Judgment → List Judgment
  | .use key use =>
    if key = callee then record entry (useActual prepared use) else []
  | .writesObject key object =>
    if key = callee then [.writesObject entry object] else []
  | .publication key =>
    if key = callee then [.publication entry] else []
  | .returned key source exited result =>
    if key = callee then
      match resume program prepared exited source result destination with
      | .ok after => [.point entry next after]
      | .error error => [.rejected entry.function pc error]
    else []
  | .aborted key exited =>
    if key = callee then
      let after := abortCall prepared exited
      .aborted entry after :: record entry (survivingStores after none)
    else []
  | _ => []

def expand (program : Program) (known : List Judgment) : Judgment → List Judgment
  | .point entry pc world =>
    match program.functions[entry.function]? with
    | none => [.rejected entry.function pc .missingInstruction]
    | some function =>
      match function.code[pc]? with
      | none => [.rejected entry.function pc .missingInstruction]
      | some (.branch targets) =>
        if targets.isEmpty then [.rejected entry.function pc .invalidProgram]
        else targets.map (fun next => .point entry next world)
      | some (.step alternatives next) =>
        if alternatives.isEmpty then [.rejected entry.function pc .invalidProgram]
        else alternatives.flatMap fun action =>
          match primitive program action world with
          | .ok (after, uses) =>
            let written := (action.writer.bind world.raw.get).toList.map (.writesObject entry)
            let published := match action with | .publish _ => [.publication entry] | _ => []
            .point entry next after :: (record entry uses ++ written ++ published)
          | .error error => [.rejected entry.function pc error]
      | some (.invoke callee arguments destination next) =>
        match program.functions[callee]? with
        | none => [.rejected entry.function pc .missingInstruction]
        | some target =>
          match prepare target world arguments with
          | .error error => [.rejected entry.function pc error]
          | .ok prepared =>
            let called : Entry := ⟨callee, prepared.entered⟩
            .point called 0 prepared.entered ::
              known.flatMap (propagate program entry called pc next prepared destination)
      | some (.ret source) =>
        match checkReturn program function entry.world world source with
        | .ok value => .returned entry source world value :: record entry (value.uses ++ survivingStores world source)
        | .error error => [.rejected entry.function pc error]
      | some .abort => .aborted entry world :: record entry (survivingStores world none)
  | _ => []

theorem expand_monotone (program : Program) : MonotoneExpansion (expand program) := by
  intro left right includes fact out member
  cases fact with
  | point entry pc world =>
    cases hf : program.functions[entry.function]? with
    | none => simpa only [expand, hf] using member
    | some function =>
      cases hi : function.code[pc]? with
      | none => simpa only [expand, hf, hi] using member
      | some instruction =>
        cases instruction <;> simp only [expand, hf, hi] at member ⊢ <;> try exact member
        rename_i callee arguments destination next
        cases hc : program.functions[callee]? with
        | none => simpa only [hc] using member
        | some target =>
          cases hp : prepare target world arguments with
          | error error => simpa only [hc, hp] using member
          | ok prepared =>
            simp only [hc, hp] at member ⊢
            rcases List.mem_cons.mp member with rfl | h
            · exact List.mem_cons_self
            · obtain ⟨fact, hf, hout⟩ := List.mem_flatMap.mp h
              exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨fact, includes fact hf, hout⟩)
  | _ => simp [expand] at member

def startEntry : Entry := ⟨0, {}⟩
def seed : List Judgment := [.point startEntry 0 startEntry.world]

def validProgram (program : Program) : Bool :=
  (program.functions[0]?).any (fun f => f.parameters.isEmpty) &&
  decide ((program.slots.map (fun s => (s.site, s.field))).Nodup)

def entryUses (facts : List Judgment) (entry : Entry) : List Use :=
  facts.filterMap fun
    | .use key use => if key = entry then some use else none
    | _ => none

def inferredContained (facts : List Judgment) (entry : Entry) : List OldSource :=
  facts.flatMap fun
    | .returned key _ _ result => if key = entry then result.contained else []
    | _ => []

def agrees (xs ys : List α) [DecidableEq α] : Bool :=
  xs.all (fun x => ys.contains x) && ys.all (fun y => xs.contains y)

def parameterWrite (function : Function) (facts : List Judgment) (entry : Entry) : Bool :=
  let writable := function.parameters.zipIdx.filterMap (fun (mode, formal) =>
    if (paramAccess mode).writes then entry.world.raw.get formal else none)
  let regions := reachable entry.world.raw.memory.heap writable
  facts.any fun
    | .writesObject key object => key == entry && regions.contains object
    | _ => false

def checkInterface (program : Program) (facts : List Judgment) (entry : Entry) : Except Error Unit := do
  let function ← need program.functions[entry.function]? .missingInstruction
  let uses := entryUses facts entry
  require (function.parameters.zipIdx.all fun (mode, formal) =>
    match mode with
    | .mutable => uses.contains (formal, .write) || uses.contains (formal, .consume)
    | .retained => uses.contains (formal, .retain) || uses.contains (formal, .rootRetain) ||
      uses.contains (formal, .publish)
    | _ => true) .unusedParameter
  let writes := parameterWrite function facts entry || uses.any (fun (formal, kind) =>
    kind == .write && (function.parameters[formal]?).any (fun mode => (paramAccess mode).writes))
  let retains := facts.contains (.publication entry) ||
    uses.any (fun (_, kind) => kind == .retain || kind == .publish)
  require (function.contract.writes == writes && function.contract.retains == retains &&
    agrees function.contract.contained (inferredContained facts entry)) .contract

structure Diagnostic where
  function : Nat
  pc : Nat
  error : Error
  deriving Repr, DecidableEq

def failures (facts : List Judgment) : List Diagnostic :=
  facts.filterMap fun
    | .rejected function pc error => some ⟨function, pc, error⟩
    | _ => none

def entries (facts : List Judgment) : List Entry :=
  (facts.filterMap fun
    | .point entry 0 _ => some entry
    | _ => none).eraseDups

structure Certificate where
  facts : List Judgment
  deriving Repr, DecidableEq

def interfaceFailure (program : Program) (facts : List Judgment) : Option Diagnostic :=
  (entries facts).findSome? fun entry =>
    match checkInterface program facts entry with
    | .ok () => none
    | .error error => some ⟨entry.function, 0, error⟩

/-- Exhaustion is a diagnostic. A returned certificate always represents
    a closed and least solution, regardless of the requested work budget. -/
def check (program : Program) (budget : Nat := 256) : Except Diagnostic Certificate :=
  if validProgram program then
    match saturate (expand program) budget seed with
    | none => .error ⟨0, 0, .analysisLimit⟩
    | some facts =>
      match (failures facts).head?.orElse (fun _ => interfaceFailure program facts) with
      | some diagnostic => .error diagnostic
      | none => .ok ⟨facts⟩
  else .error ⟨0, 0, .invalidProgram⟩

end RilAccess.Provenance
