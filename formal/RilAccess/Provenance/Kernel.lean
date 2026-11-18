import RilAccess.Provenance.Checking
import RilAccess.Solver.Saturation

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
  | writesObject (entry : Entry) (region : AllocationClass) (localAllocation : Bool)
  | publication (entry : Entry)
  | rejected (function pc : Nat) (error : Error)
  deriving Repr, DecidableEq

def record (entry : Entry) (uses : List Use) : List Judgment :=
  uses.map (.use entry)

def abortFacts (entry : Entry) (pc : Nat) (world : World) : List Judgment :=
  if world.scopes.isEmpty then .aborted entry world :: record entry (survivingStores world none)
  else [.rejected entry.function pc .scopeOrder]

def useActual (prepared : Prepared) (use : Use) : List Use :=
  match prepared.actuals[use.1]? with
  | none => []
  | some (_, view, _) =>
    match use.2 with
    | .rootRetain | .retain => []
    | kind => used view kind

inductive CallFact where
  | use (use : Use)
  | write (region : AllocationClass) (localAllocation : Bool)
  | publication
  | returned (source : Option Register) (world : World) (value : Returned)
  | aborted (world : World)
  deriving Repr, DecidableEq

@[simp] def Judgment.callFact (callee : Entry) : Judgment → Option CallFact
  | .use key evidence =>
    if key = callee then some (.use evidence) else none
  | .writesObject key object localAllocation =>
    if key = callee then some (.write object localAllocation) else none
  | .publication key =>
    if key = callee then some .publication else none
  | .returned key source exited result =>
    if key = callee then some (.returned source exited result) else none
  | .aborted key exited =>
    if key = callee then some (.aborted exited) else none
  | _ => none

@[simp] def applyCallFact (program : Program) (entry : Entry) (pc next : Nat)
    (prepared : Prepared) (destination : Option (Register × Access)) (onAbort : Option Nat) : CallFact → List Judgment
  | .use use => record entry (useActual prepared use)
  | .write object localAllocation => [.writesObject entry object localAllocation]
  | .publication => [.publication entry]
  | .returned source exited result =>
    match resume program prepared exited source result destination with
    | .ok after => [.point entry next after]
    | .error error => [.rejected entry.function pc error]
  | .aborted exited =>
    let after := abortCall prepared exited
    match onAbort with
    | none => abortFacts entry pc after
    | some handler => [.point entry handler after]

def propagate (program : Program) (entry callee : Entry) (pc next : Nat) (prepared : Prepared)
    (destination : Option (Register × Access)) (onAbort : Option Nat) (fact : Judgment) : List Judgment :=
  (fact.callFact callee).toList.flatMap (applyCallFact program entry pc next prepared destination onAbort)

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
            let written := (action.writer.bind world.view).toList.map fun (object, view) =>
              .writesObject entry object.allocationClass view.localAllocation
            let published := match action with | .publish _ => [.publication entry] | _ => []
            .point entry next after :: (record entry uses ++ written ++ published)
          | .error error => [.rejected entry.function pc error]
      | some (.invoke callee arguments destination next onAbort) =>
        match program.functions[callee]? with
        | none => [.rejected entry.function pc .missingInstruction]
        | some target =>
          match prepare target world arguments with
          | .error error => [.rejected entry.function pc error]
          | .ok prepared =>
            let called : Entry := ⟨callee, prepared.entered⟩
            .point called 0 prepared.entered ::
              known.flatMap (propagate program entry called pc next prepared destination onAbort)
      | some (.ret source) =>
        if world.scopes.isEmpty then
          match checkReturn program function entry.world world source with
          | .ok value => .returned entry source world value :: record entry (value.uses ++ survivingStores world source)
          | .error error => [.rejected entry.function pc error]
        else [.rejected entry.function pc .scopeOrder]
      | some .abort => abortFacts entry pc world
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
        rename_i callee arguments destination next onAbort
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
def entrySeed (entry : Entry) : List Judgment := [.point entry 0 entry.world]
def seed : List Judgment := entrySeed startEntry

def validSchemas (program : Program) : Bool :=
  decide ((program.slots.map (fun s => (s.site, s.field))).Nodup)

def validProgram (program : Program) : Bool :=
  (program.functions[0]?).any (fun f => f.parameters.isEmpty) && validSchemas program

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

def writeFootprint (function : Function) (facts : List Judgment) (entry : Entry) : List AllocationClass :=
  let writable := function.parameters.zipIdx.filterMap (fun (mode, formal) =>
    if (paramAccess mode).writes then entry.world.raw.get formal else none)
  let regions := (reachable entry.world.raw.memory.heap writable).map Object.allocationClass
  facts.filterMap fun
    | .writesObject key object localAllocation =>
      if key == entry && !localAllocation && regions.contains object then some object else none
    | _ => none

structure WriteEvidence where
  grounded : Bool
  possible : Bool
  deriving Repr, DecidableEq

def parameterWrites (function : Function) (facts : List Judgment) (entry : Entry) : WriteEvidence :=
  let overlap := writeFootprint function facts entry
  let byAuthority := (entryUses facts entry).any (fun (formal, kind) =>
    kind == .write && (function.parameters[formal]?).any (fun mode => (paramAccess mode).writes))
  let grounded := byAuthority || overlap.any AllocationClass.singleton
  ⟨grounded, grounded || !overlap.isEmpty⟩

def checkInterface (program : Program) (facts : List Judgment) (entry : Entry) : Except Error Unit := do
  let function ← need program.functions[entry.function]? .missingInstruction
  let uses := entryUses facts entry
  require (function.parameters.zipIdx.all fun (mode, formal) =>
    match mode with
    | .mutable => uses.contains (formal, .write) || uses.contains (formal, .consume)
    | .retained => uses.contains (formal, .retain) || uses.contains (formal, .rootRetain) ||
      uses.contains (formal, .publish)
    | _ => true) .unusedParameter
  let writes := parameterWrites function facts entry
  require (writes.grounded == writes.possible) .uncertainWrite
  let retains := facts.contains (.publication entry) ||
    uses.any (fun (_, kind) => kind == .retain || kind == .publish)
  require (function.contract.writes == writes.grounded && function.contract.retains == retains &&
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
def checkEntry (program : Program) (entry : Entry) (budget : Nat := 256) : Except Diagnostic Certificate :=
  if validSchemas program then
    match saturate (expand program) budget (entrySeed entry) with
    | none => .error ⟨entry.function, 0, .analysisLimit⟩
    | some facts =>
      match (failures facts).head?.orElse (fun _ => interfaceFailure program facts) with
      | some diagnostic => .error diagnostic
      | none => .ok ⟨facts⟩
  else .error ⟨entry.function, 0, .invalidProgram⟩

def check (program : Program) (budget : Nat := 256) : Except Diagnostic Certificate :=
  if validProgram program then checkEntry program startEntry budget
  else .error ⟨0, 0, .invalidProgram⟩

end RilAccess.Provenance
