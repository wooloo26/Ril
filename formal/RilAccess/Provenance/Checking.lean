import RilAccess.Provenance.Core
import RilAccess.Graph.Reachability

namespace RilAccess.Provenance

structure View where
  mode : Access
  qualified : Bool := false
  scopedHold : Bool := false
  dependencies : List Register := []
  formals : List Register := []
  /-- The object was allocated after this frame's entry. This witness is
      independent of the object's allocation-site class. -/
  localAllocation : Bool := false
  confined : Bool := false
  deriving Repr, DecidableEq

structure Retention where
  parent : Object
  field : Field
  formals : List Register
  retains : Bool
  localAllocation : Bool := false
  deriving Repr, DecidableEq

def Retention.sameSlot (left right : Retention) : Bool :=
  left.parent == right.parent && left.field == right.field

structure World where
  raw : RawFrame := {}
  views : List (Register × View) := []
  outside : List Object := []
  published : List Object := []
  stores : List Retention := []
  newSlots : List (Object × Field) := []
  scopes : List Register := []
  deriving Repr, DecidableEq

def World.view (world : World) (register : Register) : Option (Object × View) := do
  return (← world.raw.get register, ← getSlot world.views register)

def World.setView (world : World) (register : Register) (view : View) : World :=
  { world with views := putSlot world.views register view }

def World.endPath (world : World) (register : Register) : World :=
  let views := world.views.filter (fun (r, view) => r != register && !view.dependencies.contains register)
  { world with views }

def World.liveObjects (world : World) : List Object :=
  world.views.filterMap (fun (r, _) => world.raw.get r)

def World.outsideVisible (world : World) : List Object :=
  (world.outside ++ world.published).eraseDups

def World.remember (world : World) (store : Retention) (inNewSubgraph : Bool) : World :=
  let slot := (store.parent, store.field)
  let oldNewSlots := world.newSlots.filter (· != slot)
  let newSlots := if inNewSubgraph then slot :: oldNewSlots else oldNewSlots
  { world with stores := store :: world.stores.filter (fun old => !store.sameSlot old), newSlots }

abbrev reachable := Heap.reachable (Node := Object)
abbrev separated := Heap.separated (Node := Object)

/-- Handoff storage establishes new-subgraph inclusion independently of the
    slot's access mode. The first reception can freeze a fresh child. -/
def newLinks (newSlots : List (Object × Field)) (edges : List Link) : List Link :=
  edges.filter (fun edge => newSlots.contains (edge.parent.abstract, edge.field))

def newRegion (world : World) (root : Object) : List Object :=
  reachable (newLinks world.newSlots world.raw.memory.heap) [root]

def isolated (world : World) (root : Object) (outside : List Object) : Bool :=
  let outsideVisible := reachable world.raw.memory.heap outside
  (newRegion world root).all (fun o => !outsideVisible.contains o)

def boundaries (program : Program) (world : World) (object : Object) : List (Object × Access) :=
  let region := newRegion world object
  (world.raw.memory.heap.filterMap fun edge => do
    if !region.contains edge.parent || world.newSlots.contains (edge.parent.abstract, edge.field) then none else
      let schema ← program.slot edge.parent edge.field
      some (edge.child, schema.access)).eraseDups

def freezable (program : Program) (world : World) (object : Object) : Bool :=
  (boundaries program world object).all (fun (_, old) => old == .immutable)

def entryContains (entry : World) (formal : Register) (object : Object) : Bool :=
  object.singleton && (entry.raw.get formal).any (fun root =>
    (reachable (entry.raw.memory.heap.filter (fun edge =>
      edge.parent.singleton && edge.child.singleton)) [root]).contains object)

inductive Error where
  | invalidProgram
  | analysisLimit
  | missingInstruction
  | unavailable
  | access
  | schema
  | overlap
  | construction
  | returnSource
  | signature
  | unusedParameter
  | summarizedSlot
  | uncertainWrite
  | summaryEntry
  | scopeOrder
  deriving Repr, DecidableEq

def require (condition : Bool) (error : Error) : Except Error Unit :=
  if condition then .ok () else .error error

def need (value : Option α) (error : Error := .unavailable) : Except Error α :=
  match value with
  | some result => .ok result
  | none => .error error

def takeHandoff (world : World) (register : Register) :
    Except Error (Object × View × World) := do
  let (object, view) ← need (world.view register)
  let ended := world.endPath register
  require (view.qualified && !view.scopedHold &&
    isolated world object (ended.liveObjects ++ ended.outsideVisible)) .construction
  return (object, { view with dependencies := [] }, ended)

inductive UseKind where
  | write | handoff | retain | rootRetain | publish
  deriving Repr, DecidableEq

abbrev Use := Register × UseKind

def used (view : View) (kind : UseKind) : List Use :=
  view.formals.map (·, kind)

def survivingStores (world : World) (value : Option Register) : List Use :=
  let externallyVisible := reachable world.raw.memory.heap (world.outsideVisible ++ (value.bind world.raw.get).toList)
  world.stores.flatMap fun store =>
    if store.retains && externallyVisible.contains store.parent then store.formals.map (·, .retain) else []

def receive (view : View) (mode : Access) : Bool :=
  match mode with
  | .immutable => view.mode == .immutable
  | .ref => true
  | .mut => false
  | .shared => !view.scopedHold && (view.mode == .shared || view.qualified)

def metadata (program : Program) (action : Primitive) (world : World) : Except Error (World × List Use) := do
  match action with
  | .alloc destination _ =>
    return (world.setView destination { mode := .mut, qualified := true, localAllocation := true }, [])
  | .bind destination source mode =>
    let (_, view) ← need (world.view source)
    require (!view.confined && receive view mode) .access
    let dependencies := if mode == .ref then (source :: view.dependencies).eraseDups else []
    let bound := { view with mode, qualified := false, dependencies }
    return (world.setView destination bound, [])
  | .handoff destination source =>
    let (_, view, ended) ← takeHandoff world source
    return (ended.setView destination view, used view .handoff)
  | .store parent field source handoffSlot =>
    let (parentObj, holder) ← need (world.view parent)
    let (target, child) ← need (world.view source)
    require parentObj.singleton .summarizedSlot
    require holder.mode.writes .access
    let schema ← need (program.slot parentObj field) .schema
    let occupied := world.raw.memory.heap.any (Link.atSlot parentObj field)
    require (!occupied || schema.replaceable) .schema
    if handoffSlot then
      require (schema.access != .ref) .schema
      let (_, _, ended) ← takeHandoff world source
      require ((ended.view parent).isSome && parentObj != target) .construction
      if schema.access == .immutable then
        require (freezable program world target) .construction
      return (ended.remember ⟨parentObj, field, child.formals, false, child.localAllocation⟩ true,
        used holder .write ++ used child .handoff)
    else
      require (schema.access != .mut && schema.access == child.mode && !child.scopedHold &&
        (child.mode != .ref || child.dependencies.isEmpty)) .schema
      return (world.remember ⟨parentObj, field, child.formals, child.mode == .shared, child.localAllocation⟩ false,
        used holder .write)
  | .select destination parent field =>
    let (parentObj, holder) ← need (world.view parent)
    require parentObj.singleton .summarizedSlot
    let schema ← need (program.slot parentObj field) .schema
    let mode := attenuate holder.mode schema.access
    let dependencies := (parent :: holder.dependencies).eraseDups
    let stored := world.stores.find? (fun store => store.parent == parentObj && store.field == field)
    let formals := (stored.map Retention.formals).getD holder.formals
    let localAllocation := stored.any Retention.localAllocation
    let view := { holder with mode, qualified := false, dependencies, formals, localAllocation }
    return (world.setView destination view, [])
  | .read register =>
    let _ ← need (world.view register)
    return (world, [])
  | .write register =>
    let (_, view) ← need (world.view register)
    require view.mode.writes .access
    return (world, used view .write)
  | .publish register =>
    let (object, view) ← need (world.view register)
    require (view.mode == .shared && !view.scopedHold) .access
    return ({ world with published := (object :: world.published).eraseDups }, used view .publish)
  | .scope register =>
    let (_, view, ended) ← takeHandoff world register
    let opened := ended.setView register { view with qualified := false, scopedHold := true, confined := true }
    return ({ opened with scopes := register :: world.scopes }, [])
  | .expire register =>
    let (_, view) ← need (world.view register)
    require (view.confined && world.scopes.head? == some register) .scopeOrder
    return ({ world.endPath register with scopes := world.scopes.drop 1 }, [])

def availableDestination (action : Primitive) (world : World) : Bool :=
  action.destination.all (fun register => !world.scopes.contains register)

def primitive (program : Program) (action : Primitive) (world : World) :
    Except Error (World × List Use) := do
  require (availableDestination action world) .scopeOrder
  let (edited, uses) ← metadata program action world
  let raw ← need (runPrim action.erase world.raw)
  return ({ edited with raw := raw.abstract }, uses)

abbrev paramAccess := ParameterMode.access

def acceptsArgument (view : View) : ParameterMode → Bool
  | .observe => true
  | .mutable => view.mode == .mut
  | .retained => view.mode == .shared && !view.scopedHold
  | .immutable => view.mode == .immutable
  | .construction => view.mode == .mut && view.qualified && !view.scopedHold

abbrev Evaluated := Object × View × ParameterMode

def evaluateArguments : World → List Argument → Except Error (World × List Evaluated)
  | world, [] => .ok (world, [])
  | world, argument :: rest => do
    let (object, view) ← need (world.view argument.source)
    require (acceptsArgument view argument.marker) .access
    let next ← if argument.marker == .construction then
        (takeHandoff world argument.source).map (·.2.2)
      else pure world
    let (ended, evaluated) ← evaluateArguments next rest
    return (ended, (object, view, argument.marker) :: evaluated)

abbrev pairConflict := ParameterMode.conflicts

def separateArguments (heap : List Link) : List Evaluated → Bool
  | [] => true
  | (object, _, mode) :: rest =>
    rest.all (fun (other, _, otherMode) =>
      !pairConflict mode otherMode || separated heap [object] [other]) && separateArguments heap rest

structure Prepared where
  entered : World
  caller : World
  actuals : List Evaluated
  sources : List Register
  deriving Repr, DecidableEq

def formalView (mode : ParameterMode) (formal : Register) : View :=
  ⟨paramAccess mode, mode == .construction, mode == .mutable, [], [formal], false, false⟩

def prepare (function : Function) (caller : World) (arguments : List Argument) :
    Except Error Prepared := do
  require (decide (arguments.map Argument.marker = function.parameters)) .access
  let (afterEvaluation, actuals) ← evaluateArguments caller arguments
  require (separateArguments caller.raw.memory.heap actuals) .overlap
  let raw ← need (caller.raw.prepare (arguments.map Argument.source))
  let views := actuals.zipIdx.map fun ((_, argument, mode), formal) =>
    let received := formalView mode formal
    (formal, { received with scopedHold := received.scopedHold || argument.scopedHold, confined := argument.confined })
  let outside := (afterEvaluation.outsideVisible ++ afterEvaluation.liveObjects).eraseDups
  let entered : World := { raw, views, outside, newSlots := caller.newSlots }
  return ⟨entered, afterEvaluation, actuals, arguments.map Argument.source⟩

def formalMaySource (function : Function) (formal : Register) (mode : Access) : Bool :=
  match function.parameters[formal]? with
  | none => false
  | some parameter =>
    match mode with
    | .immutable => parameter == .immutable
    | .ref => parameter == .observe || parameter == .retained
    | .shared => parameter == .retained
    | .mut => false

def inferOld (function : Function) (entry : World) (target : Object × Access) : Option OldSource :=
  (function.parameters.zipIdx.find? (fun pair =>
    formalMaySource function pair.2 target.2 && entryContains entry pair.2 target.1)).map
      (fun pair => ⟨pair.2, target.2⟩)

structure Returned where
  root : Option View
  contained : List OldSource := []
  uses : List Use := []
  deriving Repr, DecidableEq

def checkReturn (program : Program) (function : Function) (entry world : World)
    (source : Option Register) : Except Error Returned := do
  match function.signature.result, source with
  | .unit, none => return ⟨none, [], []⟩
  | .plain, some register =>
    let (_, view) ← need (world.view register)
    require (view.mode == .immutable) .access
    return ⟨some view, [], []⟩
  | .observe formals, some register =>
    let (object, view) ← need (world.view register)
    let srcInsts := formals.filter (fun formal =>
      formalMaySource function formal .ref && entryContains entry formal object)
    require (view.mode == .ref && !view.confined && !srcInsts.isEmpty) .returnSource
    return ⟨some { view with formals := srcInsts }, [], []⟩
  | .retained formal, some register =>
    let (object, view) ← need (world.view register)
    require (view.mode == .shared && !view.scopedHold && formalMaySource function formal .shared &&
      entryContains entry formal object) .returnSource
    return ⟨some { view with formals := [formal] }, [], [(formal, .rootRetain)]⟩
  | .construction, some register =>
    let (object, view) ← need (world.view register)
    require (view.qualified && isolated world object world.outsideVisible) .construction
    let old ← need ((boundaries program world object).mapM (inferOld function entry)) .returnSource
    return ⟨some view, old, old.filterMap (fun s =>
      if s.mode == .shared then some (s.formal, .retain) else none)⟩
  | _, _ => throw .returnSource

def actualFormals (call : Prepared) (formals : List Register) : List Register :=
  (formals.flatMap fun formal =>
    (call.actuals[formal]?).toList.flatMap (fun (_, argument, _) => argument.formals)).eraseDups

def restoreMetadata (call : Prepared) (exited : World) : World :=
  let fresh := exited.stores.map (fun store => { store with formals := actualFormals call store.formals })
  let stores := fresh ++ call.caller.stores.filter (fun old => !(fresh.any (old.sameSlot ·)))
  let published := (exited.published ++ call.caller.published).eraseDups
  { call.caller with published, stores, newSlots := exited.newSlots }

def abortCall (call : Prepared) (exited : World) : World :=
  let restored := restoreMetadata call exited
  { restored with raw := { call.caller.raw with memory := exited.raw.memory } }

def receiveResult (program : Program) (call : Prepared) (exited : World) (result : Returned)
    (destination : Option (Register × Access)) (returned : Option Object) : Except Error World := do
  let restored := restoreMetadata call exited
  match destination, returned, result.root with
  | none, none, none => return restored
  | some (register, mode), some object, some view =>
    require (!restored.scopes.contains register) .scopeOrder
    if view.qualified then
      require (mode == .mut || mode == .shared || mode == .immutable) .access
      if mode == .immutable then
        require (freezable program exited object) .construction
    else
      require (mode == view.mode) .access
    let formals := actualFormals call view.formals
    let dependencies := if mode == .ref then
      (view.formals.flatMap fun formal =>
        (call.sources[formal]?).toList ++
          (call.actuals[formal]?).toList.flatMap (fun (_, argument, _) => argument.dependencies)).eraseDups
      else []
    let qualified := view.qualified && mode == .mut
    let scopedHold := mode == .ref && view.formals.any (fun formal =>
      (call.actuals[formal]?).any (fun (_, argument, _) => argument.scopedHold))
    let received := { view with mode, formals, dependencies, scopedHold, qualified }
    return restored.setView register received
  | _, _, _ => throw .returnSource

def resume (program : Program) (call : Prepared) (exited : World) (source : Option Register) (result : Returned)
    (destination : Option (Register × Access)) : Except Error World := do
  let returned ← need (exited.raw.returnValue source)
  let raw ← need (call.caller.raw.resume exited.raw.memory (destination.map Prod.fst) returned) .returnSource
  let received ← receiveResult program call exited result destination returned
  return { received with raw }

end RilAccess.Provenance
