import RilAccess.Draft.Lowering

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

namespace RilAccess.Draft.Examples

def fixedMode : MemberMode := ⟨false, .immutable⟩
def scalarSlot : Slot := ⟨.scalar 0, fixedMode⟩
def cellSlot : Slot := ⟨.object 100, fixedMode⟩
def arraySlot : Slot := ⟨.object 200, fixedMode⟩
def cellStorage : Storage := .fixed 100 [scalarSlot]
def arrayStorage : Storage := .variable 200 cellSlot
def tupleStorage : Storage := .fixed 300 [arraySlot, arraySlot]
def context : Context := ⟨42, 7, 8⟩
def existingInstance (object : Nat) : SourceInstance := ⟨⟨.allocation, 1⟩, 1, object, 1⟩
def outsideInstance : SourceInstance := ⟨⟨.module, 77⟩, 0, 9, 0⟩

def input : Input :=
  { pool := [⟨existingInstance 0, cellStorage, [.scalar 0 1]⟩,
      ⟨existingInstance 1, arrayStorage, [.reference 0, .reference 3]⟩,
      ⟨existingInstance 2, tupleStorage, [.reference 1, .reference 1]⟩,
      ⟨existingInstance 3, cellStorage, [.scalar 0 7]⟩,
      ⟨existingInstance 5, cellStorage, [.scalar 0 10]⟩],
    reserved := [0, 1, 2, 3, 5, 9], root := 2, context, outside := ⟨[], []⟩,
    schemas := [cellStorage, arrayStorage, tupleStorage],
    admissions := [0, 1, 2, 3, 5].map (fun object => (object, .immutable)),
    outsideSources := [outsideInstance.source] }

def done : RecipeStep := .finish .normal
def aborted : RecipeStep := .finish .abort
def grow : RecipeStep := .rewrite [0] [.reference 0, .reference 3, .reference 3]
def mutateInserted : RecipeStep := .rewrite [0, 1] [.scalar 0 8]
def outsideWrite : Event := ⟨.write, outsideInstance, .cleanup⟩
def outsideCapture : Event := ⟨.capture, outsideInstance, .closure⟩

/-- These external examples concern one scalar slot, with no hidden payload.
This helper is example data, not inference of a complete signature from an event. -/
def outsideStep (event : Event) : RecipeStep :=
  .outsideOp ⟨[event], [], .known ⟨[event.srcInst], [], []⟩⟩

def hiddenWrapper : OutsideObservation :=
  ⟨[outsideWrite], [], .known ⟨[outsideInstance], [context.srcInst 11], []⟩⟩
def unknownBoundary : OutsideObservation :=
  ⟨[outsideWrite], [], .unresolved [17]⟩


def accepted (recipe : List RecipeStep) (source : Input := input) : Bool := (checkRecipe source recipe).isSome

def contents (recipe : List RecipeStep) (object : Nat) (source : Input := input) : Option (List Value) := do
  let analysis ← checkRecipe source recipe
  return (← analysis.result.memory object).contents

def result (recipe : List RecipeStep) (source : Input := input) : Option Published := do
  let analysis ← checkRecipe source recipe
  analysis.result.output

def state (recipe : List RecipeStep) (source : Input := input) : Option (List Event) :=
  (checkRecipe source recipe).map (fun analysis => analysis.result.outward)

def valuesAt (heap : Heap) (object : Nat) : List Nat → Option (List Value)
  | [] => (heap object).map Cell.contents
  | index :: rest => do
    let cell ← heap object
    let .reference child ← cell.contents[index]? | none
    valuesAt heap child rest

def publishedContents (recipe : List RecipeStep) (path : List Nat) (source : Input := input) :
    Option (List Value) := do
  let analysis ← checkRecipe source recipe
  let output ← analysis.result.output
  valuesAt analysis.result.memory output.object path

def tupleUpdate : List RecipeStep :=
  [.allocate arrayStorage [], .rewrite [] [.reference 11, .reference 1], done]

def splitInput : Input :=
  { input with
    pool := [⟨existingInstance 2, tupleStorage, [.reference 1, .reference 6]⟩,
      ⟨existingInstance 6, arrayStorage, [.reference 0, .reference 3]⟩] ++
      input.pool.filter (fun cell => decide (cell.srcInst.object ≠ 2)),
    reserved := 6 :: input.reserved, admissions := (6, .immutable) :: input.admissions }

def liveInput : Input := { input with outside := ⟨[⟨0, 3, .shared⟩], []⟩ }
def forgedStorage : Storage := .variable 100 scalarSlot
def cycleStorage : Storage := .fixed 400 [⟨.object 400, fixedMode⟩, scalarSlot]
def cyclic : Input :=
  { input with
    pool := [⟨existingInstance 4, cycleStorage, [.reference 4, .scalar 0 1]⟩],
    root := 4, reserved := [4, 9], schemas := [cycleStorage], admissions := [(4, .immutable)] }

def entryStorage : Storage := .fixed 500 [scalarSlot, scalarSlot]
def mapStorage : Storage := .variable 600 ⟨.object 500, fixedMode⟩
def mapInput : Input :=
  { input with
    pool := [⟨existingInstance 6, entryStorage, [.scalar 0 1, .scalar 0 10]⟩,
      ⟨existingInstance 7, mapStorage, [.reference 6]⟩],
    root := 7, reserved := [6, 7, 9], schemas := [entryStorage, mapStorage],
    admissions := [(6, .immutable), (7, .immutable)] }
def mapInsert : List RecipeStep :=
  [.allocate entryStorage [.scalar 0 2, .scalar 0 20],
    .rewrite [] [.reference 6, .reference 11], done]
def setStorage : Storage := .variable 700 scalarSlot
def setInput : Input :=
  { input with
    pool := [⟨existingInstance 8, setStorage, [.scalar 0 1, .scalar 0 2]⟩],
    root := 8, reserved := [8, 9], schemas := [setStorage], admissions := [(8, .immutable)] }

def withExtraObject (cell : Cell) : Input :=
  let object := cell.srcInst.object
  { input with
    pool := cell :: input.pool,
    reserved := object :: input.reserved, schemas := cell.storage :: input.schemas,
    admissions := (object, .immutable) :: input.admissions }

def emptyRecordInput : Input := withExtraObject ⟨existingInstance 4, .fixed 800 [], []⟩

def rejectsRoot (shape : RootShape) (value : Value) (source : Input) : Bool :=
  match prepareRoot shape value source with
  | .error .invalidDeriveInput => true
  | .ok _ => false

def viaSnapshotDomains : List (String × List (List String)) :=
  let memberModes : List (String × Access) :=
    [("Plain", .immutable), ("Ref", .ref), ("Mut", .mut), ("Shared", .shared)]
  -- A new-qualified parameter still needs explicit handoff before it is frozen.
  let rootModes := memberModes ++ [("New", .mut)]
  let admits := fun access =>
    let candidate := { emptyRecordInput with
      admissions := emptyRecordInput.admissions.map fun (object, current) =>
        (object, if object == 4 then access else current) }
    (prepareRoot (.record 800) (.reference 4) candidate).isOk
  let roots := rootModes.filterMap fun (name, access) =>
    if admits access then some [name] else none
  let projected := rootModes.flatMap fun (root, rootAccess) =>
    memberModes.filterMap fun (member, memberAccess) =>
      if admits (attenuate rootAccess memberAccess) then some [root, member] else none
  [("root", roots), ("member", projected)]

theorem via_snapshot_domains_include_immutable_projection :
    viaSnapshotDomains.map (fun (_, rows) => rows.length) = [1, 8] := by decide +kernel

def sourceChecks : List (String × Bool) :=
  let record := { input with root := 0 }
  let sources (access : Access) : Input := { input with
    admissions := [0, 1, 2, 3].map (fun object => (object, Access.immutable)) ++ [(5, access)]
    outside := ⟨[⟨1, 5, access⟩], []⟩ }
  let wrapper := { sources .shared with
    root := 6
    pool := ⟨existingInstance 6, .fixed 900 [cellSlot], [.reference 0]⟩ :: input.pool
    reserved := 6 :: input.reserved
    schemas := .fixed 900 [cellSlot] :: input.schemas
    admissions := (6, .immutable) :: (sources .shared).admissions }
  [("derive_rejects_unit_as_a_root",
      (prepareRoot .unit (unitValue 4) emptyRecordInput).isOk),
   ("derive_rejects_a_callable_root",
      (prepareRoot .ineligible (.reference 4) emptyRecordInput).isOk),
   ("derive_requires_immutable_reception_compile_ref",
      (prepareRoot (.record 100) (.reference 0)
        { record with admissions := record.admissions.map (fun (object, access) =>
          (object, if object == 0 then .ref else access)) }).isOk),
   ("derive_requires_immutable_reception_compile_mut",
      (prepareRoot (.record 100) (.reference 0)
        { record with outside := ⟨[⟨0, 0, .mut⟩], []⟩ }).isOk),
   ("derive_rejects_inserting_a_live_value",
      accepted [.rewrite [] [.reference 5, .reference 3], done]
        { sources .ref with root := 1 }),
   ("derive_rejects_live_shared_field_replacement",
      accepted [.rewrite [] [.reference 5], done] wrapper),
   ("derive_rejects_live_shared_array_insertion",
      accepted [.rewrite [] [.reference 0, .reference 3, .reference 5], done]
        { sources .shared with root := 1 }),
   ("calling_a_unit_constructor_is_not_unit_payload_syntax",
      (lowerUnitVariant 4 (existingInstance 5) (.tag 802) .unitCall).isOk),
   ("derive_preserves_the_array_element_type",
      accepted [.rewrite [] [.scalar 0 1, .scalar 1 2], done] setInput)]

def scalarMember (values : List Value) (index : Nat) : Option Nat := do
  let .scalar _ payload ← values[index]? | none
  return payload

def arrayCounts (heap : Heap) (object : Nat) (path : List Nat) : Option (List Nat) := do
  let entries ← valuesAt heap object path
  entries.mapM fun entry => do
    let .reference id ← some entry | none
    scalarMember (← valuesAt heap id []) 0

def runtimeObservations : List (String × Option (List Nat)) :=
  let original := { input with pool := input.pool.map fun cell =>
    if cell.srcInst.object == 1 then { cell with contents := [.reference 0] } else cell }
  [("draft_updates_only_the_selected_occurrence", do
      let analysis ← checkRecipe original [grow, mutateInserted, done]
      let output ← analysis.result.output
      let memory := analysis.result.memory
      let base0 ← arrayCounts memory 2 [0]
      let base1 ← arrayCounts memory 2 [1]
      let updated0 ← arrayCounts memory output.object [0]
      let updated1 ← arrayCounts memory output.object [1]
      let outside ← scalarMember (← valuesAt memory 3 []) 0
      return [base0.length, base1.length, updated0.length, updated1.length,
        ← updated0[1]?, ← updated0[2]?, outside]),
   ("draft_inserts_map_entry_without_changing_base", do
      let analysis ← checkRecipe mapInput mapInsert
      let output ← analysis.result.output
      let memory := analysis.result.memory
      return [(← valuesAt memory 7 []).length, (← valuesAt memory output.object []).length,
        ← scalarMember (← valuesAt memory output.object [0]) 1,
        ← scalarMember (← valuesAt memory output.object [1]) 1]),
   ("draft_can_replace_a_fixed_tuple_member_with_a_shorter_array", do
      let analysis ← checkRecipe input [.rewrite [0] [.reference 3], done]
      let output ← analysis.result.output
      let memory := analysis.result.memory
      let base ← arrayCounts memory 2 [0]
      let updated0 ← arrayCounts memory output.object [0]
      let updated1 ← arrayCounts memory output.object [1]
      return [base.length, updated0.length, updated1.length, ← updated0[0]?]),
   ("draft_writes_to_the_current_path_after_reordering", do
      let analysis ← checkRecipe input [.rewrite [0] [.reference 3, .reference 0],
        .rewrite [0, 1] [.scalar 0 2], done]
      let output ← analysis.result.output
      let memory := analysis.result.memory
      return (← arrayCounts memory 2 [0]) ++
        (← arrayCounts memory output.object [0]) ++ (← arrayCounts memory output.object [1])),
   ("aborted_draft_preserves_the_base_and_inserted_source", do
      let analysis ← checkRecipe input [grow, mutateInserted, aborted]
      if analysis.result.output.isSome then none else
        let memory := analysis.result.memory
        let base ← arrayCounts memory 2 [0]
        let outside ← scalarMember (← valuesAt memory 3 []) 0
        return base.length :: base ++ [outside]),
   ("aborted_draft_dispatches_body_and_cleanup_effects", do
      let cleanup : OutsideObservation := ⟨[], [8], .known ⟨[], [], []⟩⟩
      let analysis ← checkRecipe input [.effect 5, grow, .outsideOp cleanup, aborted]
      if analysis.result.output.isSome then none else
        -- The summary records an effect set. The runtime suite checks the order.
        some (analysis.result.effects.mergeSort (· ≤ ·)))]

theorem source_checks_all_reject : sourceChecks.all (fun (_, ok) => !ok) = true := by decide +kernel
theorem runtime_observations_all_available : runtimeObservations.all (·.2.isSome) = true := by decide +kernel

def loweringExamples : List (String × Bool) :=
  let unit := unitValue 4
  let someUnit := lowerUnitVariant 4 (existingInstance 4) (.payload 801) .unitCall
  let noneTag := lowerUnitVariant 4 (existingInstance 5) (.tag 802) .bare
  [("lowering: unit is a tuple with no shared-object tag",
      RootShape.unit.isTuple && RootShape.unit.objectTag.isNone),
    ("lowering: Some() lowers to unit payload while bare Some is callable",
      someUnit.toOption.map Cell.contents == some [unit] &&
        (match lowerUnitVariant 4 (existingInstance 4) (.payload 801) .bare with
         | .error .callableValue => true
         | _ => false)),
    ("lowering: None has no payload while None() is rejected (E0338)",
      noneTag.toOption.map Cell.contents == some [] &&
        (match lowerUnitVariant 4 (existingInstance 5) (.tag 802) .unitCall with
         | .error .nullaryVariantArgument => true
         | _ => false)),
    ("derive: unit is rejected even with a matching heap number",
      rejectsRoot .unit unit emptyRecordInput &&
        rejectsRoot .unit (.reference 4) emptyRecordInput &&
        rejectsRoot (.record 800) unit emptyRecordInput),
    ("derive: empty record is prepared from the operand, not the supplied root",
      match prepareRoot (.record 800) (.reference 4) emptyRecordInput with
      | .ok world => world.input.root == 4 && result [done] world.input == some ⟨4, .immutable⟩
      | .error _ => false),
    ("derive: Some() has a sum object root",
      match someUnit with
      | .ok cell =>
        match prepareRoot (.sum 801) (.reference 4) (withExtraObject cell) with
        | .ok world => result [done] world.input == some ⟨4, .immutable⟩
        | .error _ => false
      | .error _ => false),
    ("derive: root schema and immutable reception are both checked",
      let live := { emptyRecordInput with outside := ⟨[⟨0, 4, .shared⟩], []⟩ }
      rejectsRoot (.record 801) (.reference 4) emptyRecordInput &&
        rejectsRoot (.record 800) (.reference 9) emptyRecordInput &&
        rejectsRoot (.record 800) (.reference 4) live)]

def examples : List (String × Bool) :=
  [("derive: tuple member replacement accepted", accepted tupleUpdate),
   ("derive: tuple declaration modes survive the draft",
       ((checkRecipe input tupleUpdate).bind (fun a => (a.result.memory 10).map Cell.storage)) == some tupleStorage),
   ("derive: tuple base snapshot preserved", contents tupleUpdate 2 == some [.reference 1, .reference 1]),
    ("derive: changed root is fresh and immutable", result tupleUpdate == some ⟨10, .immutable⟩),
   ("derive: array length can grow", accepted [grow, done] &&
       publishedContents [grow, done] [0] == some [.reference 0, .reference 3, .reference 3]),
    ("derive: array length can shrink",
       publishedContents [.rewrite [0] [.reference 3], done] [0] == some [.reference 3]),
    ("derive: array order can change",
       publishedContents [.rewrite [0] [.reference 3, .reference 0], done] [0] ==
         some [.reference 3, .reference 0]),
    ("derive: a path selects the current entry after reordering",
       publishedContents [.rewrite [0] [.reference 3, .reference 0],
         .rewrite [0, 1] [.scalar 0 2], done] [0, 1] == some [.scalar 0 2]),
   ("derive: homogeneous map-entry representation permits insertion",
       publishedContents mapInsert [] mapInput == some [.reference 6, .reference 11] &&
      contents mapInsert 7 mapInput == some [.reference 6]),
   ("derive: homogeneous set-member representation permits growth",
       publishedContents [.rewrite [] [.scalar 0 1, .scalar 0 2, .scalar 0 3], done] [] setInput ==
        some [.scalar 0 1, .scalar 0 2, .scalar 0 3]),
   ("derive: base keeps original order and length", contents [grow, done] 1 == some [.reference 0, .reference 3]),
    ("derive: shared and separately stored fields have the same path update",
       [input, splitInput].all fun source =>
         publishedContents [grow, done] [0] source == some [.reference 0, .reference 3, .reference 3] &&
         publishedContents [grow, done] [1] source == some [.reference 0, .reference 3]),
    ("derive: updates one occurrence of an inserted value",
       publishedContents [grow, mutateInserted, done] [0, 1] == some [.scalar 0 8] &&
       publishedContents [grow, mutateInserted, done] [0, 2] == some [.scalar 0 7]),
   ("derive: inserted immutable source remains unchanged",
      contents [grow, mutateInserted, done] 3 == some [.scalar 0 7]),
   ("derive: immutable insertion from outside the original root graph",
       publishedContents [.rewrite [0] [.reference 0, .reference 5],
         .rewrite [0, 1] [.scalar 0 11], done] [0, 1] == some [.scalar 0 11]),
    ("derive: finite path update through a cycle keeps its old suffix",
       publishedContents [.rewrite [0] [.reference 4, .scalar 0 2], done] [0] cyclic ==
         some [.reference 4, .scalar 0 2] &&
       publishedContents [.rewrite [0] [.reference 4, .scalar 0 2], done] [0, 0] cyclic ==
         some [.reference 4, .scalar 0 1]),
   ("derive: no-op can preserve original root", result [done] == some ⟨2, .immutable⟩),
    ("derive: no-op infers no state events",
       (checkRecipe input [done]).any (fun analysis => analysis.facts.isEmpty)),
   ("derive: ordinary local draft writes discharge", state [grow, done] == some []),
   ("derive: external cleanup writes survive abort",
      state [grow, outsideStep outsideWrite, aborted] == some [outsideWrite]),
   ("derive: captured external state survives abort",
      state [grow, outsideStep outsideCapture, aborted] == some [outsideCapture]),
   ("derive: external operation cannot write protected input", !accepted
      [outsideStep ⟨.write, existingInstance 0, .call⟩, done]
      { input with outsideSources := (existingInstance 0).source :: input.outsideSources }),
   ("derive: external source obligation cannot be omitted", !accepted
      [outsideStep outsideWrite, done] { input with outsideSources := [] }),
   ("derive: abort publishes no result", accepted [grow, aborted] && (result [grow, aborted]).isNone),
   ("derive: abort preserves every base entry", contents [grow, mutateInserted, aborted] 1 ==
      some [.reference 0, .reference 3] && contents [grow, mutateInserted, aborted] 3 == some [.scalar 0 7]),
   ("derive: recipe effects remain on abort",
       ((checkRecipe input [.effect 5, grow, aborted]).map (fun a => a.result.effects)) == some [5]),
   ("derive: outside environment blocks local discharge",
      (state [grow, done] { input with environments := [outsideInstance] }).any (fun events => !events.isEmpty)),
    ("derive: source object cannot be written", !(check input [.rewrite 1 [], .finish .normal]).isSome),
    ("derive: fixed tuple arity cannot shrink", !accepted [.rewrite [] [.reference 1], done]),
    ("derive: fixed tuple arity cannot grow", !accepted [.rewrite [] [.reference 1, .reference 1, .reference 1], done]),
    ("derive: homogeneous element type enforced", !accepted [.rewrite [0] [.reference 1], done]),
    ("derive: scalar type enforced", !accepted [.rewrite [0, 0] [.scalar 1 2], done]),
    ("derive: invalid path rejected", !accepted [.rewrite [0, 2] [.scalar 0 2], done]),
   ("derive: live source writer rejects input", !accepted [done] liveInput),
   ("derive: readonly reception is not immutable reception", !accepted [done]
      { input with admissions := input.admissions.map (fun (object, _) => (object, .ref)) }),
   ("derive: missing reception proof rejected", !accepted [done] { input with admissions := [] }),
   ("derive: inconsistent duplicate reception rejected", !accepted [done]
      { input with admissions := (0, .ref) :: input.admissions }),
   ("derive: draft capture escape rejected", !accepted [outsideStep ⟨.capture, context.srcInst 11, .closure⟩, done]),
   ("derive: draft retained writer escape rejected", !accepted [outsideStep ⟨.retain, context.srcInst 11, .call⟩, done]),
   ("derive: draft alias is unusable after publication", !accepted [done, grow]),
   ("derive: draft alias is unusable after abort", !accepted [aborted, grow]),
   ("derive: unclosed recipe rejected", !accepted [grow]),
   ("derive: undeclared schema cannot be injected", !accepted [.allocate forgedStorage [], done]),
   ("derive: inconsistent type-tag declarations rejected", !accepted [done]
      { input with schemas := forgedStorage :: input.schemas }),
   ("derive: dangling input reference rejected", !accepted [done]
      { input with pool := input.pool.filter (fun cell => decide (cell.srcInst.object ≠ 3)) }),
   ("derive: incomplete object reservation rejected", !accepted [done] { input with reserved := [0, 1, 2, 9] }),
   ("derive: outside future-identity alias rejected", !accepted [done]
      { input with outside := ⟨[⟨0, 11, .shared⟩], []⟩ }),
   ("derive: reused context cannot hide old state", !accepted [done]
      { input with context := { context with activation := 1, scope := 1 } }),
   ("derive: captured environment cannot reuse draft allocation context", !accepted [done]
      { input with environments := [context.srcInst 9] }),
   ("derive: old wrapper event cannot hide a draft capture",
      !accepted [.outsideOp hiddenWrapper, done]),
   ("derive: unknown footprint remains an obligation", !accepted [.outsideOp unknownBoundary, done]),
   ("derive: known external effects propagate",
       ((checkRecipe input [.outsideOp ⟨[outsideWrite], [8], .known ⟨[outsideInstance], [], []⟩⟩, done]).map
        (fun analysis => analysis.result.effects)) == some [8]),
   ("derive: source analysis includes actual local and external writes",
       (checkRecipe input [grow, outsideStep outsideWrite, aborted]).any fun analysis =>
         decide (Fact.event .write context.source ∈ analysis.facts ∧
           Fact.event .write outsideInstance.source ∈ analysis.facts))]

theorem examples_all_pass : examples.all Prod.snd = true := by decide +kernel

end RilAccess.Draft.Examples
