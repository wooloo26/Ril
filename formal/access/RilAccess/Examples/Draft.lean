import RilAccess.Draft.Boundary

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
def context : Context := ⟨42, 7, 0, 8⟩
def oldOrigin (object : Nat) : Origin := ⟨⟨.allocation, 1⟩, 1, object, 0, 1⟩
def outsideOrigin : Origin := ⟨⟨.module, 77⟩, 0, 9, 0, 0⟩

def input : Input :=
  { pool := [⟨oldOrigin 0, cellStorage, [.scalar 0 1]⟩,
      ⟨oldOrigin 1, arrayStorage, [.reference 0, .reference 3]⟩,
      ⟨oldOrigin 2, tupleStorage, [.reference 1, .reference 1]⟩,
      ⟨oldOrigin 3, cellStorage, [.scalar 0 7]⟩,
      ⟨oldOrigin 5, cellStorage, [.scalar 0 10]⟩],
    reserved := [0, 1, 2, 3, 5, 9], root := 2, context, outside := ⟨[], []⟩,
    schemas := [cellStorage, arrayStorage, tupleStorage],
    admissions := [0, 1, 2, 3, 5].map (fun object => (object, .immutable)),
    externalSources := [outsideOrigin.source] }

def done : RecipeStep := .finish .normal
def aborted : RecipeStep := .finish .abort
def grow : RecipeStep := .rewrite [0] [.reference 0, .reference 3, .reference 3]
def mutateInserted : RecipeStep := .rewrite [0, 1] [.scalar 0 8]
def outsideWrite : Event := ⟨.write, outsideOrigin, .cleanup⟩
def outsideCapture : Event := ⟨.capture, outsideOrigin, .closure⟩

/-- These external fixtures concern one scalar slot, with no hidden payload.
This helper is fixture data, not inference of a complete contract from an event. -/
def external (event : Event) : RecipeStep :=
  .external ⟨[event], [], .known ⟨[event.origin], [], []⟩⟩

def hiddenWrapper : ExternalObservation :=
  ⟨[outsideWrite], [], .known ⟨[outsideOrigin], [context.origin 11], []⟩⟩
def unknownBoundary : ExternalObservation :=
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
    pool := [⟨oldOrigin 2, tupleStorage, [.reference 1, .reference 6]⟩,
      ⟨oldOrigin 6, arrayStorage, [.reference 0, .reference 3]⟩] ++
      input.pool.filter (fun cell => decide (cell.origin.object ≠ 2)),
    reserved := 6 :: input.reserved, admissions := (6, .immutable) :: input.admissions }

def liveInput : Input := { input with outside := ⟨[⟨0, 3, .shared⟩], []⟩ }
def forgedStorage : Storage := .variable 100 scalarSlot
def cycleStorage : Storage := .fixed 400 [⟨.object 400, fixedMode⟩, scalarSlot]
def cyclic : Input :=
  { input with
    pool := [⟨oldOrigin 4, cycleStorage, [.reference 4, .scalar 0 1]⟩],
    root := 4, reserved := [4, 9], schemas := [cycleStorage], admissions := [(4, .immutable)] }

def entryStorage : Storage := .fixed 500 [scalarSlot, scalarSlot]
def mapStorage : Storage := .variable 600 ⟨.object 500, fixedMode⟩
def mapInput : Input :=
  { input with
    pool := [⟨oldOrigin 6, entryStorage, [.scalar 0 1, .scalar 0 10]⟩,
      ⟨oldOrigin 7, mapStorage, [.reference 6]⟩],
    root := 7, reserved := [6, 7, 9], schemas := [entryStorage, mapStorage],
    admissions := [(6, .immutable), (7, .immutable)] }
def mapInsert : List RecipeStep :=
  [.allocate entryStorage [.scalar 0 2, .scalar 0 20],
    .rewrite [] [.reference 6, .reference 11], done]
def setStorage : Storage := .variable 700 scalarSlot
def setInput : Input :=
  { input with
    pool := [⟨oldOrigin 8, setStorage, [.scalar 0 1, .scalar 0 2]⟩],
    root := 8, reserved := [8, 9], schemas := [setStorage], admissions := [(8, .immutable)] }

def fixtures : List (String × Bool) :=
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
      state [grow, external outsideWrite, aborted] == some [outsideWrite]),
   ("derive: captured external state survives abort",
      state [grow, external outsideCapture, aborted] == some [outsideCapture]),
   ("derive: external contract cannot write protected input", !accepted
      [external ⟨.write, oldOrigin 0, .call⟩, done]
      { input with externalSources := (oldOrigin 0).source :: input.externalSources }),
   ("derive: external source obligation cannot be omitted", !accepted
      [external outsideWrite, done] { input with externalSources := [] }),
   ("derive: abort publishes no result", accepted [grow, aborted] && (result [grow, aborted]).isNone),
   ("derive: abort preserves every base entry", contents [grow, mutateInserted, aborted] 1 ==
      some [.reference 0, .reference 3] && contents [grow, mutateInserted, aborted] 3 == some [.scalar 0 7]),
   ("derive: recipe effects remain on abort",
       ((checkRecipe input [.effect 5, grow, aborted]).map (fun a => a.result.effects)) == some [5]),
   ("derive: outside environment blocks local discharge",
      (state [grow, done] { input with environments := [outsideOrigin] }).any (fun events => !events.isEmpty)),
    ("derive: source object cannot be written", !(check input [.rewrite 1 [], .finish .normal]).isSome),
    ("derive: fixed tuple arity cannot shrink", !accepted [.rewrite [] [.reference 1], done]),
    ("derive: fixed tuple arity cannot grow", !accepted [.rewrite [] [.reference 1, .reference 1, .reference 1], done]),
    ("derive: homogeneous element type enforced", !accepted [.rewrite [0] [.reference 1], done]),
    ("derive: scalar type enforced", !accepted [.rewrite [0, 0] [.scalar 1 2], done]),
    ("derive: invalid path rejected", !accepted [.rewrite [0, 2] [.scalar 0 2], done]),
   ("derive: live source writer rejects input", !accepted [done] liveInput),
   ("derive: readonly reception is not immutable reception", !accepted [done]
      { input with admissions := input.admissions.map (fun (object, _) => (object, .ref)) }),
   ("derive: missing reception evidence rejected", !accepted [done] { input with admissions := [] }),
   ("derive: inconsistent duplicate reception rejected", !accepted [done]
      { input with admissions := (0, .ref) :: input.admissions }),
   ("derive: draft capture escape rejected", !accepted [external ⟨.capture, context.origin 11, .closure⟩, done]),
   ("derive: draft retained writer escape rejected", !accepted [external ⟨.retain, context.origin 11, .call⟩, done]),
   ("derive: draft alias is unusable after publication", !accepted [done, grow]),
   ("derive: draft alias is unusable after abort", !accepted [aborted, grow]),
   ("derive: unclosed recipe rejected", !accepted [grow]),
   ("derive: undeclared schema cannot be injected", !accepted [.allocate forgedStorage [], done]),
   ("derive: inconsistent type-tag declarations rejected", !accepted [done]
      { input with schemas := forgedStorage :: input.schemas }),
   ("derive: dangling input reference rejected", !accepted [done]
      { input with pool := input.pool.filter (fun cell => decide (cell.origin.object ≠ 3)) }),
   ("derive: incomplete object reservation rejected", !accepted [done] { input with reserved := [0, 1, 2, 9] }),
   ("derive: outside future-identity alias rejected", !accepted [done]
      { input with outside := ⟨[⟨0, 11, .shared⟩], []⟩ }),
   ("derive: reused context cannot hide old state", !accepted [done]
      { input with context := { context with activation := 1, scope := 1 } }),
   ("derive: captured environment cannot reuse draft ownership", !accepted [done]
      { input with environments := [context.origin 9] }),
   ("derive: old wrapper event cannot hide a draft capture",
      !accepted [.external hiddenWrapper, done]),
   ("derive: unknown footprint remains an obligation", !accepted [.external unknownBoundary, done]),
   ("derive: known external effects propagate",
       ((checkRecipe input [.external ⟨[outsideWrite], [8], .known ⟨[outsideOrigin], [], []⟩⟩, done]).map
        (fun analysis => analysis.result.effects)) == some [8]),
   ("derive: source analysis includes actual local and external writes",
       (checkRecipe input [grow, external outsideWrite, aborted]).any fun analysis =>
         decide (Fact.event .write context.source ∈ analysis.facts ∧
           Fact.event .write outsideOrigin.source ∈ analysis.facts))]

theorem fixtures_all_pass : fixtures.all Prod.snd = true := by decide +kernel

end RilAccess.Draft.Examples
