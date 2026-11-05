import RilAccess.Graph.Identity

/-! Finite path updates over immutable snapshots. The draft owns its root and
copies the selected descendants on each write. -/
namespace RilAccess.Draft

inductive DataType where
  | scalar (tag : Nat)
  | object (tag : Nat)
  deriving Repr, DecidableEq

structure Slot where
  dataType : DataType
  mode : MemberMode
  deriving Repr, DecidableEq

/-- Fixed storage covers resolved products/selected variants. Variable storage
covers an ordered homogeneous entry representation of arrays, maps and sets. -/
inductive Storage where
  | fixed (tag : Nat) (members : List Slot)
  | variable (tag : Nat) (element : Slot)
  deriving Repr, DecidableEq

def Storage.tag : Storage → Nat
  | .fixed tag _ | .variable tag _ => tag

def Storage.member : Storage → Nat → Option Slot
  | .fixed _ members, index => members[index]?
  | .variable _ element, _ => some element

inductive Value where
  | scalar (tag payload : Nat)
  | reference (object : Nat)
  deriving Repr, DecidableEq

structure Cell where
  origin : Origin
  storage : Storage
  contents : List Value
  deriving Repr, DecidableEq

abbrev Heap := Nat → Option Cell

def lookup (pool : List Cell) (object : Nat) : Option Cell :=
  pool.find? (fun cell => decide (cell.origin.object = object))

def put (heap : Heap) (object : Nat) (cell : Cell) : Heap :=
  fun selected => if selected = object then some cell else heap selected

def valueFits (heap : Heap) : DataType → Value → Bool
  | .scalar expected, .scalar actual _ => decide (expected = actual)
  | .object expected, .reference object =>
    (heap object).any (fun cell => decide (cell.storage.tag = expected))
  | _, _ => false

def contentsFit (heap : Heap) : Storage → List Value → Bool
  | .fixed _ members, values =>
    decide (members.length = values.length) &&
      (members.zip values).all (fun (member, value) => valueFits heap member.dataType value)
  | .variable _ element, values => values.all (valueFits heap element.dataType)

structure Context where
  producer : Nat
  activation : Nat
  task : Nat
  scope : Nat
  deriving Repr, DecidableEq

def Context.source (context : Context) : Source := ⟨.allocation, context.producer⟩

def Context.origin (context : Context) (object : Nat) : Origin :=
  ⟨context.source, context.activation, object, context.task, context.scope⟩

structure Input where
  pool : List Cell
  reserved : List Nat
  root : Nat
  context : Context
  outside : GraphAuthority.Graph Nat
  schemas : List Storage := []
  admissions : List (Nat × Access) := []
  environments : List Origin := []
  externalSources : List Source := []

def Input.bound (input : Input) : Nat := allocationBound input.reserved

def Input.draftRoot (input : Input) : Nat := input.bound

def copyRoot (input : Input) (cell : Cell) : Cell :=
  { cell with origin := input.context.origin input.draftRoot }

def inputEdges (input : Input) : List (GraphAuthority.Edge Nat) :=
  input.pool.flatMap fun cell => cell.contents.zipIdx |>.filterMap fun (value, index) =>
    match value, cell.storage.member index with
    | .reference child, some member =>
      some ⟨cell.origin.object, index, child, member.mode, member.mode.access⟩
    | _, _ => none

/-- The outside graph must cover all actual independent authority roots/paths.
The kernel computes consistency; it does not assume a supplied safety flag. -/
def Input.authorityGraph (input : Input) : GraphAuthority.Graph Nat :=
  ⟨input.outside.roots ++ input.pool.map (fun cell =>
      ⟨allocationBound (input.outside.roots.map GraphAuthority.Root.view) + cell.origin.object,
        cell.origin.object, .immutable⟩),
    input.outside.edges ++ inputEdges input⟩

def Input.authoritiesReserved (input : Input) : Bool :=
  input.outside.roots.all (fun root => decide (root.object ∈ input.reserved)) &&
  input.outside.edges.all (fun edge => decide (edge.parent ∈ input.reserved ∧ edge.child ∈ input.reserved)) &&
  input.environments.all (fun origin => decide (origin.object ∈ input.reserved) &&
    !owned input.context.activation input.context.task input.context.scope origin)

def Input.schemasValid (input : Input) : Bool :=
  decide ((input.schemas.map Storage.tag).Nodup) &&
    input.pool.all (fun cell => decide (cell.storage ∈ input.schemas))

/-- Normalized starting reception modes, not caller-supplied isolation flags.
The caller/lowering must establish that these are the actual received modes. -/
def Input.receptionsValid (input : Input) : Bool :=
  decide ((input.admissions.map Prod.fst).Nodup) &&
  input.admissions.all (fun (object, access) => decide (access = .immutable ∧
    object ∈ input.pool.map (fun cell => cell.origin.object))) &&
  input.pool.all (fun cell => input.admissions.any (fun (object, access) =>
    decide (object = cell.origin.object ∧ access = .immutable)))

def Input.valid (input : Input) : Bool :=
  decide ((input.pool.map (fun cell => cell.origin.object)).Nodup) &&
  input.pool.all (fun cell =>
    decide (cell.origin.object ∈ input.reserved) &&
    !owned input.context.activation input.context.task input.context.scope cell.origin &&
    contentsFit (lookup input.pool) cell.storage cell.contents) &&
  (lookup input.pool input.root).isSome &&
  GraphAuthority.immutableConsistent input.authorityGraph &&
    (input.authoritiesReserved && (input.schemasValid && input.receptionsValid))

def initialHeap (input : Input) : Heap :=
  fun object => if object < input.bound then lookup input.pool object
    else if object = input.draftRoot then (lookup input.pool input.root).map (copyRoot input)
    else none

structure Published where
  object : Nat
  access : Access
  deriving Repr, DecidableEq

inductive FootprintKnowledge where
  | known (footprint : Footprint)
  | unresolved (obligations : List Nat)
  deriving Repr, DecidableEq

structure ExternalObservation where
  events : List Event
  effects : List Nat
  footprint : FootprintKnowledge
  deriving Repr, DecidableEq

def ExternalObservation.known (observation : ExternalObservation) : Bool :=
  match observation.footprint with
  | .known _ => true
  | .unresolved _ => false

/-- Truthfulness/completeness belongs to the checked caller or external body.
Unknown footprints cannot establish this premise. -/
def ExternalConforms (observation : ExternalObservation) (actualEvents : List Event)
    (actualEffects : List Nat) (actualFootprint : Footprint) : Prop :=
  (∀ event ∈ actualEvents, event ∈ observation.events) ∧
  (∀ effect ∈ actualEffects, effect ∈ observation.effects) ∧
  match observation.footprint with
  | .known footprint => FootprintCovers footprint actualFootprint
  | .unresolved _ => False

structure World where
  input : Input
  memory : Heap
  locals : List Nat := []
  nextObject : Nat
  active : Bool := true
  dirty : Bool := false
  events : List Event := []
  effects : List Nat := []
  output : Option Published := none
  observations : List ExternalObservation := []

def World.draftObjects (world : World) : List Nat :=
  world.input.draftRoot :: world.locals

def prepare (input : Input) : Option World :=
  if input.valid then some ⟨input, initialHeap input, [], input.draftRoot + 1,
    true, false, [], [], none, []⟩ else none

def confinedValue (world : World) : Value → Bool
  | .scalar _ _ => true
  | .reference object => (lookup world.input.pool object).isSome ||
    decide (object ∈ world.locals)

inductive Exit where
  | normal | abort
  deriving Repr, DecidableEq

/-- External events observe separately checked boundary operations; they do not
execute or grant authority to an external body. Its complete access, alias and
lifetime obligations remain a caller/implementation conformance condition. -/
inductive Command where
  | rewrite (object : Nat) (contents : List Value)
  | allocate (storage : Storage) (contents : List Value)
  | external (observation : ExternalObservation)
  | effect (effect : Nat)
  | finish (reason : Exit)
  deriving Repr, DecidableEq

def rewritten (world : World) (object : Nat) (cell : Cell) (contents : List Value) : World :=
  { world with
    memory := put world.memory object { cell with contents }, dirty := true,
    events := ⟨.write, cell.origin, .derive⟩ :: world.events }

def allocated (world : World) (storage : Storage) (contents : List Value) : World :=
  let cell : Cell := ⟨world.input.context.origin world.nextObject, storage, contents⟩
  { world with
    memory := put world.memory world.nextObject cell,
    locals := world.nextObject :: world.locals, nextObject := world.nextObject + 1,
    events := ⟨.write, cell.origin, .derive⟩ :: world.events }

def observed (world : World) (observation : ExternalObservation) : World :=
  { world with
    events := observation.events ++ world.events,
    effects := observation.effects ++ world.effects, observations := observation :: world.observations }

def finished (world : World) (reason : Exit) : World :=
  { world with active := false, output := match reason with
      | .abort => none
      | .normal => some ⟨if world.dirty then world.input.draftRoot else world.input.root, .immutable⟩ }

/-- Independent graph execution ignores authority, type and phase guards. -/
def execute (command : Command) (world : World) : Option World :=
  match command with
  | .rewrite object contents => (world.memory object).map (fun cell => rewritten world object cell contents)
  | .allocate storage contents => some (allocated world storage contents)
  | .external observation => some (observed world observation)
  | .effect effect => some { world with effects := effect :: world.effects }
  | .finish reason => some (finished world reason)

/-- External contracts cannot write, retain a writer to, or transfer an input
object. Reads/captures of an already immutable input preserve its snapshot. -/
def externalPreservesInputs (input : Input) (event : Event) : Bool :=
  match event.kind with
  | .write | .retain | .transfer => decide (event.origin.object ∉ input.pool.map (fun cell => cell.origin.object))
  | _ => true

def eventAllowed (input : Input) (event : Event) : Bool :=
  decide (event.origin.object ∈ input.reserved ∧ event.origin.source ∈ input.externalSources) &&
    !owned input.context.activation input.context.task input.context.scope event.origin &&
    externalPreservesInputs input event

def observationAllowed (input : Input) (observation : ExternalObservation) : Bool :=
  match observation.footprint with
  | .unresolved _ => false
  | .known footprint =>
    observation.events.all (eventAllowed input) &&
    (footprint.roots ++ footprint.environments ++ footprint.escaping).all (fun origin =>
      decide (origin.object ∈ input.reserved) &&
        !owned input.context.activation input.context.task input.context.scope origin) &&
    Identity.coherent (input.pool.map Cell.origin ++ input.environments ++
      observation.events.map Event.origin ++ footprint.roots ++ footprint.environments ++ footprint.escaping)

/-- Local guards, never a caller-provided global safety certificate. -/
def admissible (command : Command) (world : World) : Bool :=
  world.active && match command with
  | .rewrite object contents => (world.memory object).any fun cell =>
    decide (object = world.input.draftRoot ∧ world.input.bound ≤ object) &&
    decide (cell.origin = world.input.context.origin object) &&
    contentsFit world.memory cell.storage contents && contents.all (confinedValue world)
  | .allocate storage contents =>
    let candidate := allocated world storage contents
    decide (storage ∈ world.input.schemas) &&
      (decide (world.input.bound ≤ world.nextObject) && (world.memory world.nextObject).isNone &&
        contentsFit candidate.memory storage contents && contents.all (confinedValue candidate))
  | .external observation => observationAllowed world.input observation
  | .effect _ | .finish .abort => true
  | .finish .normal =>
    (world.memory (if world.dirty then world.input.draftRoot else world.input.root)).isSome

def step (command : Command) (world : World) : Option World :=
  if admissible command world then execute command world else none

inductive Trace (program : List Command) : World → World → Prop where
  | refl : Trace program world world
  | tail : Trace program start middle → command ∈ program →
      step command middle = some next → Trace program start next

def World.footprint (world : World) : Footprint :=
  ⟨world.draftObjects.map world.input.context.origin, world.input.environments, []⟩

def World.outward (world : World) : List Event :=
  if world.observations.all ExternalObservation.known then
    discharge world.input.context.activation world.input.context.task world.input.context.scope
      world.footprint world.events
  else world.events

/-- A finite source bound for memory and outputs, not a grant of authority. -/
def Input.sources (input : Input) : List Source :=
  input.context.source :: input.pool.map (fun cell => cell.origin.source)

def commandRules (input : Input) : Command → List (Rule Fact)
  | .rewrite _ _ | .allocate _ _ => [⟨[], .event .write input.context.source⟩]
  | .external observation => observation.events.map (fun event => ⟨[], .event event.kind event.origin.source⟩)
  | _ => []

def analyze (input : Input) (program : List Command) : List Fact :=
  solve (program.flatMap (commandRules input))

def runUnchecked : List Command → World → Option World
  | [], world => some world
  | command :: rest, world => (execute command world).bind (runUnchecked rest)

def runChecked : List Command → World → Option World
  | [], world => some world
  | command :: rest, world => (step command world).bind (runChecked rest)

structure Analysis where
  result : World
  facts : List Fact

/-- A checker for resolved finite recipe instances, not source-language type
inference. Inputs are graphs/operations; no safety certificates are accepted. -/
def check (input : Input) (program : List Command) : Option Analysis := do
  let start ← prepare input
  let result ← runChecked program start
  if result.active then none else some ⟨result, analyze input program⟩

/-- Plan a write against the current draft. Each descendant is rebuilt with a
fresh address, and the caller installs the resulting contents at the draft root. -/
def rebuild (heap : Heap) (object : Nat) (contents : List Value) (next : Nat) :
    List Nat → Option (List Command × List Value)
  | [] => some ([], contents)
  | index :: rest => do
    let parent ← heap object
    let .reference child ← parent.contents[index]? | none
    let cell ← heap child
    let (copies, values) ← rebuild heap child contents next rest
    let address := next + copies.length
    return (copies ++ [.allocate cell.storage values],
      parent.contents.set index (.reference address))

inductive RecipeStep where
  | rewrite (path : List Nat) (contents : List Value)
  | allocate (storage : Storage) (contents : List Value)
  | external (observation : ExternalObservation)
  | effect (effect : Nat)
  | finish (reason : Exit)

def RecipeStep.lower (world : World) : RecipeStep → Option (List Command)
  | .rewrite path contents => do
    let (copies, values) ← rebuild world.memory world.input.draftRoot contents world.nextObject path
    return copies ++ [.rewrite world.input.draftRoot values]
  | .allocate storage contents => some [.allocate storage contents]
  | .external observation => some [.external observation]
  | .effect id => some [.effect id]
  | .finish reason => some [.finish reason]

def lowerRecipe (world : World) : List RecipeStep → Option (List Command)
  | [] => some []
  | action :: rest => do
    let commands ← action.lower world
    let next ← runUnchecked commands world
    return commands ++ (← lowerRecipe next rest)

def checkRecipe (input : Input) (recipe : List RecipeStep) : Option Analysis := do
  let start ← prepare input
  let commands ← lowerRecipe start recipe
  check input commands

end RilAccess.Draft
