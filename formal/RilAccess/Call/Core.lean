import RilAccess.Access.Footprints

/-! Checked call boundaries. Calls in this layer are resolved, finite call-site
instances. Recursive interfaces and general function values are a separate proof
obligation, not silently interpreted by a fuel-limited evaluator. -/
namespace RilAccess.Calls

open Integrated

structure Argument where
  source : Path
  formal : Nat
  mode : ParameterMode
  marker : ParameterMode
  deriving Repr, DecidableEq

inductive Syntax where
  | access (body : Integrated.Syntax)
  | sequence (first second : Syntax)
  | branch (left right : Syntax)
  | invoke (arguments : List Argument) (captures : List Nat) (body : Syntax)
  deriving Repr, DecidableEq

def prepare (arguments : List Argument) : Code :=
  arguments.foldr (fun argument rest => .sequence
    (.atom (.parameter argument.source argument.formal argument.mode)) rest)
    (.atom .activateParameters)

def lower : Syntax → Code
  | .access body => Integrated.lower body
  | .sequence first second => .sequence (lower first) (lower second)
  | .branch left right => .choice (lower left) (lower right)
  | .invoke arguments _ body => .sequence (.sequence (.atom .enterScope) (prepare arguments))
      (.sequence (lower body) (.atom .leaveScope))

def operandRegisters : Atom → List Nat
  | .bind source _ _ | .read source | .write source | .replaceScalar source |
      .retain source | .beginBorrow source _ | .parameter source _ _ => [source.register]
  | .assign source destination => [source.register, destination]
  | .move source _ => [source]
  | .pairWrite left right => [left.register, right.register]
  | _ => []

def references : Code → List Nat
  | .atom operation => operandRegisters operation
  | .sequence first second | .choice first second => references first ++ references second

def exactNames (left right : List Nat) : Bool :=
  left.all (fun name => decide (name ∈ right)) && right.all (fun name => decide (name ∈ left))

def capturesCorrect (arguments : List Argument) (captures : List Nat) (body : Syntax) : Bool :=
  let localNames := arguments.map Argument.formal ++ Integrated.binders (lower body)
  let freeNames := (references (lower body)).filter (fun name => decide (name ∉ localNames))
  exactNames captures freeNames

def valid : Syntax → Bool
  | .access body => Integrated.surfaceValid body
  | .sequence first second | .branch first second => valid first && valid second
  | .invoke arguments captures body => valid body && capturesCorrect arguments captures body &&
      arguments.all (fun argument => decide (argument.mode = argument.marker))

def prepareRaw (arguments : List Argument) : RawState → List RawState :=
  match arguments with
  | [] => fun state => [state]
  | argument :: rest => fun state =>
    (rawStep (.copy argument.source argument.formal) state).toList.flatMap (prepareRaw rest)

/-- Runtime calls copy evaluated argument handles left-to-right. They do not
inspect parameter modes, markers, required-use evidence, or authority tokens. -/
def execute : Syntax → RawState → List RawState
  | .access body, state => Integrated.sourceExecute body state
  | .sequence first second, state => (execute first state).flatMap (execute second)
  | .branch left right, state => execute left state ++ execute right state
  | .invoke arguments _ body, state => (prepareRaw arguments state).flatMap (execute body)

def argumentPresent (w : World) (argument : Argument) : Bool :=
  (resolve w argument.source).isSome && unused w argument.formal

def parameterToken (entry : World) (formal : Nat) : Option Nat := do
  let permission ← lookupPermission entry formal
  permission.dependencies.head?

def evidenceUses (token : Nat) (evidence : Evidence) : Bool :=
  decide (token ∈ evidence.resolved.authorityOrigins) &&
    (decide (evidence.rule = .write) || decide (evidence.rule = .replaceScalar) ||
      decide (evidence.rule = .retain))

/-- This checks surviving authority, not writes or object equality. The parent
relation preserves the distinction between independent aliased participants. -/
def rootedWriter (world : World) (token : Token) : Bool :=
  token.retained || world.permissions.any fun permission =>
    permission.alive && permission.mode.access.writes && decide (permission.scope < world.scope) &&
      decide (token.id ∈ permission.dependencies) &&
      permission.dependencies.all (fun id =>
        match lookupToken world id with | some dependency => dependency.active | none => false) &&
      match rawLookup world.raw permission.register with
      | some pointer => contains token.region pointer
      | none => false

def retainedBeyond (formalToken : Nat) (world : World) : Bool :=
  world.tokens.any fun token => token.active && decide (formalToken < token.id) &&
    rootedWriter world token &&
    decide (formalToken ∈ tokenAncestors world.tokens token.id)

def requiredUse (entry : World) (frontier : List World) (argument : Argument) : Bool :=
  match parameterToken entry argument.formal with
  | none => false
  | some token =>
    match argument.mode with
    | .immutable | .observe | .construction => true
    | .mutable => frontier.any (fun world => world.evidence.any (evidenceUses token))
    | .retained => frontier.any (retainedBeyond token)

def requiredUses (entry : World) (frontier : List World) (arguments : List Argument) : Bool :=
  arguments.all (requiredUse entry frontier)

def finish (worlds : List World) : Except Error (List World) :=
  checkMany (fun world => do
    let next ← checkAtom .leaveScope world
    pure [next]) worlds

def infer : Syntax → World → Except Error (List World)
  | .access body, world => Integrated.infer (Integrated.lower body) world
  | .sequence first second, world => do
    let front ← infer first world
    checkMany (infer second) front
  | .branch left right, world => do
    let l ← infer left world
    let r ← infer right world
    pure (l ++ r)
  | .invoke arguments _ body, world => do
    if arguments.all (argumentPresent world) then
      let prepared ← Integrated.infer (.sequence (.atom .enterScope) (prepare arguments)) world
      checkMany (fun entry => do
        let front ← infer body entry
        if requiredUses entry front arguments then finish front else .error .invalidCertificate) prepared
    else .error .invalidSource

def check (program : Syntax) : Except Error Integrated.Analysis :=
  if valid program && decide (Integrated.binders (lower program)).Nodup then do
    let worlds ← infer program initialWorld
    if worlds.any (fun world => !world.frames.isEmpty) then .error .unclosedScope
    else
      match (worlds.flatMap World.requirements).find?
          (fun requirement => !satisfiesUse (allUses worlds) requirement) with
      | some requirement => .error (.absentUse requirement)
      | none => .ok ⟨worlds, worlds.flatMap worldOrigins⟩
  else .error .invalidSource

end RilAccess.Calls
