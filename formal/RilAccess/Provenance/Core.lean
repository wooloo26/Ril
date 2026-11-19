import RilAccess.Model

/-! A closed, resolved core for source analysis. The runtime executes only
registers, allocations, and heap operations. Frames, receiver modes, holds and
signature rows are checked by the compiler-facing interpretation. -/
namespace RilAccess.Provenance

abbrev Register := Nat
abbrev Field := Nat

structure Object where
  site : Nat
  occurrence : Option Nat
  deriving Repr, DecidableEq

inductive AllocationClass where
  | first (site : Nat)
  | repeated (site : Nat)
  deriving Repr, DecidableEq

def Object.allocationClass (object : Object) : AllocationClass :=
  if object.occurrence.isNone then .first object.site else .repeated object.site

def AllocationClass.singleton : AllocationClass → Bool
  | .first _ => true
  | .repeated _ => false

def Object.singleton (object : Object) : Bool := object.occurrence.isNone

def Object.abstract (object : Object) : Object :=
  { object with occurrence := object.occurrence.map (fun _ => 0) }

def getSlot (slots : List (Nat × α)) (key : Nat) : Option α :=
  (slots.find? fun slot => slot.1 == key).map Prod.snd

def putSlot (slots : List (Nat × α)) (key : Nat) (value : α) : List (Nat × α) :=
  (key, value) :: slots.filter (fun slot => slot.1 != key)

abbrev Link := HeapLink Object

def Link.abstract (link : Link) : Link :=
  link.map Object.abstract

def Link.atSlot (parent : Object) (field : Field) (link : Link) : Bool :=
  decide (link.parent = parent ∧ link.field = field)

structure Memory where
  heap : List Link := []
  sites : List Nat := []
  clock : Nat := 0
  deriving Repr, DecidableEq

def Memory.abstract (memory : Memory) : Memory :=
  ⟨memory.heap.map Link.abstract, memory.sites, 0⟩

structure RawFrame where
  registers : List (Register × Object) := []
  memory : Memory := {}
  deriving Repr, DecidableEq

def RawFrame.abstract (frame : RawFrame) : RawFrame :=
  ⟨frame.registers.map (fun (r, object) => (r, object.abstract)), frame.memory.abstract⟩

def RawFrame.get (frame : RawFrame) (r : Register) : Option Object :=
  getSlot frame.registers r

def RawFrame.put (frame : RawFrame) (r : Register) (object : Object) : RawFrame :=
  { frame with registers := putSlot frame.registers r object }

inductive Prim where
  | alloc (destination site : Nat)
  | copy (destination source : Register)
  | store (parent : Register) (field : Field) (source : Register)
  | select (destination parent : Register) (field : Field)
  | read (register : Register)
  | write (register : Register)
  | publish (register : Register)
  | skip
  deriving Repr, DecidableEq

def RawFrame.allocateAt (frame : RawFrame) (destination site : Nat) (repeated : Bool) : RawFrame :=
  let next := frame.put destination ⟨site, if repeated then some frame.memory.clock else none⟩
  { next with memory := { frame.memory with
    sites := if repeated then frame.memory.sites else site :: frame.memory.sites
    clock := frame.memory.clock + 1 } }

def RawFrame.allocate (frame : RawFrame) (destination site : Nat) : RawFrame :=
  frame.allocateAt destination site (frame.memory.sites.contains site)

def RawFrame.store (frame : RawFrame) (owner : Object) (field : Field) (target : Object) : RawFrame :=
  let heap := ⟨owner, field, target⟩ :: frame.memory.heap.filter (!Link.atSlot owner field ·)
  { frame with memory := { frame.memory with heap } }

def runPrim (action : Prim) (frame : RawFrame) : Option RawFrame :=
  match action with
  | .alloc destination site => some (frame.allocate destination site)
  | .copy destination source =>
      (frame.get source).map (frame.put destination)
  | .store parent field source =>
      (frame.get parent).bind fun owner => (frame.get source).map (frame.store owner field)
  | .select destination parent field =>
      (frame.get parent).bind fun owner =>
        (frame.memory.heap.find? (Link.atSlot owner field)).map (fun link => frame.put destination link.child)
  | .read register | .write register | .publish register =>
      (frame.get register).map fun _ => frame
  | .skip => some frame

inductive Primitive where
  | alloc (destination site : Nat)
  | bind (destination source : Register) (mode : Access)
  | handoff (destination source : Register)
  | store (parent : Register) (field : Field) (source : Register) (consume : Bool := false)
  | select (destination parent : Register) (field : Field)
  | read (register : Register)
  | write (register : Register)
  | publish (register : Register)
  | scope (register : Register)
  | expire (register : Register)
  deriving Repr, DecidableEq

def Primitive.erase : Primitive → Prim
  | .alloc d s => .alloc d s
  | .bind d s _ | .handoff d s => .copy d s
  | .store p f s _ => .store p f s
  | .select d p f => .select d p f
  | .read r => .read r
  | .write r => .write r
  | .publish r => .publish r
  | .scope _ | .expire _ => .skip

def Primitive.operands : Primitive → List Register
  | .alloc _ _ => []
  | .bind _ source _ | .handoff _ source => [source]
  | .select _ parent _ => [parent]
  | .store parent _ source _ => [parent, source]
  | .read register | .write register | .publish register | .scope register | .expire register => [register]

def Primitive.writer : Primitive → Option Register
  | .write register | .store register _ _ _ => some register
  | _ => none

def Primitive.destination : Primitive → Option Register
  | .alloc d _ | .bind d _ _ | .handoff d _ | .select d _ _ => some d
  | _ => none

structure Argument where
  source : Register
  marker : ParameterMode
  deriving Repr, DecidableEq

inductive ReturnMode where
  | unit
  | plain
  | observe (formals : List Register)
  | retained (formal : Register)
  | construction
  deriving Repr, DecidableEq

structure OldSource where
  formal : Register
  mode : Access
  deriving Repr, DecidableEq

structure Signature where
  result : ReturnMode := .unit
  writes : Bool := false
  retains : Bool := false
  contained : List OldSource := []
  deriving Repr, DecidableEq

inductive Instruction where
  /-- Multiple alternatives model a dynamic branch or selection whose possible
      concrete keys have already been resolved. A pruned branch is absent. -/
  | branch (targets : List Nat)
  | step (alternatives : List Primitive) (next : Nat)
  | invoke (callee : Nat) (arguments : List Argument) (destination : Option (Register × Access))
      (next : Nat) (onAbort : Option Nat := none)
  | ret (source : Option Register)
  | abort
  deriving Repr, DecidableEq

structure Function where
  parameters : List ParameterMode := []
  signature : Signature := {}
  code : List Instruction
  deriving Repr, DecidableEq

/-- Schemas are indexed by allocation site and resolved slot. The checker
    rejects ambiguous keys. Access-mode metadata never changes the schema. -/
structure Slot where
  site : Nat
  field : Field
  mode : MemberMode
  deriving Repr, DecidableEq

structure Program where
  functions : List Function
  slots : List Slot := []
  deriving Repr, DecidableEq

def Program.slot (program : Program) (object : Object) (field : Field) : Option MemberMode :=
  (program.slots.find? (fun s => s.site == object.site && s.field == field)).map Slot.mode

def Program.instruction (program : Program) (function pc : Nat) : Option Instruction :=
  (program.functions[function]?).bind (fun f => f.code[pc]?)

inductive RawInstruction where
  | branch (targets : List Nat)
  | step (alternatives : List Prim) (next : Nat)
  | invoke (callee : Nat) (arguments : List Register) (destination : Option Register)
      (next : Nat) (onAbort : Option Nat := none)
  | ret (source : Option Register)
  | abort
  deriving Repr, DecidableEq

def Instruction.erase : Instruction → RawInstruction
  | .branch targets => .branch targets
  | .step alternatives next => .step (alternatives.map Primitive.erase) next
  | .invoke callee args dest next onAbort =>
    .invoke callee (args.map Argument.source) (dest.map Prod.fst) next onAbort
  | .ret source => .ret source
  | .abort => .abort

def Program.erase (program : Program) : List (List RawInstruction) :=
  program.functions.map fun f => f.code.map Instruction.erase

def RawFrame.prepare (caller : RawFrame) (arguments : List Register) : Option RawFrame := do
  let values ← arguments.mapM caller.get
  return ⟨values.zipIdx.map (fun (object, formal) => (formal, object)), caller.memory⟩

def RawFrame.resume (caller : RawFrame) (memory : Memory) (destination : Option Register)
    (returned : Option Object) : Option RawFrame :=
  let restored := { caller with memory }
  match destination, returned with
  | some register, some object => some (restored.put register object)
  | none, none => some restored
  | _, _ => none

def RawFrame.returnValue (frame : RawFrame) (source : Option Register) : Option (Option Object) :=
  source.mapM frame.get

inductive Position (α : Type) where
  | at (pc : Nat) (state : α)
  | returned (value : Option Register) (state : α)
  | aborted (state : α)
  deriving Repr, DecidableEq

def Position.unwind (onAbort : Option Nat) (frame : α) : Position α :=
  match onAbort with
  | none => .aborted frame
  | some next => .at next frame

def rawInstruction (code : List (List RawInstruction)) (function pc : Nat) : Option RawInstruction :=
  (code[function]?).bind (fun f => f[pc]?)

/-- Finite runtime prefixes with well-nested calls. The call rule composes a
    callee's entry-to-exit derivation, so recursion needs no execution fuel.
    Dead handles can remain in the raw registers after erasure. -/
inductive Executes (code : List (List RawInstruction)) :
    Nat → RawFrame → Position RawFrame → Prop where
  | start : Executes code function entry (.at 0 entry)
  | branch :
      Executes code function entry (.at pc before) →
      rawInstruction code function pc = some (.branch targets) →
      next ∈ targets →
      Executes code function entry (.at next before)
  | step :
      Executes code function entry (.at pc before) →
      rawInstruction code function pc = some (.step alternatives next) →
      action ∈ alternatives → runPrim action before = some after →
      Executes code function entry (.at next after)
  | call :
      Executes code function entry (.at pc before) →
      rawInstruction code function pc = some (.invoke callee arguments destination next onAbort) →
      before.prepare arguments = some entered →
      Executes code callee entered (.returned source exited) →
      exited.returnValue source = some result →
      before.resume exited.memory destination result = some after →
      Executes code function entry (.at next after)
  | callAbort :
      Executes code function entry (.at pc before) →
      rawInstruction code function pc = some (.invoke callee arguments destination next onAbort) →
      before.prepare arguments = some entered →
      Executes code callee entered (.aborted exited) →
      Executes code function entry (Position.unwind onAbort { before with memory := exited.memory })
  | ret :
      Executes code function entry (.at pc before) →
      rawInstruction code function pc = some (.ret source) →
      before.returnValue source = some result →
      Executes code function entry (.returned source before)
  | abort :
      Executes code function entry (.at pc before) →
      rawInstruction code function pc = some .abort →
      Executes code function entry (.aborted before)

end RilAccess.Provenance
