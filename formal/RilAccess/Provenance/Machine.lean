import RilAccess.Provenance.Core

namespace RilAccess.Provenance

structure Continuation where
  function : Nat
  next : Nat
  destination : Option Register
  frame : RawFrame
  onAbort : Option Nat := none
  deriving Repr, DecidableEq

inductive Machine where
  | running (function pc : Nat) (frame : RawFrame) (stack : List Continuation)
  | finished (source : Option Register) (frame : RawFrame)
  | panicked (memory : Memory)
  deriving Repr, DecidableEq

def Machine.unwind (frame : RawFrame) : List Continuation → Machine
  | [] => .panicked frame.memory
  | current :: stack =>
    let resumed := { current.frame with memory := frame.memory }
    match current.onAbort with
    | some handler => .running current.function handler resumed stack
    | none => unwind resumed stack

/-- Erased small steps. In particular, entering a recursive call pushes a
    continuation without waiting for the callee to produce a return. -/
inductive MachineStep (code : List (List RawInstruction)) : Machine → Machine → Prop where
  | branch :
      rawInstruction code fn pc = some (.branch targets) → next ∈ targets →
      MachineStep code (.running fn pc before stack) (.running fn next before stack)
  | primitive :
      rawInstruction code fn pc = some (.step alternatives next) →
      action ∈ alternatives → runPrim action before = some after →
      MachineStep code (.running fn pc before stack) (.running fn next after stack)
  | enter :
      rawInstruction code fn pc = some (.invoke callee arguments destination next onAbort) →
      before.prepare arguments = some entered →
      MachineStep code (.running fn pc before stack)
        (.running callee 0 entered (⟨fn, next, destination, before, onAbort⟩ :: stack))
  | leave :
      rawInstruction code fn pc = some (.ret source) →
      before.returnValue source = some result →
      continuation.frame.resume before.memory continuation.destination result = some after →
      MachineStep code (.running fn pc before (continuation :: stack))
        (.running continuation.function continuation.next after stack)
  | finish :
      rawInstruction code fn pc = some (.ret source) →
      before.returnValue source = some result →
      MachineStep code (.running fn pc before []) (.finished source before)
  | abort :
      rawInstruction code fn pc = some .abort →
      MachineStep code (.running fn pc before stack) (Machine.unwind before stack)

inductive MachineTrace (code : List (List RawInstruction)) : Machine → Prop where
  | start : MachineTrace code (.running 0 0 {} [])
  | tail : MachineTrace code before → MachineStep code before after → MachineTrace code after

/-- The suspended frame remembers a valid history and the evaluated call
    that entered the next frame. This is a logical reconstruction only. -/
inductive StackContext (code : List (List RawInstruction)) : Nat → RawFrame → List Continuation → Prop where
  | top : StackContext code 0 {} []
  | push :
      StackContext code fn initialFrame stack →
      Executes code fn initialFrame (.at pc before) →
      rawInstruction code fn pc = some (.invoke callee arguments destination next onAbort) →
      before.prepare arguments = some entered →
      StackContext code callee entered (⟨fn, next, destination, before, onAbort⟩ :: stack)

def Decomposed (code : List (List RawInstruction)) : Machine → Prop
  | .running fn pc frame stack =>
    ∃ initialFrame, StackContext code fn initialFrame stack ∧ Executes code fn initialFrame (.at pc frame)
  | .finished source frame => Executes code 0 {} (.returned source frame)
  | .panicked memory => ∃ frame, frame.memory = memory ∧ Executes code 0 {} (.aborted frame)

theorem StackContext.unwind (context : StackContext code fn entered stack)
    (run : Executes code fn entered (.aborted frame)) :
    Decomposed code (Machine.unwind frame stack) := by
  induction context generalizing frame with
  | top => exact ⟨frame, rfl, run⟩
  | @push fn initialFrame stack pc before callee arguments destination next onAbort entered context history call prepared ih =>
    have unwound := Executes.callAbort history call prepared run
    cases onAbort with
    | none => exact ih unwound
    | some target => exact ⟨initialFrame, context, unwound⟩

theorem decomposes (trace : MachineTrace code machine) : Decomposed code machine := by
  induction trace with
  | start => exact ⟨{}, .top, .start⟩
  | tail _ step ih =>
    cases step with
    | branch code chosen =>
      obtain ⟨entered, context, history⟩ := ih
      exact ⟨entered, context, .branch history code chosen⟩
    | primitive code chosen run =>
      obtain ⟨entered, context, history⟩ := ih
      exact ⟨entered, context, .step history code chosen run⟩
    | enter code prepared =>
      obtain ⟨_, context, history⟩ := ih
      exact ⟨_, .push context history code prepared, .start⟩
    | leave code selected resumed =>
      obtain ⟨_, context, history⟩ := ih
      cases context with
      | push context caller call prepared =>
        exact ⟨_, context, .call caller call prepared (.ret history code selected) selected resumed⟩
    | finish code selected =>
      obtain ⟨_, context, history⟩ := ih
      cases context
      exact .ret history code selected
    | abort code =>
      obtain ⟨_, context, history⟩ := ih
      exact context.unwind (.abort history code)

end RilAccess.Provenance
