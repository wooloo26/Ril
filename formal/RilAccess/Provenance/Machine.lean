import RilAccess.Provenance.Certificate

namespace RilAccess.Provenance

structure Continuation where
  function : Nat
  next : Nat
  destination : Option Register
  frame : RawFrame
  deriving Repr, DecidableEq

inductive Machine where
  | running (function pc : Nat) (frame : RawFrame) (stack : List Continuation)
  | finished (source : Option Register) (frame : RawFrame)
  | panicked (memory : Memory)
  deriving Repr, DecidableEq

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
      rawInstruction code fn pc = some (.invoke callee arguments destination next) →
      before.prepare arguments = some entered →
      MachineStep code (.running fn pc before stack)
        (.running callee 0 entered (⟨fn, next, destination, before⟩ :: stack))
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
      MachineStep code (.running fn pc before stack) (.panicked before.memory)

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
      rawInstruction code fn pc = some (.invoke callee arguments destination next) →
      before.prepare arguments = some entered →
      StackContext code callee entered (⟨fn, next, destination, before⟩ :: stack)

def Decomposed (code : List (List RawInstruction)) : Machine → Prop
  | .running fn pc frame stack =>
    ∃ initialFrame, StackContext code fn initialFrame stack ∧ Executes code fn initialFrame (.at pc frame)
  | .finished source frame => Executes code 0 {} (.returned source frame)
  | .panicked memory => ∃ frame, frame.memory = memory ∧ Executes code 0 {} (.aborted frame)

theorem StackContext.unwind (context : StackContext code fn entered stack)
    (run : Executes code fn entered (.aborted frame)) :
    ∃ result, result.memory = frame.memory ∧ Executes code 0 {} (.aborted result) := by
  induction context generalizing frame with
  | top => exact ⟨frame, rfl, run⟩
  | @push fn initialFrame stack pc before callee arguments destination next entered _ history call prepared ih =>
    exact ih (frame := { before with memory := frame.memory }) (.callAbort history call prepared run)

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

theorem StackContext.activated (checked : Checked program facts)
    (context : StackContext program.erase fn initialFrame stack) :
    ∃ entry : Entry, entry.function = fn ∧ entry.world.raw = initialFrame.abstract ∧
      Judgment.point entry 0 entry.world ∈ facts := by
  induction context with
  | top => exact ⟨startEntry, rfl, rfl, checked.seed _ (by simp [seed])⟩
  | push _ history code prepared ih =>
    obtain ⟨entry, he, hw, active⟩ := ih
    have ⟨world, equivalent, member⟩ := covers_execution checked history he hw active
    rw [← he] at code
    obtain ⟨body, instruction, hf, hi, erases⟩ := instruction_matches code
    cases instruction <;> simp [Instruction.erase] at erases
    case invoke callee arguments receiver next =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := erases
      obtain ⟨_, call, _, analyzed, activated, _⟩ := checked.call member hf hi
      have eq := prepare_raw analyzed
      rw [equivalent, RawFrame.prepare_abstract, prepared] at eq
      exact ⟨⟨callee, call.entered⟩, rfl, (Option.some.inj eq).symm, activated⟩

def MachineGuarantee (program : Program) (facts : List Judgment) : Machine → Prop
  | .running fn pc frame _ =>
    ∃ (entry : Entry) (frozen : RawFrame), entry.function = fn ∧ entry.world.raw = frozen.abstract ∧
      Judgment.point entry 0 entry.world ∈ facts ∧
      Covered program facts entry (.at pc frame) ∧ RuntimeGuarantee program facts entry frozen (.at pc frame)
  | .finished source frame =>
    Covered program facts startEntry (.returned source frame) ∧
      RuntimeGuarantee program facts startEntry {} (.returned source frame)
  | .panicked memory => ∃ (frame : RawFrame), frame.memory = memory ∧
      Covered program facts startEntry (.aborted frame)

theorem verified_machine (h : check program budget = .ok certificate)
    (trace : MachineTrace program.erase machine) :
    MachineGuarantee program certificate.facts machine := by
  have checked := check_sound h
  have decomposition := decomposes trace
  cases machine with
  | running fn pc frame stack =>
    obtain ⟨frozen, context, history⟩ := decomposition
    obtain ⟨entry, rfl, hw, activated⟩ := context.activated checked
    exact ⟨entry, frozen, rfl, hw, activated, verified_execution checked history hw activated⟩
  | finished source frame => exact (verified_program h).2 _ decomposition
  | panicked memory =>
    obtain ⟨frame, hm, history⟩ := decomposition
    exact ⟨frame, hm, checked_execution h history⟩

theorem StackContext.resume_ready (checked : Checked program facts)
    (context : StackContext program.erase fn entered (continuation :: stack))
    (run : Executes program.erase fn entered (.returned source exited))
    (returned : exited.returnValue source = some result) :
    ∃ after, continuation.frame.resume exited.memory continuation.destination result = some after := by
  cases context with
  | @push caller initialFrame _ pc before callee arguments destination next entered context history code prepared =>
    obtain ⟨entry, he, hw, active⟩ := context.activated checked
    obtain ⟨world, equivalent, member⟩ := covers_execution checked history he hw active
    rw [← he] at code
    obtain ⟨body, instruction, hf, hi, erased⟩ := instruction_matches code
    cases instruction <;> simp [Instruction.erase] at erased
    case invoke target args receiver following =>
      obtain ⟨rfl, rfl, rfl, rfl⟩ := erased
      obtain ⟨_, call, _, analyzed, activated, continuationFact⟩ := checked.call member hf hi
      have heq : call.entered.raw = entered.abstract := by
        have eq := prepare_raw analyzed
        rw [equivalent, RawFrame.prepare_abstract, prepared] at eq
        exact (Option.some.inj eq).symm
      obtain ⟨worldExit, value, _, exitEq, exitMember, _, _⟩ :=
        covers_execution checked run rfl heq activated
      cases hr : resume program call worldExit source value receiver with
      | error error =>
        exfalso
        exact checked.noRejection entry.function pc error
          (continuationFact _ exitMember _ (by simp [propagate, hr]))
      | ok after =>
        have valueEq : worldExit.raw.returnValue source = some (result.map Object.abstract) := by
          rw [exitEq, RawFrame.return_abstract, returned]
          rfl
        have raw := resume_raw hr valueEq
        rw [prepared_caller_raw analyzed, equivalent, exitEq] at raw
        change before.abstract.resume exited.memory.abstract (receiver.map Prod.fst)
          (result.map Object.abstract) = some after.raw at raw
        rw [RawFrame.resume_abstract] at raw
        cases hv : before.resume exited.memory (receiver.map Prod.fst) result
        · simp [hv] at raw
        · exact ⟨_, rfl⟩

theorem machine_progress (h : check program budget = .ok certificate)
    (trace : MachineTrace program.erase (.running fn pc frame stack)) :
    ∃ next, MachineStep program.erase (.running fn pc frame stack) next := by
  have checked := check_sound h
  obtain ⟨entered, context, history⟩ := decomposes trace
  obtain ⟨entry, he, hw, active⟩ := context.activated checked
  have coverage := covers_execution checked history he hw active
  obtain ⟨body, instruction, hf, hi, safe⟩ := checked_point_safe checked coverage hw
  have code : rawInstruction program.erase fn pc = some instruction.erase := by
    rw [← he, rawInstruction_erase]
    simp [Program.instruction, hf, hi]
  cases instruction with
  | branch targets =>
    obtain ⟨target, picked⟩ := List.exists_mem_of_ne_nil _ safe.1
    exact ⟨_, .branch code picked⟩
  | step alternatives next =>
    obtain ⟨action, picked⟩ := List.exists_mem_of_ne_nil _ safe.1
    obtain ⟨_, ran, _, _⟩ := safe.2 action picked
    exact ⟨_, .primitive code (List.mem_map_of_mem picked) ran⟩
  | invoke callee arguments destination next =>
    obtain ⟨_, _, _, prepared, _, _, _, _⟩ := safe
    exact ⟨_, .enter code prepared⟩
  | ret source =>
    obtain ⟨_, _, _, returned, _, _⟩ := safe
    cases stack with
    | nil => exact ⟨_, .finish code returned⟩
    | cons continuation tail =>
      obtain ⟨_, resumed⟩ := context.resume_ready checked (.ret history code returned) returned
      exact ⟨_, .leave code returned resumed⟩
  | abort => exact ⟨_, .abort code⟩

end RilAccess.Provenance
