import RilAccess.Provenance.Machine
import RilAccess.Provenance.Certificate

namespace RilAccess.Provenance

theorem StackContext.activated (checked : Checked program facts)
    (context : StackContext program.erase fn initialFrame stack) :
    ∃ entry : Entry, entry.function = fn ∧ entry.world.raw = initialFrame.abstract ∧
      Judgment.point entry 0 entry.world ∈ facts := by
  induction context with
  | top => exact ⟨startEntry, rfl, rfl, checked.seed _ (by simp [seed, entrySeed])⟩
  | push _ history code prepared ih =>
    obtain ⟨entry, he, hw, active⟩ := ih
    have ⟨world, equivalent, member⟩ := covers_execution checked history he hw active
    rw [← he] at code
    obtain ⟨body, instruction, hf, hi, erases⟩ := instruction_matches code
    cases instruction <;> simp [Instruction.erase] at erases
    case invoke callee arguments receiver next onAbort =>
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := erases
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
  | @push caller initialFrame _ pc before callee arguments destination next onAbort entered context history code prepared =>
    obtain ⟨entry, he, hw, active⟩ := context.activated checked
    obtain ⟨world, equivalent, member⟩ := covers_execution checked history he hw active
    rw [← he] at code
    obtain ⟨body, instruction, hf, hi, erased⟩ := instruction_matches code
    cases instruction <;> simp [Instruction.erase] at erased
    case invoke target args receiver following exceptional =>
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := erased
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
  | invoke callee arguments destination next onAbort =>
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
