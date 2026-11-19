import RilAccess.Provenance.Abstraction

namespace RilAccess.Provenance

structure Checked (program : Program) (facts : List Judgment) (inputs : List Judgment := seed) : Prop where
  seed : Includes inputs facts
  stable : Stable (expand program) facts
  least : ∀ upper, Includes inputs upper → Stable (expand program) upper → Includes facts upper
  noRejection : ∀ function pc error, Judgment.rejected function pc error ∉ facts
  interfaces : ∀ entry ∈ entries facts, checkInterface program facts entry = .ok ()

theorem checkEntry_sound (h : checkEntry program entry budget = .ok certificate) :
    Checked program certificate.facts (entrySeed entry) := by
  unfold checkEntry at h
  cases hv : validSchemas program <;> simp [hv] at h
  cases hf : saturate (expand program) budget (entrySeed entry) with
  | none => simp [hf] at h
  | some facts =>
    cases he : (failures facts).head? with
    | some error => simp [hf, he] at h
    | none =>
      cases hi : interfaceFailure program facts with
      | some error => simp [hf, he, hi] at h
      | none =>
        simp [hf, he, hi] at h
        subst certificate
        have closure := saturate_stable hf
        refine ⟨closure.1, closure.2, fun _ hs hc => saturate_least (expand_monotone _) hc hs hf, ?_, ?_⟩
        · intro function pc error rejected
          have member : ⟨function, pc, error⟩ ∈ failures facts :=
            List.mem_filterMap.mpr ⟨_, rejected, rfl⟩
          have empty : failures facts = [] := List.head?_eq_none_iff.mp he
          rw [empty] at member
          exact List.not_mem_nil member
        · intro entry member
          unfold interfaceFailure at hi
          have none := List.findSome?_eq_none_iff.mp hi entry member
          cases hr : checkInterface program facts entry with
          | ok value => cases value; rfl
          | error error => simp [hr] at none

theorem check_sound (h : check program budget = .ok certificate) :
    Checked program certificate.facts := by
  unfold check at h
  split at h
  · exact checkEntry_sound h
  · simp at h

theorem checked_budgets_agree (h₁ : check program budget₁ = .ok first)
    (h₂ : check program budget₂ = .ok second) :
    fact ∈ first.facts ↔ fact ∈ second.facts := by
  have left := check_sound h₁
  have right := check_sound h₂
  exact ⟨left.least _ right.seed right.stable _, right.least _ left.seed left.stable _⟩

theorem Checked.instruction (checked : Checked program facts inputs)
    (atPoint : Judgment.point entry pc world ∈ facts) :
    ∃ function instruction, program.functions[entry.function]? = some function ∧
      function.code[pc]? = some instruction := by
  cases hf : program.functions[entry.function]? with
  | none =>
    exfalso
    exact checked.noRejection entry.function pc .missingInstruction
      (checked.stable _ atPoint _ (by simp [expand, hf]))
  | some function =>
    cases hi : function.code[pc]? with
    | none =>
      exfalso
      exact checked.noRejection entry.function pc .missingInstruction
        (checked.stable _ atPoint _ (by simp [expand, hf, hi]))
    | some instruction => exact ⟨function, instruction, rfl, hi⟩

theorem Checked.primitive (checked : Checked program facts inputs)
    (atPoint : Judgment.point entry pc world ∈ facts)
    (hf : program.functions[entry.function]? = some function)
    (hi : function.code[pc]? = some (.step alternatives next)) (ha : action ∈ alternatives) :
    ∃ after uses, primitive program action world = .ok (after, uses) ∧
      Judgment.point entry next after ∈ facts := by
  have nonempty : ¬alternatives = [] := fun eq => by simp [eq] at ha
  cases hm : Provenance.primitive program action world with
  | error error =>
    exfalso
    apply checked.noRejection entry.function pc error
    apply checked.stable _ atPoint
    simp only [expand, hf, hi, List.isEmpty_iff, nonempty, if_false]
    exact List.mem_flatMap.mpr ⟨action, ha, by simp [hm]⟩
  | ok value =>
    obtain ⟨after, uses⟩ := value
    refine ⟨after, uses, rfl, checked.stable _ atPoint _ ?_⟩
    simp only [expand, hf, hi, List.isEmpty_iff, nonempty, if_false]
    exact List.mem_flatMap.mpr ⟨action, ha, by simp [hm]⟩

theorem Checked.call (checked : Checked program facts inputs)
    (atPoint : Judgment.point entry pc world ∈ facts)
    (hf : program.functions[entry.function]? = some function)
    (hi : function.code[pc]? = some (.invoke callee arguments destination next onAbort)) :
    ∃ target prepared, program.functions[callee]? = some target ∧
      prepare target world arguments = .ok prepared ∧
      Judgment.point ⟨callee, prepared.entered⟩ 0 prepared.entered ∈ facts ∧
      ∀ fact ∈ facts, ∀ output ∈ propagate program entry ⟨callee, prepared.entered⟩
        pc next prepared destination onAbort fact, output ∈ facts := by
  cases hc : program.functions[callee]? with
  | none =>
    exfalso
    exact checked.noRejection entry.function pc .missingInstruction
      (checked.stable _ atPoint _ (by simp [expand, hf, hi, hc]))
  | some target =>
    cases hp : prepare target world arguments with
    | error error =>
      exfalso
      exact checked.noRejection entry.function pc error
        (checked.stable _ atPoint _ (by simp [expand, hf, hi, hc, hp]))
    | ok prepared =>
      refine ⟨target, prepared, rfl, hp, checked.stable _ atPoint _ ?_, ?_⟩
      · simp [expand, hf, hi, hc, hp]
      · intro fact member output emitted
        apply checked.stable _ atPoint
        simp only [expand, hf, hi, hc, hp]
        exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨fact, member, emitted⟩)

theorem Checked.ret (checked : Checked program facts inputs)
    (atPoint : Judgment.point entry pc world ∈ facts)
    (hf : program.functions[entry.function]? = some function)
    (hi : function.code[pc]? = some (.ret source)) :
    ∃ value, checkReturn program function entry.world world source = .ok value ∧
      Judgment.returned entry source world value ∈ facts := by
  cases hs : world.scopes.isEmpty with
  | false =>
    exfalso
    exact checked.noRejection entry.function pc .scopeOrder
      (checked.stable _ atPoint _ (by simp [expand, hf, hi, hs]))
  | true =>
    cases hr : checkReturn program function entry.world world source with
    | error error =>
      exfalso
      exact checked.noRejection entry.function pc error
        (checked.stable _ atPoint _ (by simp [expand, hf, hi, hs, hr]))
    | ok value =>
      exact ⟨value, rfl, checked.stable _ atPoint _ (by simp [expand, hf, hi, hs, hr])⟩

theorem Checked.abortMember (checked : Checked program facts inputs)
    (emits : Includes (abortFacts entry pc world) facts) :
    Judgment.aborted entry world ∈ facts := by
  cases hs : world.scopes.isEmpty with
  | false =>
    exfalso
    exact checked.noRejection entry.function pc .scopeOrder (emits _ (by simp [abortFacts, hs]))
  | true =>
    exact emits _ (by simp [abortFacts, hs])

theorem Checked.abort (checked : Checked program facts inputs)
    (atPoint : Judgment.point entry pc world ∈ facts)
    (hf : program.functions[entry.function]? = some function)
    (hi : function.code[pc]? = some .abort) :
    Judgment.aborted entry world ∈ facts := by
  apply checked.abortMember (pc := pc)
  intro fact member
  exact checked.stable _ atPoint _ (by simpa [expand, hf, hi] using member)

def Covered (program : Program) (facts : List Judgment) (entry : Entry) : Position RawFrame → Prop
  | .at pc frame =>
    ∃ world, world.raw = frame.abstract ∧ Judgment.point entry pc world ∈ facts
  | .returned source frame =>
    ∃ world value function, world.raw = frame.abstract ∧ Judgment.returned entry source world value ∈ facts ∧
      program.functions[entry.function]? = some function ∧
      checkReturn program function entry.world world source = .ok value
  | .aborted frame =>
    ∃ world, world.raw = frame.abstract ∧ Judgment.aborted entry world ∈ facts

theorem instruction_matches {program : Program} {entry : Entry}
    (h : rawInstruction program.erase entry.function pc = some raw) :
    ∃ (function : Function) (instruction : Instruction), program.functions[entry.function]? = some function ∧
      function.code[pc]? = some instruction ∧ instruction.erase = raw := by
  rw [rawInstruction_erase] at h
  cases hf : program.functions[entry.function]? with
  | none => simp [Program.instruction, hf] at h
  | some function =>
    cases hi : function.code[pc]? with
    | none => simp [Program.instruction, hf, hi] at h
    | some instruction =>
      exact ⟨function, instruction, rfl, hi, by simpa [Program.instruction, hf, hi] using h⟩

/-- Module tabulation simulates every finite erased prefix, including the
    prefixes used to summarize a recursive call. The induction index is the
    runtime derivation, independent of the analyzer's work budget. -/
theorem covers_execution (checked : Checked program facts inputs)
    {entry : Entry} {initialFrame : RawFrame} (run : Executes program.erase function initialFrame result)
    (he : entry.function = function) (hw : entry.world.raw = initialFrame.abstract)
    (seeded : Judgment.point entry 0 entry.world ∈ facts) :
    Covered program facts entry result := by
  induction run generalizing entry with
  | start => exact ⟨entry.world, hw, seeded⟩
  | @branch function initial pc before targets next _ code selected ih =>
    have ⟨world, equivalent, member⟩ := ih he hw seeded
    rw [← he] at code
    obtain ⟨body, instruction, hf, hi, erases⟩ := instruction_matches code
    cases instruction <;> simp [Instruction.erase] at erases
    case branch sourceTargets =>
      subst sourceTargets
      refine ⟨world, equivalent, checked.stable _ member _ ?_⟩
      have nonempty : targets ≠ [] := fun eq => by simp [eq] at selected
      simp [expand, hf, hi, nonempty, selected]
  | @step function initial pc before alternatives next action after _ code selected ran ih =>
    have ⟨world, equivalent, member⟩ := ih he hw seeded
    rw [← he] at code
    obtain ⟨body, instruction, hf, hi, erases⟩ := instruction_matches code
    cases instruction <;> simp [Instruction.erase] at erases
    case step operations following =>
      obtain ⟨rfl, rfl⟩ := erases
      obtain ⟨op, listed, rfl⟩ := List.mem_map.mp selected
      obtain ⟨abstractAfter, uses, ok, nextMember⟩ := checked.primitive member hf hi listed
      obtain ⟨raw, rawStep, abstraction⟩ := primitive_refines ok equivalent
      have same := Option.some.inj (rawStep.symm.trans ran)
      exact ⟨abstractAfter, same ▸ abstraction, nextMember⟩
  | @call function initial pc before callee args destination next onAbort entered source exited result after
      _ code rawPrepared _ returned rawResumed ih beforeReturn =>
    have ⟨world, equivalent, member⟩ := ih he hw seeded
    rw [← he] at code
    obtain ⟨body, instruction, hf, hi, erases⟩ := instruction_matches code
    cases instruction <;> simp [Instruction.erase] at erases
    case invoke target arguments receiver following exceptional =>
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := erases
      obtain ⟨targetBody, call, _, prepared, activated, propagateFact⟩ := checked.call member hf hi
      have enterEq : call.entered.raw = entered.abstract := by
        have eq := prepare_raw prepared
        rw [equivalent, RawFrame.prepare_abstract, rawPrepared] at eq
        exact (Option.some.inj eq).symm
      have ⟨exitWorld, value, _, exitEq, exitMember, _, _⟩ := beforeReturn rfl enterEq activated
      cases hr : resume program call exitWorld source value receiver with
      | error error =>
        exfalso
        exact checked.noRejection entry.function pc error
          (propagateFact _ exitMember _ (by simp [propagate, hr]))
      | ok resumed =>
        have returnEq : exitWorld.raw.returnValue source = some (result.map Object.abstract) := by
          rw [exitEq, RawFrame.return_abstract, returned]
          rfl
        have eq := resume_raw hr returnEq
        rw [prepared_caller_raw prepared, equivalent, exitEq] at eq
        change before.abstract.resume exited.memory.abstract (receiver.map Prod.fst)
          (result.map Object.abstract) = some resumed.raw at eq
        rw [RawFrame.resume_abstract, rawResumed] at eq
        exact ⟨resumed, (Option.some.inj eq).symm, propagateFact _ exitMember _ (by simp [propagate, hr])⟩
  | @callAbort function initial pc before callee args destination next onAbort entered exited
      _ code rawPrepared _ ih inside =>
    have ⟨world, equivalent, member⟩ := ih he hw seeded
    rw [← he] at code
    obtain ⟨body, instruction, hf, hi, erases⟩ := instruction_matches code
    cases instruction <;> simp [Instruction.erase] at erases
    case invoke target arguments receiver following exceptional =>
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := erases
      obtain ⟨targetBody, call, _, prepared, activated, propagateFact⟩ := checked.call member hf hi
      have enterEq : call.entered.raw = entered.abstract := by
        have eq := prepare_raw prepared
        rw [equivalent, RawFrame.prepare_abstract, rawPrepared] at eq
        exact (Option.some.inj eq).symm
      have ⟨exitWorld, exitEq, exitMember⟩ := inside rfl enterEq activated
      let after := abortCall call exitWorld
      have abstraction : after.raw = ({ before with memory := exited.memory } : RawFrame).abstract := by
        change { call.caller.raw with memory := exitWorld.raw.memory } =
          ({ before with memory := exited.memory } : RawFrame).abstract
        rw [prepared_caller_raw prepared, equivalent, exitEq]
        rfl
      cases exceptional with
      | none =>
        refine ⟨after, abstraction, checked.abortMember (pc := pc) ?_⟩
        intro fact member
        exact propagateFact _ exitMember _ (by simpa [propagate, after] using member)
      | some recovery =>
        exact ⟨after, abstraction, propagateFact _ exitMember _ (by simp [propagate, after])⟩
  | @ret function initial pc before source result _ code _ ih =>
    have ⟨world, equivalent, member⟩ := ih he hw seeded
    rw [← he] at code
    obtain ⟨body, instruction, hf, hi, erases⟩ := instruction_matches code
    cases instruction <;> simp [Instruction.erase] at erases
    case ret stored =>
      subst stored
      obtain ⟨value, signature, reported⟩ := checked.ret member hf hi
      exact ⟨world, value, body, equivalent, reported, hf, signature⟩
  | @abort function initial pc before _ code ih =>
    have ⟨world, equivalent, member⟩ := ih he hw seeded
    rw [← he] at code
    obtain ⟨body, instruction, hf, hi, erases⟩ := instruction_matches code
    cases instruction <;> simp [Instruction.erase] at erases
    exact ⟨world, equivalent, checked.abort member hf hi⟩

theorem checked_execution (h : check program budget = .ok certificate)
    (run : Executes program.erase 0 {} result) :
    Covered program certificate.facts startEntry result := by
  have verified := check_sound h
  exact covers_execution verified run rfl rfl (verified.seed _ (by simp [seed, entrySeed]))

end RilAccess.Provenance
