import RilAccess.Provenance.Returns

namespace RilAccess.Provenance

theorem declared_contains (checked : Checked program facts inputs)
    (activated : Judgment.point entry 0 entry.world ∈ facts)
    (returned : Judgment.returned entry source world value ∈ facts)
    (hf : program.functions[entry.function]? = some function) :
    Includes value.contained function.signature.contained := by
  have entryListed : entry ∈ entries facts :=
    List.mem_eraseDups.mpr (List.mem_filterMap.mpr ⟨_, activated, rfl⟩)
  have interface := checked.interfaces entry entryListed
  simp [checkInterface, hf, need, require] at interface
  split at interface
  · split at interface
    · split at interface
      · rename_i agreesCheck
        intro old hold
        have inferred : old ∈ inferredContained facts entry :=
          List.mem_flatMap.mpr ⟨_, returned, by simpa using hold⟩
        have row := Bool.and_eq_true_iff.mp agreesCheck.2
        exact List.contains_iff_mem.mp (List.all_eq_true.mp row.2 _ inferred)
      · simp at interface
    · simp at interface
  · simp at interface

def NextSafe (program : Program) (facts : List Judgment) (entry : Entry) (frozen frame : RawFrame)
    (pc : Nat) (function : Function) : Instruction → Prop
  | .branch targets =>
    targets ≠ [] ∧ ∀ next ∈ targets, Covered program facts entry (.at next frame)
  | .step alternatives next =>
    alternatives ≠ [] ∧ ∀ action ∈ alternatives, ∃ after,
      runPrim action.erase frame = some after ∧ Covered program facts entry (.at next after) ∧
      LocalSafety facts entry pc frame action
  | .invoke callee arguments _ _ _ =>
    ∃ (prepared : Prepared) (actuals : List (Object × ParameterMode)) (entered : RawFrame),
      frame.prepare (arguments.map Argument.source) = some entered ∧
      argumentsAt frame arguments = some actuals ∧ ConcreteSeparate frame.memory.heap actuals ∧
      prepared.entered.raw = entered.abstract ∧
      Covered program facts ⟨callee, prepared.entered⟩ (.at 0 entered)
  | .ret source =>
    ∃ world value returned, frame.returnValue source = some returned ∧
      ReturnGuarantee program function frozen frame world source value ∧
      Covered program facts entry (.returned source frame)
  | .abort => Covered program facts entry (.aborted frame)

theorem checked_point_safe (checked : Checked program facts inputs)
    (covered : Covered program facts entry (.at pc frame)) (hfrozen : entry.world.raw = frozen.abstract) :
    ∃ (function : Function) (instruction : Instruction),
      program.functions[entry.function]? = some function ∧ function.code[pc]? = some instruction ∧
      NextSafe program facts entry frozen frame pc function instruction := by
  obtain ⟨world, hw, point⟩ := covered
  obtain ⟨function, instruction, hf, hi⟩ := checked.instruction point
  refine ⟨function, instruction, hf, hi, ?_⟩
  cases instruction with
  | branch targets =>
    have nonempty : targets ≠ [] := by
      intro empty
      exact checked.noRejection entry.function pc .invalidProgram
        (checked.stable _ point _ (by simp [expand, hf, hi, empty]))
    refine ⟨nonempty, ?_⟩
    intro next selected
    exact ⟨world, hw, checked.stable _ point _ (by simp [expand, hf, hi, nonempty, selected])⟩
  | step alternatives next =>
    have nonempty : alternatives ≠ [] := by
      intro empty
      exact checked.noRejection entry.function pc .invalidProgram
        (checked.stable _ point _ (by simp [expand, hf, hi, empty]))
    exact ⟨nonempty, fun action member => checked_step_ready checked ⟨world, hw, point⟩ hf hi member⟩
  | invoke => exact checked_call_ready checked ⟨world, hw, point⟩ hf hi
  | ret => exact checked_return_ready checked hfrozen ⟨world, hw, point⟩ hf hi
  | abort =>
    exact ⟨world, hw, checked.abort point hf hi⟩

def RuntimeGuarantee (program : Program) (facts : List Judgment) (entry : Entry) (frozen : RawFrame) :
    Position RawFrame → Prop
  | .at pc frame =>
    ∃ (function : Function) (instruction : Instruction),
      program.functions[entry.function]? = some function ∧ function.code[pc]? = some instruction ∧
      NextSafe program facts entry frozen frame pc function instruction
  | .returned source frame =>
    ∃ (function : Function) (world : World) (value : Returned),
      program.functions[entry.function]? = some function ∧
      ReturnGuarantee program function frozen frame world source value ∧
      Includes value.contained function.signature.contained
  | .aborted _ => True

/-- A certificate applies to any finite prefix starting at an activated frame.
    Call readiness activates the callee before requiring any normal exit. -/
theorem verified_execution (checked : Checked program facts inputs)
    (run : Executes program.erase entry.function frozen result)
    (entrySnapshot : entry.world.raw = frozen.abstract)
    (activated : Judgment.point entry 0 entry.world ∈ facts) :
    Covered program facts entry result ∧ RuntimeGuarantee program facts entry frozen result := by
  have coverage := covers_execution checked run rfl entrySnapshot activated
  refine ⟨coverage, ?_⟩
  cases result with
  | «at» pc frame => exact checked_point_safe checked coverage entrySnapshot
  | returned source frame =>
    obtain ⟨world, value, function, hw, member, body, valid⟩ := coverage
    exact ⟨function, world, value, body, checked_return_sound entrySnapshot hw valid,
      declared_contains checked activated member body⟩
  | aborted _ => trivial

theorem verified_program (accepts : check program budget = .ok certificate) :
    Checked program certificate.facts ∧
    ∀ result, Executes program.erase 0 {} result →
      Covered program certificate.facts startEntry result ∧
      RuntimeGuarantee program certificate.facts startEntry {} result := by
  have verified := check_sound accepts
  exact ⟨verified, fun _ run => verified_execution verified run rfl (verified.seed _ (by simp [seed, entrySeed]))⟩

end RilAccess.Provenance
