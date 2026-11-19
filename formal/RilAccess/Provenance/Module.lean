import RilAccess.Provenance.Certificate

namespace RilAccess.Provenance

/-- A body-derived interface for a normalized call entry. The consumer needs
    its slot schemas and signature, along with the projected boundary facts. -/
structure EntrySummary where
  private mk ::
  entry : Entry
  parameters : List ParameterMode
  signature : Signature
  slots : List Slot
  outcomes : List CallFact
  deriving Repr

def summarize (program : Program) (entry : Entry) (budget : Nat := 256) :
    Except Diagnostic EntrySummary := do
  let some body := program.functions[entry.function]? | throw ⟨entry.function, 0, .missingInstruction⟩
  let certificate ← checkEntry program entry budget
  let outcomes := (certificate.facts.filterMap (Judgment.callFact entry)).eraseDups
  return ⟨entry, body.parameters, body.signature, program.slots, outcomes⟩

def EntrySummary.apply (summary : EntrySummary) (program : Program) (caller : Entry)
    (pc next : Nat) (before : World) (arguments : List Argument)
    (receiver : Option (Register × Access)) (onAbort : Option Nat := none) : Except Error (List Judgment) := do
  require (decide (program.slots = summary.slots)) .schema
  let signature : Function := ⟨summary.parameters, summary.signature, []⟩
  let call ← prepare signature before arguments
  require (decide (call.entered = summary.entry.world)) .summaryEntry
  let outcomes := summary.outcomes.flatMap (applyCallFact program caller pc next call receiver onAbort)
  match (failures outcomes).head? with
  | none => return outcomes
  | some diagnostic => .error diagnostic.error

theorem summarized_body (h : summarize program entry budget = .ok summary) :
    ∃ body certificate, program.functions[entry.function]? = some body ∧
      checkEntry program entry budget = .ok certificate ∧
      summary = ⟨entry, body.parameters, body.signature, program.slots,
        (certificate.facts.filterMap (Judgment.callFact entry)).eraseDups⟩ := by
  unfold summarize at h
  cases hb : program.functions[entry.function]? with
  | none => simp [hb, throw] at h
  | some body =>
    cases hc : checkEntry program entry budget with
    | error error => simp [hb, hc] at h
    | ok certificate =>
      simp [hb, hc] at h
      exact ⟨body, certificate, rfl, rfl, h.symm⟩

def SummaryCovers (program : Program) (summary : EntrySummary) (frozen : RawFrame) :
    Position RawFrame → Prop
  | .at pc frame =>
    ∀ body alternatives next action register,
      program.functions[summary.entry.function]? = some body →
      body.code[pc]? = some (.step alternatives next) →
      action ∈ alternatives → action.writer = some register →
      ∃ object localAllocation, frame.get register = some object ∧
        .write object.allocationClass localAllocation ∈ summary.outcomes
  | .returned source frame =>
    ∃ (world : World) (value : Returned) (body : Function), world.raw = frame.abstract ∧
      .returned source world value ∈ summary.outcomes ∧
      program.functions[summary.entry.function]? = some body ∧
      body.signature = summary.signature ∧
      ReturnGuarantee program body frozen frame world source value ∧
      Includes value.contained summary.signature.contained
  | .aborted frame =>
    ∃ world : World, world.raw = frame.abstract ∧ .aborted world ∈ summary.outcomes

theorem summarize_sound (h : summarize program entry budget = .ok summary)
    (he : entry.world.raw = frozen.abstract)
    (run : Executes program.erase entry.function frozen result) :
    SummaryCovers program summary frozen result := by
  obtain ⟨body, certificate, hb, hc, rfl⟩ := summarized_body h
  have checked := checkEntry_sound hc
  have started := checked.seed (.point entry 0 entry.world) (by simp [entrySeed])
  obtain ⟨covered, safe⟩ := verified_execution checked run he started
  cases result with
  | «at» pc frame =>
    intro reachedBody alternatives next action register present instruction listed writer
    obtain ⟨world, hw, point⟩ := covered
    obtain ⟨after, uses, valid, _⟩ := checked.primitive point present instruction listed
    obtain ⟨object, view, concrete, path, _⟩ := primitive_authorized valid hw writer
    have written : Judgment.writesObject entry object.allocationClass view.localAllocation ∈ certificate.facts := by
      apply checked.stable _ point
      have nonempty : alternatives.isEmpty = false := by
        cases alternatives <;> simp_all
      simp only [expand, present, instruction, nonempty, Bool.false_eq_true, if_false]
      exact List.mem_flatMap.mpr ⟨action, listed, by simp [valid, writer, path]⟩
    exact ⟨object, view.localAllocation, concrete, List.mem_eraseDups.mpr
      (List.mem_filterMap.mpr ⟨_, written, by simp⟩)⟩
  | returned source frame =>
    obtain ⟨world, value, actualBody, hw, member, hi, hr⟩ := covered
    have same := Option.some.inj (hi.symm.trans hb)
    subst actualBody
    exact ⟨world, value, body, hw, List.mem_eraseDups.mpr (List.mem_filterMap.mpr
      ⟨_, member, by simp⟩), hb, rfl, checked_return_sound he hw hr, declared_contains checked started member hb⟩
  | aborted frame =>
    obtain ⟨world, hw, member⟩ := covered
    exact ⟨world, hw, List.mem_eraseDups.mpr (List.mem_filterMap.mpr ⟨_, member, by simp⟩)⟩

theorem summarize_at_call {before : World} {caller frozen : RawFrame}
    (h : summarize program ⟨callee, prepared.entered⟩ budget = .ok summary)
    (preparedCall : prepare signature before arguments = .ok prepared)
    (callerMatches : before.raw = caller.abstract)
    (evaluated : caller.prepare (arguments.map Argument.source) = some frozen)
    (run : Executes program.erase callee frozen result) :
    Includes (prepared.caller.external ++ prepared.caller.liveObjects) prepared.entered.outside ∧
    SummaryCovers program summary frozen result := by
  have snapshot := prepare_raw preparedCall
  rw [callerMatches, RawFrame.prepare_abstract, evaluated] at snapshot
  exact ⟨prepared_external_roots preparedCall, summarize_sound h (Option.some.inj snapshot).symm run⟩

/-- The same transfer consumes a summary during the fixed point and after it
    has been exported for independent checking of a continuation. -/
theorem exported_transfer (h : summarize provider entry budget = .ok summary)
    (applied : summary.apply program caller pc next before arguments receiver onAbort = .ok outputs)
    (fact : CallFact) (member : fact ∈ summary.outcomes) :
    ∃ prepared, prepare ⟨summary.parameters, summary.signature, []⟩ before arguments = .ok prepared ∧
      prepared.entered = entry.world ∧
      Includes (applyCallFact program caller pc next prepared receiver onAbort fact) outputs := by
  obtain ⟨body, cert, hb, hc, hx⟩ := summarized_body h
  have summaryEntry : summary.entry = entry := congrArg EntrySummary.entry hx
  by_cases hs : program.slots = summary.slots
  · cases hp : prepare ⟨summary.parameters, summary.signature, []⟩ before arguments with
    | error error => simp [EntrySummary.apply, hs, hp, require] at applied
    | ok prepared =>
      by_cases he : prepared.entered = summary.entry.world
      · simp [EntrySummary.apply, hs, hp, he, require] at applied
        split at applied
        · simp at applied
          subst outputs
          refine ⟨prepared, rfl, ?_, ?_⟩
          · exact he.trans (congrArg Entry.world summaryEntry)
          · intro emitted hm
            exact List.mem_flatMap.mpr ⟨fact, member, hm⟩
        · simp at applied
      · simp [EntrySummary.apply, hs, hp, he, require] at applied
  · simp [EntrySummary.apply, hs, require] at applied

end RilAccess.Provenance
