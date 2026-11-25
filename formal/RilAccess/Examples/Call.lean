import RilAccess.Call.Proofs

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

namespace RilAccess.Calls.Examples

open Integrated

def fixed (access : Access) : MemberMode := ⟨false, access⟩
def slot (access : Access) : MemberMode := ⟨true, access⟩
def p (register : Nat) (fields : List Nat := []) : Path := ⟨register, fields⟩
def operations (atoms : List Atom) : Integrated.Syntax :=
  atoms.foldr (fun atom rest => .sequence (.command atom) rest) (.command .skip)
def access (atoms : List Atom) : Syntax := .access (operations atoms)
def arg (source formal : Nat) (mode : ParameterMode) : Argument := ⟨p source, formal, mode, mode⟩
def sequence (parts : List Syntax) : Syntax := parts.foldr Syntax.sequence (access [])
def accepted (program : Syntax) : Bool := (check program).isOk

/-- Evaluate provenance predicates (`formalMutated` / `formalRetained`) on a single call's frontier. -/
def inspectCall (setup : List Atom) (arguments : List Argument) (body : Syntax)
    (predicate : World → List World → Bool) : Bool :=
  match Integrated.infer (Integrated.lower (operations setup)) initialWorld with
  | .error _ => false
  | .ok [preWorld] =>
    match Integrated.infer (.sequence (.atom .enterScope) (prepare arguments)) preWorld with
    | .error _ => false
    | .ok [entry] =>
      match infer body entry with
      | .error _ => false
      | .ok frontier => predicate entry frontier
    | .ok _ => false
  | .ok _ => false

def mutate := sequence [access [.allocate 0 (fixed .mut) []],
  .invoke [arg 0 10 .mutable] [] (access [.write (p 10)])]
def observeVariable := sequence [access [.allocate 0 (slot .mut) [], .write (p 0)],
  .invoke [arg 0 10 .observe] [] (access [.read (p 10)]),
  access [.allocate 1 (fixed .mut) [], .assign (p 1) 0, .write (p 0)]]
def readAliased := sequence [access [.allocate 0 (fixed .mut) [], .write (p 0)],
  .invoke [arg 0 10 .observe, arg 0 11 .observe] [] (access [.read (p 10), .read (p 11)])]
def disjointWriters := sequence [access [.allocate 0 (fixed .mut) [], .allocate 1 (fixed .mut) []],
  .invoke [arg 0 10 .mutable, arg 1 11 .mutable] [] (access [.pairWrite (p 10) (p 11)])]
def aliasedWriters := sequence [access [.allocate 0 (fixed .mut) []],
  .invoke [arg 0 10 .mutable, arg 0 11 .mutable] [] (access [.pairWrite (p 10) (p 11)])]
def writeReadAlias := sequence [access [.allocate 0 (fixed .mut) []],
  .invoke [arg 0 10 .mutable, arg 0 11 .observe] [] (access [.write (p 10), .read (p 11)])]
def ordinaryWriteCannotRetain := sequence [access [.allocate 0 (fixed .mut) []],
  .invoke [arg 0 10 .mutable] [] (access [.retain (p 10)])]
def retainedWriter := sequence [access [.allocate 0 (fixed .mut) []],
  .invoke [arg 0 10 .retained] [] (access [.retain (p 10)])]
def writeAloneNotRetention := sequence [access [.allocate 0 (fixed .mut) []],
  .invoke [arg 0 10 .retained] [] (access [.write (p 10)])]
def callLocalSharingNotRetention := sequence [access [.allocate 0 (fixed .mut) []],
  .invoke [arg 0 10 .retained] []
    (access [.bind (p 10) 12 (fixed .shared), .write (p 12)])]
def retainedThroughAlias := sequence [access [.allocate 0 (fixed .mut) []],
  .invoke [arg 0 10 .retained] []
    (access [.bind (p 10) 12 (fixed .shared), .retain (p 12)])]
def nestedMutation := sequence [access [.allocate 0 (fixed .mut) []],
  .invoke [arg 0 10 .mutable] []
    (.invoke [arg 10 20 .mutable] [] (access [.write (p 20)]))]
def nestedRetention := sequence [access [.allocate 0 (fixed .mut) []],
  .invoke [arg 0 10 .retained] []
    (.invoke [arg 10 20 .retained] [] (access [.retain (p 20)]))]
def nestedRetentionFromTemporary := sequence [access [.allocate 0 (fixed .mut) []],
  .invoke [arg 0 10 .mutable] []
    (.invoke [arg 10 20 .retained] [] (access [.retain (p 20)]))]
def noCircularUse := sequence [access [.allocate 0 (fixed .mut) []],
  .invoke [arg 0 10 .mutable] []
    (.invoke [arg 10 20 .mutable] [] (access [.read (p 20)]))]
def possibleWrite := sequence [access [.allocate 0 (fixed .mut) []],
  .invoke [arg 0 10 .mutable] []
    (.branch (access [.write (p 10)]) (access [.read (p 10)]))]
def wrongMarker := sequence [access [.allocate 0 (fixed .mut) []],
  .invoke [⟨p 0, 10, .mutable, .observe⟩] [] (access [.write (p 10)])]
def rebindFormal := sequence [access [.allocate 0 (fixed .mut) []],
  .invoke [arg 0 10 .mutable] []
    (access [.allocate 12 (fixed .mut) [], .assign (p 12) 10, .write (p 10)])]
def constructInput := sequence [access [.allocate 0 (fixed .mut) []],
  .invoke [arg 0 10 .construction] [] (access [.write (p 10)])]
def observedInputIsNotConstruction := sequence [access [.allocate 0 (fixed .mut) [],
  .bind (p 0) 1 (fixed .ref), .write (p 0)],
  .invoke [arg 1 10 .construction] [] (access [.write (p 10)])]
def formalCannotEscape := sequence [access [.allocate 0 (fixed .mut) []],
  .invoke [arg 0 10 .mutable] [] (access [.write (p 10)]), access [.read (p 10)]]
def immutableInput := sequence [access [.allocate 0 (fixed .immutable) []],
  .invoke [arg 0 10 .immutable] [] (access [.read (p 10)])]
def mutablePlainInput := sequence [access [.allocate 0 (fixed .mut) []],
  .invoke [arg 0 10 .immutable] [] (access [.read (p 10)])]
def undeclaredCapture := sequence [access [.allocate 0 (fixed .mut) [], .allocate 1 (fixed .mut) []],
  .invoke [arg 0 10 .mutable] [] (access [.write (p 10), .write (p 1)])]
def declaredCapture := sequence [access [.allocate 0 (fixed .mut) [], .allocate 1 (fixed .mut) []],
  .invoke [arg 0 10 .mutable] [1] (access [.write (p 10), .write (p 1)])]
def independentCapture := sequence [access [.allocate 0 (fixed .mut) []],
  .invoke [arg 0 10 .mutable] [0] (access [.write (p 10), .read (p 0)])]
def aliasedRetainedWriters := sequence [access [.allocate 0 (fixed .mut) []],
  .invoke [arg 0 10 .retained, arg 0 11 .retained] [] (access [.retain (p 10), .retain (p 11)])]
def nestedMutCallFromAliasedSharedParticipants := sequence [access [.allocate 0 (fixed .mut) []],
  .invoke [arg 0 10 .retained, arg 0 11 .retained] []
    (sequence [.invoke [arg 10 20 .mutable] [] (access [.write (p 20)]),
      access [.retain (p 10), .retain (p 11)]])]
def exclusiveAndSharedParticipantsOverlap := sequence [access [.allocate 0 (fixed .mut) []],
  .invoke [arg 0 10 .mutable, arg 0 11 .retained] [] (access [.write (p 10), .retain (p 11)])]
def nestedMutCallOfAliasedSharedParticipantsOverlaps := sequence [access [.allocate 0 (fixed .mut) []],
  .invoke [arg 0 10 .retained, arg 0 11 .retained] []
    (sequence [.invoke [arg 10 20 .mutable, arg 11 21 .observe] []
        (access [.write (p 20), .read (p 21)]),
      access [.retain (p 10), .retain (p 11)]])]
def nestedMutCallFromMixedParticipants := sequence
  [access [.allocate 0 (fixed .mut) [], .allocate 1 (fixed .mut) []],
  .invoke [arg 0 10 .mutable, arg 1 11 .retained] []
    (sequence [.invoke [arg 10 20 .mutable, arg 11 21 .observe] []
        (access [.write (p 20), .read (p 21)]),
      access [.retain (p 11)]])]
def nestedMutCallWithCapture (aliased : Bool) := sequence
  [access [.allocate 0 (fixed .mut) [],
    if aliased then .bind (p 0) 1 (fixed .shared) else .allocate 1 (fixed .mut) []],
  access (if aliased then [] else [.write (p 1)]),
  .invoke [arg 0 10 .retained] [1]
    (sequence [access (if aliased then [.write (p 1)] else []),
      .invoke [arg 10 20 .mutable, arg 1 21 .observe] []
        (access [.write (p 20), .read (p 21)]),
      access [.retain (p 10)]])]
def coincidentRetainedWritersNeedIndependentUse := sequence [access [.allocate 0 (fixed .mut) []],
  .invoke [arg 0 10 .retained, arg 0 11 .retained] [] (access [.retain (p 10)])]
def formalAliasIsNotRetention := sequence [access [.allocate 0 (fixed .mut) [], .allocate 1 (fixed .mut) []],
  .invoke [arg 0 10 .retained, arg 1 11 .retained] [] (access [.retain (p 10)])]
def overwrittenPublication := sequence [access [.allocate 0 (fixed .mut) [],
  .bind (p 0) 1 (slot .shared), .allocate 2 (fixed .mut) []],
  .invoke [arg 2 10 .retained] [0, 1]
    (access [.assign (p 10) 1, .assign (p 0) 1]), access [.write (p 1)]]
def survivingPublication := sequence [access [.allocate 0 (fixed .mut) [],
  .bind (p 0) 1 (slot .shared), .allocate 2 (fixed .mut) []],
  .invoke [arg 2 10 .retained] [1]
    (access [.assign (p 10) 1]), access [.write (p 1)]]

structure ProgramExample where
  name : String
  sourceCase : String
  program : Syntax
  expected : Bool

def programs : List ProgramExample :=
  [⟨"call: mutable argument", "mutable_receiver_resumes_after_scoped_call", mutate, true⟩,
   ⟨"call: temporary observation pins current var target", "a_ref_argument_can_observe_a_replaceable_binding", observeVariable, true⟩,
   ⟨"call: read/read aliasing", "two_ref_arguments_can_observe_the_same_source", readAliased, true⟩,
   ⟨"call: disjoint mutable participants", "two_mutable_arguments_can_use_disjoint_sources", disjointWriters, true⟩,
   ⟨"call: aliased writers rejected", "overlapping_mut_writers", aliasedWriters, false⟩,
   ⟨"call: write/read conflict rejected", "overlapping_read_write", writeReadAlias, false⟩,
   ⟨"call: ordinary mut cannot retain", "mutable_formal_cannot_supply_a_retained_writer", ordinaryWriteCannotRetain, false⟩,
   ⟨"call: retained writer survives", "shared_return_retains", retainedWriter, true⟩,
   ⟨"call: write alone is not retention", "shared_parameter_not_retained", writeAloneNotRetention, false⟩,
   ⟨"call: local sharing is not outward retention", "local_sharing_does_not_retain_a_parameter", callLocalSharingNotRetention, false⟩,
   ⟨"call: retained alias keeps formal authority origin", "retaining_a_local_alias_keeps_its_formal_authority", retainedThroughAlias, true⟩,
   ⟨"call: nested mut forwarding", "nested_mutable_call_proves_the_outer_use", nestedMutation, true⟩,
   ⟨"call: nested retained forwarding", "nested_shared_call_preserves_retained_authority", nestedRetention, true⟩,
   ⟨"call: temporary forwarding cannot retain", "nested_shared_forwarding_cannot_retain_a_scoped_writer", nestedRetentionFromTemporary, false⟩,
   ⟨"call: forwarding cannot invent writable use", "forwarding_to_a_reader_does_not_exercise_writable_authority", noCircularUse, false⟩,
   ⟨"call: use on a retained alternative", "reachable_write_on_one_alternative_satisfies_mutable_use", possibleWrite, true⟩,
   ⟨"call: argument markers match exactly", "call_markers_must_match_a_mutable_formal", wrongMarker, false⟩,
   ⟨"call: formal slots are fixed", "mutable_formal_is_a_fixed_slot", rebindFormal, false⟩,
   ⟨"call: construction input", "a_new_argument_can_supply_construction_authority", constructInput, true⟩,
   ⟨"call: observed input has no construction authority", "a_read_only_argument_cannot_supply_construction_authority", observedInputIsNotConstruction, false⟩,
   ⟨"call: formal valid scope ends", "a_mutable_formal_cannot_be_read_from_its_caller", formalCannotEscape, false⟩,
   ⟨"call: immutable input", "immutable_snapshot_can_be_passed_as_a_plain_argument", immutableInput, true⟩,
   ⟨"call: plain input cannot publish a live writer", "a_plain_argument_requires_a_snapshot", mutablePlainInput, false⟩,
   ⟨"call: undeclared capture rejected", "a_named_helper_must_declare_its_capture", undeclaredCapture, false⟩,
   ⟨"call: declared independent capture", "independent_capture_and_mutable_argument_can_be_used_together", declaredCapture, true⟩,
   ⟨"call: captured alias is a separate participant", "named_callable_capture_overlaps_a_mutable_argument", independentCapture, false⟩,
   ⟨"call: aliased shared participants can both be retained", "coincident_shared_arguments_can_both_be_retained", aliasedRetainedWriters, true⟩,
   ⟨"call: unretained sibling ^mut formal rejected (E0527)", "retaining_one_shared_formal_does_not_retain_its_sibling", formalAliasIsNotRetention, false⟩,
   ⟨"call: overwritten publication is not surviving retention", "overwritten_outer_binding_does_not_retain_a_parameter", overwrittenPublication, false⟩,
   ⟨"call: outer binding roots surviving publication", "publication_survives_in_a_replaced_outer_binding", survivingPublication, true⟩,
   ⟨"call: an aliased shared participant can yield a nested call-scoped mut argument", "shared_participant_can_yield_a_nested_call_scoped_mut_argument", nestedMutCallFromAliasedSharedParticipants, true⟩,
   ⟨"call: exclusive and shared participants cannot overlap", "exclusive_argument_cannot_overlap_a_shared_argument", exclusiveAndSharedParticipantsOverlap, false⟩,
   ⟨"call: a nested call-scoped mut argument conflicts with an aliased observation", "distinct_shared_formals_do_not_prove_independence_for_a_nested_call", nestedMutCallOfAliasedSharedParticipantsOverlaps, false⟩,
   ⟨"call: a nested call-scoped mut argument conflicts with a shared captured alias", "shared_formal_and_capture_may_alias_during_a_nested_mut_call", nestedMutCallWithCapture true, false⟩,
   ⟨"call: a nested call-scoped mut argument can observe a disjoint capture", "read_only_capture_is_disjoint_from_shared_formal", nestedMutCallWithCapture false, true⟩,
   ⟨"call: a nested call-scoped mut argument excludes an aliased shared via instance", "exclusive_mut_argument_of_via_aliased_arguments_excludes_the_shared_pair", nestedMutCallOfAliasedSharedParticipantsOverlaps, false⟩,
   ⟨"call: mixed via modes permit a disjoint writer and observer", "exclusive_mut_argument_of_via_arguments_allows_forwarding_mixed_modes", nestedMutCallFromMixedParticipants, true⟩,
   ⟨"call: callback cannot use an aliased shared via instance", "higher_order_callback_requires_a_compatible_pair_of_root_modes", nestedMutCallOfAliasedSharedParticipantsOverlaps, false⟩,
   ⟨"call: callback selected from a record checks its via instance", "higher_order_callback_selected_from_a_record_checks_the_mode_pair", nestedMutCallOfAliasedSharedParticipantsOverlaps, false⟩,
   ⟨"call: coincident shared arguments do not merge their formal obligations", "retaining_one_shared_argument_cannot_satisfy_an_aliased_formal", coincidentRetainedWritersNeedIndependentUse, false⟩]

def sourceChecks : List (String × Bool) :=
  programs.map fun testCase => (testCase.sourceCase, accepted testCase.program)

/-- The interface records formal positions, even when actual arguments alias. -/
def publishedObligations : List (String × (List Nat × List Nat)) :=
  let setup := [.allocate 0 (fixed .mut) []]
  let sharedPair := [arg 0 10 .retained, arg 0 11 .retained]
  let retainPair := access [.retain (p 10), .retain (p 11)]
  let contracts : List (String × List Argument × Syntax) :=
    [("published_mutation_has_no_retention", [arg 0 10 .mutable], access [.write (p 10)]),
     ("published_root_retention_does_not_write", [arg 0 10 .retained], access [.retain (p 10)]),
     ("published_shared_pair_retains_both_formals", sharedPair, retainPair),
     ("published_nested_mut_call_writes_only_its_formal", sharedPair,
       sequence [.invoke [arg 10 20 .mutable] [] (access [.write (p 20)]), retainPair])]
  contracts.map fun (name, arguments, body) =>
    let collect := fun predicate =>
      (List.range arguments.length).filter fun position =>
        arguments[position]?.any fun argument =>
          inspectCall setup arguments body (fun entry front => predicate entry front argument.formal)
    (name, (collect formalMutated, collect formalRetained))

def examples : List (String × Bool) :=
  programs.map fun testCase => (testCase.name, accepted testCase.program == testCase.expected)

theorem examples_all_pass : examples.all Prod.snd = true := by decide +kernel

theorem source_cases_unique : (programs.map ProgramExample.sourceCase).Nodup := by decide

theorem retained_alias_keeps_formal_origin :
    inspectCall [.allocate 0 (fixed .mut) []] [arg 0 10 .retained]
      (access [.bind (p 10) 12 (fixed .shared), .retain (p 12)])
      (fun entry front => formalRetained entry front 10) = true := by decide +kernel

end RilAccess.Calls.Examples
