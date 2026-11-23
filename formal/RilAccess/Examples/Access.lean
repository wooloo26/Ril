import RilAccess.Access.Footprints

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

namespace RilAccess.Integrated.Examples

def fixed (access : Access) : MemberMode := ⟨false, access⟩
def replaceableMode (access : Access) : MemberMode := ⟨true, access⟩
def path (register : Nat) (fields : List Nat := []) : Path := ⟨register, fields⟩
def command (atom : Atom) : Syntax := .command atom
def sequence (commands : List Syntax) : Syntax :=
  commands.foldr Syntax.sequence (.command .skip)
def atoms (operations : List Atom) : Syntax := sequence (operations.map command)
def accepted (program : Syntax) : Bool := (check program).isOk

def immutableRead := atoms [.allocate 0 (fixed .immutable) [], .read (path 0)]
def immutableWrite := atoms [.allocate 0 (fixed .immutable) [], .write (path 0)]
def localWrite := atoms [.allocate 0 (fixed .mut) [], .write (path 0)]
def idleWriter := atoms [.allocate 0 (fixed .mut) [], .read (path 0)]
def liveObserver := atoms [.allocate 0 (fixed .mut) [], .bind (path 0) 1 (fixed .ref),
  .write (path 0), .read (path 1)]
def observerUpgrade := atoms [.allocate 0 (fixed .mut) [], .bind (path 0) 1 (fixed .ref), .write (path 1)]
def sharedWriter := atoms [.allocate 0 (fixed .mut) [], .bind (path 0) 1 (fixed .shared), .write (path 1)]
def exclusiveAlias := atoms [.allocate 0 (fixed .mut) [], .bind (path 0) 1 (fixed .mut), .write (path 1)]
def livePublication := atoms [.allocate 0 (fixed .mut) [], .bind (path 0) 1 (fixed .immutable)]
def fixedReplacement := atoms [.allocate 0 (fixed .immutable) [], .allocate 1 (fixed .immutable) [],
  .assign (path 1) 0]
def variableImmutable := atoms [.allocate 0 (replaceableMode .immutable) [], .allocate 1 (fixed .immutable) [],
  .assign (path 1) 0, .read (path 0)]
def variableConstruction := atoms [.allocate 0 (replaceableMode .mut) [], .allocate 1 (fixed .mut) [],
  .assign (path 1) 0, .write (path 0)]
def variableCannotHandoff := atoms [.allocate 0 (replaceableMode .mut) [], .handoff 0 1, .write (path 1)]
def variableNotPinned := atoms [.allocate 0 (replaceableMode .mut) [], .bind (path 0) 1 (fixed .ref)]
def oldSharedAliasSurvives := atoms [.allocate 0 (replaceableMode .mut) [],
  .bind (path 0) 1 (fixed .shared), .write (path 1), .allocate 2 (fixed .mut) [],
  .assign (path 2) 0, .write (path 0), .write (path 1)]
def validHandoff := atoms [.allocate 0 (fixed .mut) [], .bind (path 0) 1 (fixed .ref),
  .handoff 0 2, .write (path 2)]
def movedSource := atoms [.allocate 0 (fixed .mut) [], .handoff 0 1, .write (path 0)]
def movedObserver := atoms [.allocate 0 (fixed .mut) [], .bind (path 0) 1 (fixed .ref),
  .handoff 0 2, .write (path 2), .read (path 1)]
def sharedPreventsHandoff := atoms [.allocate 0 (fixed .mut) [],
  .bind (path 0) 1 (fixed .shared), .write (path 1), .handoff 0 2]

def validScopedAccess := sequence [command (.allocate 0 (fixed .mut) []),
  .scopedStep (path 0) 1 (command (.write (path 1))), command (.write (path 0))]
def independentScopedWrite := sequence [command (.allocate 0 (fixed .mut) []),
  .scopedStep (path 0) 1 (command (.write (path 0)))]
def independentScopedRead := sequence [command (.allocate 0 (fixed .mut) []),
  .scopedStep (path 0) 1 (atoms [.write (path 1), .read (path 0)])]
def nestedScopedAccess := sequence [command (.allocate 0 (fixed .mut) []),
  .scopedStep (path 0) 1 (sequence [.scopedStep (path 1) 2 (command (.write (path 2))),
    command (.write (path 1))]), command (.write (path 0))]
def temporarySharing := sequence [command (.allocate 0 (fixed .mut) []),
  .scopedStep (path 0) 1 (atoms [.bind (path 1) 2 (fixed .shared), .write (path 2)])]
def temporaryRetention := sequence [command (.allocate 0 (fixed .mut) []),
  .scopedStep (path 0) 1 (command (.retain (path 1)))]
def idleScopedAccess := sequence [command (.allocate 0 (fixed .mut) []),
  .scopedStep (path 0) 1 (command (.read (path 1)))]
def endedScopedObserver := sequence [command (.allocate 0 (fixed .mut) []),
  .scopedStep (path 0) 1 (atoms [.bind (path 1) 2 (fixed .ref), .read (path 2), .write (path 1)]),
  command (.read (path 2))]
def escapingScopedObserver := sequence [command (.allocate 0 (fixed .mut) []),
  command (.bind (path 0) 2 (replaceableMode .ref)),
  .scopedStep (path 0) 1 (atoms [.write (path 1), .assign (path 1) 2])]
def suspendedReplacement := sequence [command (.allocate 0 (replaceableMode .mut) []),
  .scopedStep (path 0) 1 (atoms [.allocate 2 (fixed .mut) [], .assign (path 2) 0, .write (path 1)])]

def scalarSchema (replaceable : Bool) : Schema :=
  [⟨[0], ⟨replaceable, .immutable⟩, false⟩]
def scalarReplacement := atoms [.allocate 0 (fixed .mut) (scalarSchema true),
  .replaceScalar (path 0 [0])]
def fixedScalarReplacement := atoms [.allocate 0 (fixed .mut) (scalarSchema false),
  .replaceScalar (path 0 [0])]
def scalarNotObject := atoms [.allocate 0 (fixed .mut) (scalarSchema true), .write (path 0 [0])]
def immutableSuppressesSlot := atoms [.allocate 0 (fixed .immutable) (scalarSchema true),
  .replaceScalar (path 0 [0])]
def observerSuppressesSlot := atoms [.allocate 0 (fixed .mut) (scalarSchema true),
  .bind (path 0) 1 (fixed .ref), .replaceScalar (path 1 [0])]
def plainMember := atoms [.allocate 0 (fixed .mut) [⟨[0], fixed .immutable, true⟩],
  .bind (path 0 [0]) 1 (fixed .shared), .write (path 1)]
def disjointMembers := atoms [.allocate 0 (fixed .mut)
  [⟨[0], fixed .mut, true⟩, ⟨[1], fixed .mut, true⟩],
  .pairWrite (path 0 [0]) (path 0 [1])]
def overlappingPair := atoms [.allocate 0 (fixed .mut) [],
  .bind (path 0) 1 (fixed .shared), .pairWrite (path 0) (path 1)]
def nestedMember := atoms [.allocate 0 (fixed .mut)
  [⟨[0], fixed .mut, true⟩, ⟨[0, 0], ⟨true, .immutable⟩, false⟩],
  .replaceScalar (path 0 [0, 0])]
def missingMember := atoms [.allocate 0 (fixed .mut) [], .write (path 0 [99])]

def permute := sequence [command (.allocate 0 (fixed .mut) []),
  command (.allocate 1 (fixed .mut) []),
  command (.bind (path 0) 2 (replaceableMode .shared)),
  command (.bind (path 1) 3 (replaceableMode .shared)),
  .branch (atoms [.assign (path 0) 2, .assign (path 1) 3])
    (atoms [.assign (path 1) 2, .assign (path 0) 3]),
  command (.pairWrite (path 2) (path 3))]
def uncertainOverlap := sequence [command (.allocate 0 (fixed .mut) []),
  command (.allocate 1 (fixed .mut) []),
  command (.bind (path 0) 2 (replaceableMode .shared)),
  command (.bind (path 1) 3 (replaceableMode .shared)),
  .branch (atoms [.assign (path 0) 2, .assign (path 1) 3])
    (atoms [.assign (path 0) 2, .assign (path 0) 3]),
  command (.pairWrite (path 2) (path 3))]
def scopeEnded := sequence [.block (atoms [.allocate 0 (fixed .mut) [], .write (path 0)]),
  command (.read (path 0))]
def retainedPreventsHandoff := atoms [.allocate 0 (fixed .mut) [], .retain (path 0), .handoff 0 1]
def scopedRetention : Syntax := .block (atoms [.allocate 0 (fixed .mut) [], .retain (path 0)])
def possibleUse := sequence [command (.allocate 0 (fixed .mut) []),
  .branch (command (.write (path 0))) (command (.read (path 0)))]
def unclosed := atoms [.enterScope, .allocate 0 (fixed .immutable) []]
def rootless := atoms [.write (path 0)]

def injectedScopeEnd := sequence [command (.allocate 0 (fixed .mut) []),
  .scopedStep (path 0) 1 (atoms [.leaveScope, .write (path 0), .enterScope])]

def duplicatedDeclaration := Syntax.branch
  (atoms [.allocate 0 (fixed .mut) [], .write (path 0)])
  (atoms [.allocate 0 (fixed .mut) [], .read (path 0)])
def orphanField := atoms [.allocate 0 (fixed .immutable) [⟨[0, 1], fixed .mut, true⟩]]
def duplicateField := atoms [.allocate 0 (fixed .immutable)
  [⟨[0], fixed .mut, true⟩, ⟨[0], fixed .immutable, true⟩]]
def scalarObserver := atoms [.allocate 0 (fixed .mut) (scalarSchema true),
  .bind (path 0 [0]) 1 (fixed .ref)]
def scopeSharedEscape := sequence [command (.allocate 0 (fixed .mut) []),
  command (.bind (path 0) 1 (replaceableMode .shared)),
  .block (atoms [.allocate 2 (fixed .mut) [], .assign (path 2) 1]), command (.write (path 1))]
def scopeEscapePreventsHandoff := sequence [command (.allocate 0 (fixed .mut) []),
  command (.bind (path 0) 1 (replaceableMode .shared)),
  .block (atoms [.allocate 2 (fixed .mut) [], .assign (path 2) 1, .handoff 2 3]),
  command (.write (path 1))]
def chainedHandoff := atoms [.allocate 0 (fixed .mut) [], .bind (path 0) 1 (fixed .ref),
  .handoff 0 2, .handoff 2 3, .write (path 3)]
def laterSharedReception := atoms [.allocate 0 (replaceableMode .shared) [],
  .write (path 0), .allocate 1 (fixed .mut) [], .assign (path 1) 0, .write (path 0)]
def sharedWriterWithoutReception := atoms [.allocate 0 (replaceableMode .shared) [], .write (path 0)]

def confinedResult (program : Syntax) (scope : Nat) : Bool :=
  match check program with
  | .error _ => false
  | .ok analysis => analysis.worlds.all fun world =>
      confinedTo world scope ⟨0, [], ⟨.allocation, 0⟩⟩

def forgedMemberRejected : Bool :=
  let schema := [Field.mk [0] (fixed .immutable) true]
  let world := (transfer initialWorld (.allocate 0 (fixed .mut) schema)).getD initialWorld
  match resolve world (path 0 [0]) with
  | none => false
  | some resolved =>
    let forged := { resolved with
      members := [], effective := .shared,
      binding := { resolved.binding with mode := fixed .shared } }
    let accessCheck : AccessCheck := ⟨⟨.write, resolved.pointer⟩, .write, forged, [], []⟩
    authorizedLocal accessCheck && !authorized accessCheck

structure ProgramExample where
  name : String
  program : Syntax
  expected : Bool
  sourceCase : Option String

def programs : List ProgramExample :=
  [⟨"immutable read", immutableRead, true, some "immutable_record_can_be_read"⟩,
   ⟨"immutable write rejected", immutableWrite, false, some "immutable_root_cannot_supply_a_mutable_argument"⟩,
   ⟨"local writable use", localWrite, true, some "local_mutates_record"⟩,
   ⟨"idle writer rejected", idleWriter, false, some "idle_local_writer_requires_writable_use"⟩,
   ⟨"live observer", liveObserver, true, some "live_observer_sees_an_existing_writer"⟩,
   ⟨"observer upgrade rejected", observerUpgrade, false, some "observer_root_cannot_supply_a_mutable_argument"⟩,
   ⟨"shared writer", sharedWriter, true, some "explicit_local_shared_alias_can_write"⟩,
   ⟨"exclusive alias rejected", exclusiveAlias, false, some "persistent_mutable_alias_requires_acknowledgment"⟩,
   ⟨"live publication rejected", livePublication, false, some "local_snapshot_cannot_publish_a_live_writer"⟩,
   ⟨"fixed replacement rejected", fixedReplacement, false, some "immutable_object_slot_rejects_replacement"⟩,
   ⟨"var immutable replacement", variableImmutable, true, some "immutable_var_slot_can_receive_another_snapshot"⟩,
   ⟨"var mutable construction input", variableConstruction, true, some "mutable_var_slot_can_receive_a_new_object"⟩,
   ⟨"var construction qualification rejected", variableCannotHandoff, false, some "mutable_var_slot_cannot_supply_handoff_qualification"⟩,
   ⟨"var root is not pinned", variableNotPinned, false, some "a_ref_view_cannot_anchor_a_variable_slot"⟩,
   ⟨"old alias survives replacement", oldSharedAliasSurvives, true, some "shared_alias_survives_replacement_of_its_original_slot"⟩,
   ⟨"qualified handoff", validHandoff, true, some "explicit_handoff_keeps_unrelated_path"⟩,
   ⟨"ended handoff source rejected", movedSource, false, some "handoff_ends_binding"⟩,
   ⟨"ended derived observer rejected", movedObserver, false, some "handoff_ends_dependent_view"⟩,
   ⟨"shared root cannot hand off", sharedPreventsHandoff, false, some "live_shared_writer_prevents_exclusive_handoff"⟩,
   ⟨"block-scoped hold", validScopedAccess, true, some "mutable_receiver_resumes_after_scoped_call"⟩,
   ⟨"independent write under active hold rejected", independentScopedWrite, false, some "mutable_closure_capture_overlaps_a_mutable_argument"⟩,
   ⟨"independent read under active write hold rejected", independentScopedRead, false, some "named_callable_capture_overlaps_a_mutable_argument"⟩,
   ⟨"nested scoped holds", nestedScopedAccess, true, some "nested_mutable_call_proves_the_outer_use"⟩,
   ⟨"temporary sharing rejected", temporarySharing, false, some "temporary_mutable_parameter_cannot_form_shared_alias"⟩,
   ⟨"temporary retention rejected", temporaryRetention, false, some "mutable_formal_cannot_supply_a_retained_writer"⟩,
   ⟨"idle temporary writer rejected", idleScopedAccess, false, some "mutable_parameter_requires_write"⟩,
   ⟨"ended scoped view rejected", endedScopedObserver, false, some "a_view_of_a_mutable_argument_is_unavailable_after_its_call"⟩,
   ⟨"escaping scoped view rejected", escapingScopedObserver, false, some "call_scoped_writer_cannot_be_stored_as_a_ref"⟩,
   ⟨"suspended root replacement rejected", suspendedReplacement, false, some "mutable_argument_blocks_overlapping_captured_slot_replacement"⟩,
   ⟨"scalar slot replacement", scalarReplacement, true, some "mutable_record_can_replace_a_scalar_slot"⟩,
   ⟨"fixed scalar slot rejected", fixedScalarReplacement, false, some "fixed_scalar_member_cannot_be_replaced"⟩,
   ⟨"scalar is not an object", scalarNotObject, false, some "scalar_member_cannot_supply_a_mutable_object"⟩,
   ⟨"immutable suppresses var member", immutableSuppressesSlot, false, some "immutable_record_suppresses_replaceable_member"⟩,
   ⟨"observer suppresses var member", observerSuppressesSlot, false, some "live_observer_cannot_replace_a_member"⟩,
   ⟨"plain member grants no writer", plainMember, false, some "immutable_member_cannot_supply_a_shared_writer"⟩,
   ⟨"disjoint members", disjointMembers, true, some "exact_fields_are_separate_mutable_arguments"⟩,
   ⟨"alias overlap rejected", overlappingPair, false, some "overlapping_mut_writers"⟩,
   ⟨"nested member path", nestedMember, true, some "nested_writable_member_can_replace_a_scalar_slot"⟩,
   ⟨"unknown member rejected", missingMember, false, some "writes_require_a_declared_member"⟩,
   ⟨"correlated permute", permute, true, some "exclusive_arguments_remain_disjoint_when_branches_swap_them"⟩,
   ⟨"possible overlap rejected", uncertainOverlap, false, some "a_conditional_overlapping_pair_cannot_receive_exclusive_borrows"⟩,
   ⟨"scope expiry", scopeEnded, false, some "scoped_local_is_unavailable_after_its_block"⟩,
   ⟨"retention ends qualification", retainedPreventsHandoff, false, some "captured_writer_prevents_handoff"⟩,
   ⟨"retention survives scope", scopedRetention, true, some "publication_survives_in_a_caller_member"⟩,
   ⟨"use on one retained branch", possibleUse, true, some "reachable_write_on_one_alternative_satisfies_mutable_use"⟩,
   ⟨"unclosed scope rejected", unclosed, false, none⟩,
   ⟨"rootless path rejected", rootless, false, some "writes_require_a_declared_root"⟩,
   ⟨"scope bookkeeping cannot be injected", injectedScopeEnd, false, none⟩,
   ⟨"declaration identities are globally unique", duplicatedDeclaration, false, none⟩,
   ⟨"orphan schema path rejected", orphanField, false, none⟩,
   ⟨"duplicate schema field rejected", duplicateField, false, some "record_schema_cannot_repeat_a_member"⟩,
   ⟨"scalar cannot receive ref", scalarObserver, false, some "scalar_member_cannot_anchor_a_ref_view"⟩,
   ⟨"scope escape is inferred", scopeSharedEscape, true, some "shared_alias_can_leave_a_block"⟩,
   ⟨"inferred escape prevents handoff", scopeEscapePreventsHandoff, false, some "shared_alias_leaving_a_block_prevents_handoff"⟩,
   ⟨"ended paths permit subsequent handoff", chainedHandoff, true, some "exclusive_handoff_can_continue_from_the_new_binding"⟩,
   ⟨"later shared assignment justifies var shared reception", laterSharedReception, true, some "shared_var_can_receive_its_existing_writer_on_replacement"⟩,
   ⟨"writing alone does not justify shared local reception", sharedWriterWithoutReception, false, some "writing_a_fresh_shared_local_does_not_satisfy_reception"⟩]

/-- Raw judgments from the same programs checked by the standalone Lean suite. -/
def sourceChecks : List (String × Bool) :=
  programs.filterMap fun testCase =>
    testCase.sourceCase.map fun name => (name, accepted testCase.program)

def examples : List (String × Bool) :=
  (programs.map fun testCase => (testCase.name, accepted testCase.program == testCase.expected)) ++
  [("generated confined footprint", confinedResult localWrite 0),
   ("outside authority blocks confinement", !confinedResult localWrite 1),
   ("publication blocks confinement", !confinedResult scopedRetention 0),
   ("original schema rejects forged path modes", forgedMemberRejected)]

theorem examples_all_pass : examples.all Prod.snd = true := by decide +kernel

theorem source_cases_unique : (programs.filterMap ProgramExample.sourceCase).Nodup := by decide

theorem permute_two_worlds :
    (check permute).toOption.map (fun analysis => analysis.worlds.length) = some 2 := by decide +kernel

theorem accepted_has_real_execution :
    (sourceExecute localWrite initialWorld.raw).length = 1 ∧ accepted localWrite = true := by decide +kernel

end RilAccess.Integrated.Examples
