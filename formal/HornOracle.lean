import Lean
import RilAccess.Examples.Boundary
import RilAccess.Examples.Call
import RilAccess.Examples.Composition
import RilAccess.Examples.Draft
import RilAccess.Examples.Graph
import RilAccess.Examples.Handoff
import RilAccess.Examples.RecursiveStorage
import RilAccess.Examples.ResolvedProvenance
import RilAccess.Examples.Scoped
import RilAccess.Examples.Concurrency
import RilAccess.Examples.Summary
import RilAccess.Examples.Visibility
import RilAccess.Signatures
import RilAccess.Solver

open Lean

structure JsonRule where
  premises : List Nat
  conclusion : Nat
  deriving FromJson

structure JsonCoordinate where
  kind : String
  key : String
  deriving FromJson, DecidableEq

structure JsonSource where
  formal : Nat
  source_path : List JsonCoordinate
  result_path : List JsonCoordinate
  access : Nat
  deriving FromJson, DecidableEq

def JsonSource.parameter (formal : Nat) : JsonSource := ⟨formal, [], [], 0⟩

structure JsonInvocation where
  receiver : Nat
  parameter : Nat
  input : Option String
  formal : Option Nat
  preserves_input : Bool
  deriving FromJson

def JsonInvocation.contract (call : JsonInvocation) : RilAccess.CallbackInvocation :=
  ⟨call.receiver, call.parameter,
    call.formal.elim (.input (call.input.getD "")) .formal, call.preserves_input⟩

structure JsonStorageUpdate where
  formal : Nat
  path : List JsonCoordinate
  sources : List JsonSource
  callback_returns : List Json
  definite : Bool
  constructs : Bool
  deriving FromJson

def JsonStorageUpdate.contract (update : JsonStorageUpdate) :
    RilAccess.StorageUpdate (Nat × List JsonCoordinate) JsonSource :=
  ⟨(update.formal, update.path), update.sources, update.callback_returns.map Json.compress,
    update.definite, update.constructs⟩

structure JsonEffectUse where
  effect : String
  operation : Option String
  deriving FromJson, DecidableEq

structure JsonSummary where
  writes : List Nat
  retained : List Nat
  independent_retention : List Nat
  return_sources : List JsonSource
  effects : List Nat
  effect_uses : List JsonEffectUse
  invocations : List JsonInvocation
  invoked : List Nat
  callback_returns : List Json
  storage_updates : List JsonStorageUpdate
  captures : Bool
  constructs : Bool
  nonreturning : Bool
  deriving FromJson

def JsonSummary.formal (summary : JsonSummary) : RilAccess.SummaryOf JsonSource :=
  { rootReturn := summary.return_sources.filter (·.result_path.isEmpty)
    contained := summary.return_sources.filter (!·.result_path.isEmpty)
    writes := summary.writes.map JsonSource.parameter
    retained := summary.retained.map JsonSource.parameter
    createdEnvironments := if summary.captures then [JsonSource.parameter 0] else []
    effects := summary.effects }

structure JsonComparison where
  baseline : JsonSummary
  revision : JsonSummary
  deriving FromJson

def compareSummaries (baseline revision : JsonSummary) : Bool :=
  RilAccess.SummaryOf.subsumesBy (fun _ => false) baseline.formal revision.formal &&
    revision.independent_retention.all baseline.independent_retention.contains &&
    revision.effect_uses.all (fun effect => baseline.effect_uses.any fun old =>
      old.effect == effect.effect && (old.operation.isNone || old.operation == effect.operation)) &&
    RilAccess.callbackInvocationsSubsumed (baseline.invocations.map JsonInvocation.contract)
      (revision.invocations.map JsonInvocation.contract) &&
    revision.invoked.all baseline.invoked.contains &&
    RilAccess.callbackReturnsSubsumed (baseline.callback_returns.map Json.compress)
      (revision.callback_returns.map Json.compress) &&
    RilAccess.storageUpdatesSubsumed (baseline.storage_updates.map JsonStorageUpdate.contract)
      (revision.storage_updates.map JsonStorageUpdate.contract) &&
    (!baseline.constructs || revision.constructs) &&
    (!baseline.nonreturning || revision.nonreturning)

structure JsonInstance where
  modes : List String
  summary : JsonSummary
  deriving FromJson

structure JsonDomainComparison where
  baseline : List JsonInstance
  revision : List JsonInstance
  deriving FromJson

def compareDomains (case : JsonDomainComparison) : Bool :=
  let domain := fun (rows : List JsonInstance) => rows.map fun row => (row.modes, row.summary)
  RilAccess.viaDomainSubsumes compareSummaries (domain case.baseline) (domain case.revision)

def solve (entries : List JsonRule) : List Nat :=
  let rules : List (RilAccess.Rule Nat) :=
    entries.map fun rule => ⟨rule.premises, rule.conclusion⟩
  (RilAccess.solve rules).mergeSort

def decodeAccess : Nat → Option RilAccess.Access
  | 0 => some .immutable
  | 1 => some .ref
  | 2 => some .mut
  | 3 => some .shared
  | _ => none

def encodeAccess : RilAccess.Access → Nat
  | .immutable => 0
  | .ref => 1
  | .mut => 2
  | .shared => 3

def checkPath (path : List Nat) : Option Nat := do
  let root :: members ← path.mapM decodeAccess | none
  return encodeAccess (RilAccess.pathAccess root members)

open RilAccess.CoreSummary RilAccess.CoreSummary.Examples in
def callEntryCases : List (String × Bool) :=
  [("replaced_member_is_not_from_old_formal_entry", (check actual entries forged).isOk),
   ("replaced_member_is_in_new_call_entry", (checkAtEntry actual laterHeap arguments forged).isOk),
   ("replaced_member_participates_in_call_overlap",
     RilAccess.CoreEntry.separated laterHeap [saved] [inserted]),
   ("call_entry_graph_includes_later_argument_preparation",
     decide (inserted ∈ capturedInstances laterHeap [saved]))]

open RilAccess.GraphAuthority RilAccess.GraphAuthority.Examples in
def graphCases : List (String × Bool) :=
  [("a_cyclic_graph_can_be_cloned_compared_and_inspected",
     decide (Fact.mk 0 1 .mut ∈ analyze cycle) &&
     decide (resolvePath cycle.edges 0 .mut [0, 0] = some (0, .mut))),
   ("cloning_preserves_repeated_paths_to_one_object",
     decide (resolvePath repeated.edges 0 .mut [0] = resolvePath repeated.edges 0 .mut [1])),
   ("a_readonly_member_cannot_use_its_sibling_writer", canWritePath readonlySibling 0 [0]),
   ("a_writable_member_can_coexist_with_its_readonly_alias", canWritePath readonlySibling 0 [1]),
   ("nested_shared_replacement_keeps_writable_outer_layers",
     (nestedSharedStored.map fun graph =>
       canWritePath graph 0 [0, 0] && canWritePath graph 0 [0, 0, 0] &&
       canWritePath graph 0 [0, 0, 1]).getD false),
   ("a_nested_ref_is_readonly_under_writable_layers", canWritePath nestedSources 0 [0, 0, 2]),
   ("a_nested_snapshot_is_readonly_under_writable_layers", canWritePath nestedSources 0 [0, 0, 3]),
   ("a_new_wrapper_cannot_freeze_an_existing_writer", immutableConsistent frozenNestedSources),
   ("a_snapshot_can_freeze_a_completely_new_graph",
     immutableConsistent frozenRoot && !hasWriter frozenRoot 1),
   ("a_member_reached_through_a_ref_cannot_be_received_as_mutable",
     canWritePath { repeated with roots := [⟨0, 0, .ref⟩] } 0 [0]),
   ("replacing_a_ref_member_keeps_it_readonly",
     (checkedRef.map fun graph => canWritePath graph 0 [0]).getD false),
   ("a_mutable_path_cannot_implicitly_fill_a_ref_member", (receiveStored .ref .mut false).isSome),
   ("a_shared_marker_requires_a_shared_binding", (receiveStored .ref .mut true).isSome),
   ("a_fixed_shared_member_cannot_be_replaced", (checkedReplace fixedSlot 0 [] 0 1 [] true).isSome),
   ("replacing_a_shared_member_requires_acknowledgment", (checkedReplace sharedSlot 0 [] 0 1 [] false).isSome),
   ("publication_survives_in_a_caller_member", checkedShared.isSome),
   ("replaced_member_is_not_from_old_formal_entry", decide (2 ∈ entryObjects mutableSlot 0)),
   ("replaced_member_is_in_new_call_entry", (checkedShared.map fun graph =>
      decide (2 ∈ entryObjects graph 0)).getD false)]

open RilAccess.Provenance RilAccess.Provenance.Examples in
def cleanupCompositionCases : List (String × Bool) :=
  [("panic_runs_both_cleanups_through_their_installed_handler", (check (cleanupProgram true)).isOk),
   ("synchronous_cleanup_may_diverge", (check divergingCleanupProgram).isOk),
   ("a_cleanup_handler_write_requires_a_caller_state_clause", (check (cleanupProgram false)).isOk)]

open RilAccess.Calls.Examples in
def callAuthorityCases : List (String × Bool) :=
  [("a_ref_argument_can_observe_a_replaceable_binding", accepted observeVariable),
   ("two_ref_arguments_can_observe_the_same_source", accepted readAliased),
   ("two_mutable_arguments_can_use_disjoint_sources", accepted disjointWriters),
   ("overlapping_mut_writers", accepted aliasedWriters),
   ("overlapping_read_write", accepted writeReadAlias),
   ("mutable_formal_cannot_supply_a_retained_writer", accepted ordinaryWriteCannotRetain),
   ("shared_return_retains", accepted retainedWriter),
   ("shared_parameter_not_retained", accepted writeAloneNotRetention),
   ("retaining_a_local_alias_keeps_its_formal_authority", accepted retainedThroughAlias),
   ("nested_mutable_call_proves_the_outer_use", accepted nestedMutation),
   ("nested_shared_call_preserves_retained_authority", accepted nestedRetention),
   ("recursive_forwarding_is_ungrounded", accepted noCircularUse),
   ("reachable_write_on_one_alternative_satisfies_mutable_use", accepted possibleWrite),
   ("call_markers_must_match_a_mutable_formal", accepted wrongMarker),
   ("mutable_formal_is_a_fixed_slot", accepted rebindFormal),
   ("a_new_argument_can_supply_construction_authority", accepted constructInput),
   ("a_read_only_argument_cannot_supply_construction_authority", accepted observedInputIsNotConstruction),
   ("a_plain_argument_requires_a_snapshot", accepted mutablePlainInput),
   ("a_named_helper_must_declare_its_capture", accepted undeclaredCapture),
   ("independent_capture_and_mutable_argument_can_be_used_together", accepted declaredCapture),
   ("named_callable_capture_overlaps_a_mutable_argument", accepted independentCapture),
   ("retaining_one_shared_formal_does_not_retain_its_sibling", accepted formalAliasIsNotRetention),
   ("overwritten_outer_binding_does_not_retain_a_parameter", accepted overwrittenPublication),
   ("publication_survives_in_a_replaced_outer_binding", accepted survivingPublication),
   ("local_sharing_does_not_retain_a_parameter", accepted callLocalSharingNotRetention)]

open RilAccess.CoreConcurrency RilAccess.CoreConcurrency.Examples in
def taskJoinCases : List (String × Bool) :=
  let fallible : ScopeState :=
    ⟨7, [{ id := 1, regionSigma := 7, mode := .sharedImmutable, fallibleResult := true }]⟩
  let twoJoins := (joinTask fallible 1 7 false).bind (joinTask · 1 7 false)
  [("plain_task_join_is_memoized_and_rooted",
    ((joinTask taskScope 1 7 false).bind (joinTask · 1 7 false)).isSome),
   ("owned_task_join_preserves_fresh_payload", (joinTask taskScope 2 7 true).isSome),
   ("owned_join_ends_the_task_path", (joinTask afterExclusiveJoin 2 7 true).isSome),
   ("every_memoized_fallible_join_requires_inspection",
    ((twoJoins.bind (inspectJoinedResult · 1 7)).bind drainPlainTasks).isSome)]

open RilAccess.CoreBoundary RilAccess.CoreBoundary.Examples in
def boundaryCases : List (String × Bool) :=
  [("confined_new_container_writes_discharge", (outward privateBoundary 7 9).isEmpty),
   ("handler_contains_effect", (handled privateBoundary 3).effects.isEmpty),
   ("installed_handler_does_not_cover_its_own_arm", (handled handlerEffect 3).effects.isEmpty),
   ("outer_handler_covers_inner_arm", (handled outerHandler 3).effects.isEmpty),
   ("cleanup_uses_evidence_at_resource_binding", (handled cleanupEffect 3).effects.isEmpty),
   ("stateful_handler_cannot_cross_fiber_boundary",
     concurrentShareableFnHandler pureSources [10] { pureFnHandler with writes := [external] } [])]

open RilAccess.Draft RilAccess.Draft.Examples in
def draftCases : List (String × Bool) :=
  let original := { input with pool := input.pool.map fun cell =>
    if cell.srcInst.object == 1 then { cell with contents := [.reference 0] } else cell }
  let update := [grow, mutateInserted, done]
  [("draft_updates_only_the_selected_occurrence",
     contents update 1 original == some [.reference 0] &&
     (publishedContents update [0] original).any (fun values => values.length == 3) &&
     publishedContents update [1] original == some [.reference 0] &&
     publishedContents update [0, 1] original == some [.scalar 0 8] &&
     publishedContents update [0, 2] original == some [.scalar 0 7] &&
     contents update 3 original == some [.scalar 0 7]),
   ("draft_inserts_map_entry_without_changing_base",
     contents mapInsert 7 mapInput == some [.reference 6] &&
     publishedContents mapInsert [] mapInput == some [.reference 6, .reference 11] &&
     publishedContents mapInsert [1] mapInput == some [.scalar 0 2, .scalar 0 20])]

open RilAccess.Integrated RilAccess.Integrated.HandoffExamples in
def handoffCases : List (String × Bool) :=
  [("explicit_handoff_keeps_unrelated_path",
     (checkAtom (.handoff 0 2) before).isOk && currentLive after 2 && currentLive after 4),
   ("handoff_ends_binding", currentLive after 0),
   ("handoff_ends_dependent_view", currentLive after 1),
   ("handoff_cannot_repeat", (checkAtom (.handoff 0 3) after).isOk)] ++
   callbackChecks.map (fun (name, accepted, _) => (name, accepted))

open RilAccess.Provenance RilAccess.Provenance.Examples in
def provenanceCases : List (String × Bool) :=
  [("replacing_a_reference_slot_removes_its_old_origin",
    decide (beforeWrites overwrite 2 0 = [⟨20, none⟩])),
   ("helper_capture_before_initialization", accepts future),
   ("dead_branch_is_not_write_authority", accepts (recursiveWriter false)),
   ("loops_and_recursion_with_no_exit_typecheck_as_never",
    accepts divergentLoop && accepts divergentRecursion),
   ("while_backedge_can_make_arguments_overlap", accepts (loopAlias true false)),
   ("for_continue_carries_aliases_to_the_next_iteration", accepts (loopAlias true false)),
   ("a_single_iteration_for_does_not_revisit_the_body", accepts (loopAlias false false)),
   ("loop_aliases_can_take_multiple_iterations_to_reach_the_call", accepts (loopAlias true true)),
   ("recursive_forwarding_is_ungrounded", accepts (recursiveWriter false)),
   ("mutual_recursion_has_grounded_writer", accepts (recursiveWriter true)),
   ("exact_fields_are_separate_mutable_arguments", accepts (fields false)),
   ("exclusive_arguments_remain_disjoint_when_branches_swap_them", accepts permutedFields),
   ("unknown_index_cannot_prove_separation", accepts (fields true)),
   ("cyclic_arguments_share_a_reachable_descendant", accepts cycle),
   ("replaced_member_is_in_new_call_entry", accepts (entryReturn false)),
   ("replaced_member_is_not_from_old_formal_entry", accepts (entryReturn true)),
   ("handing_off_a_wrapper_keeps_its_independent_ref_source", accepts (wrapOld (.read 0))),
   ("handing_off_a_wrapper_ends_views_of_its_members", accepts (wrapOld (.read 2))),
   ("a_nested_ref_is_readonly_under_writable_layers", accepts upgradeOld),
   ("a_new_wrapper_cannot_freeze_an_existing_ref", accepts freezeOldView),
   ("a_snapshot_can_freeze_a_completely_new_graph", accepts (completeNewGraph .immutable)),
   ("new_reception_can_select_mutable_element_mode", accepts (completeNewGraph .mut)),
   ("new_argument_ends_path_before_later_arguments", accepts endedArgument),
   ("publication_survives_in_a_caller_member", accepts (retention false)),
   ("overwriting_a_publication_ends_retention", accepts (retention true)),
   ("forwarded_call_scoped_ref_cannot_be_published", accepts temporaryForward),
   ("aborting_write_still_requires_write_clause", accepts (abortingWriter false)),
   ("aborting_writer_declares_the_write", accepts (abortingWriter true)),
   ("new_container_does_not_discharge_existing_member_writes", accepts (writeThroughWrapper false)),
   ("new_container_writes_existing_member", accepts (writeThroughWrapper true)),
   ("factory_writes_to_a_later_instance_are_local", accepts (localFactoryWrite false)),
   ("factory_writes_to_a_later_instance_cannot_justify_state", accepts (localFactoryWrite true))]

open RilAccess.Integrated RilAccess.Examples.ScopedExamples in
def scopedCases : List (String × Bool) :=
  [("foreign_handle_permits_mutable_call_and_chained_handoff",
    accepted resourceCallAccessAndHandoff && accepted resourceChainedHandoff),
   ("foreign_handle_plain_binding_cannot_freeze", accepted resourcePlainSnapshotRejected),
   ("scoped_resource_can_be_observed_and_mutated_by_helpers", accepted scopedCallRefAndMutAccess),
   ("scoped_resource_plain_use_can_be_unused", accepted scopedReadOnlyUnusedOk),
   ("scoped_resource_read_only_view_cannot_write", accepted scopedReadOnlyRejectsWrite),
   ("scoped_resource_mutable_reception_needs_body_write", accepted scopedIdleMutRejected),
   ("scoped_resource_cannot_be_aliased_by_let", accepted scopedRebindEscapeRejected),
   ("scoped_resource_cannot_be_captured_by_closure", accepted scopedClosureCaptureRejected),
   ("scoped_resource_cannot_be_consumed_before_cleanup", accepted scopedCallNewHandoffRejected)] ++
  refScopeCases.map fun (name, anchors, slot, _) => (name, refSourcesEnclose anchors slot)

open RilAccess.VisibilityModel RilAccess.Examples.VisibilityExamples in
def visibilityCases : List (String × Bool) :=
  [("package_private", visibleFrom .pubPkg .externalPkg),
   ("package_item_visible_to_other_module_in_package", visibleFrom .pubPkg .samePkg),
   ("private_selection", visibleFrom .priv .samePkg),
   ("visibility_leak", signatureWellFormed publicRoot [⟨true, [], .priv⟩]),
   ("public_cleanup_cannot_expose_package_item", signatureWellFormed publicRoot [packageRoot]),
   ("opaque_converts_inside_scope", representationTransparent .priv .opaqueScope .sameScope),
   ("opaque_member_outside_scope", representationTransparent .pubExport .opaqueScope .samePkg),
   ("no_top_level_var", validTopLevelBinding .mutableOrLiveState),
   ("extensible_sum_closes_inside_package", exhaustiveMatch rilExtIoError .samePkg [0, 1] false),
   ("extensible_sum_redundant_wildcard_inside_package", exhaustiveMatch rilExtIoError .samePkg [0, 1] true),
   ("extensible_sum_needs_wildcard_across_packages", exhaustiveMatch rilExtIoError .externalPkg [0, 1] false),
   ("extensible_sum_wildcard_covers_other_packages", exhaustiveMatch foreignErrno .externalPkg [1, 2, 3] true)]

def main (args : List String) : IO Unit := do
  let stdin ← IO.getStdin
  let source ← stdin.readToEnd
  let stdout ← IO.getStdout
  let .ok json := Json.parse source
    | throw (IO.userError "expected JSON oracle input")
  if args == ["summary"] then
    let .ok cases := fromJson? (α := List JsonComparison) json
      | throw (IO.userError "expected a JSON array of callable summaries")
    stdout.putStrLn (toJson (cases.map fun case => compareSummaries case.baseline case.revision)).compress
  else if args == ["domain"] then
    let .ok cases := fromJson? (α := List JsonDomainComparison) json
      | throw (IO.userError "expected a JSON array of via domain comparisons")
    stdout.putStrLn (toJson (cases.map compareDomains)).compress
  else if args == ["batch"] then
    let .ok cases := fromJson? (α := List (List JsonRule)) json
      | throw (IO.userError "expected a JSON array of Horn programs")
    stdout.putStrLn (toJson (cases.map solve)).compress
  else if args == ["path-access"] then
    let .ok paths := fromJson? (α := List (List Nat)) json
      | throw (IO.userError "expected a JSON array of access paths")
    let some answers := paths.mapM checkPath
      | throw (IO.userError "access paths require a root and mode numbers 0 to 3")
    stdout.putStrLn (toJson answers).compress
  else if args == ["call-entry"] then
    stdout.putStrLn (toJson callEntryCases).compress
  else if args == ["graph"] then
    stdout.putStrLn (toJson graphCases).compress
  else if args == ["cleanup-composition"] then
    stdout.putStrLn (toJson cleanupCompositionCases).compress
  else if args == ["summary-reuse"] then
    stdout.putStrLn (toJson (RilAccess.Provenance.Examples.summaryReuse false)).compress
  else if args == ["recursive-storage"] then
    stdout.putStrLn (toJson RilAccess.RecursiveStorage.Examples.contracts).compress
  else if args == ["call-authority"] then
    stdout.putStrLn (toJson callAuthorityCases).compress
  else if args == ["task-joins"] then
    stdout.putStrLn (toJson taskJoinCases).compress
  else if args == ["boundary"] then
    stdout.putStrLn (toJson boundaryCases).compress
  else if args == ["draft"] then
    stdout.putStrLn (toJson draftCases).compress
  else if args == ["handoff"] then
    stdout.putStrLn (toJson handoffCases).compress
  else if args == ["provenance"] then
    stdout.putStrLn (toJson provenanceCases).compress
  else if args == ["scoped"] then
    stdout.putStrLn (toJson scopedCases).compress
  else if args == ["visibility"] then
    stdout.putStrLn (toJson visibilityCases).compress
  else
    let .ok entries := fromJson? (α := List JsonRule) json
      | throw (IO.userError "expected a JSON array of Horn rules")
    stdout.putStrLn (toJson (solve entries)).compress
