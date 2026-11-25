import Lean
import RilAccess.Examples.Access
import RilAccess.Examples.Boundary
import RilAccess.Examples.Call
import RilAccess.Examples.Composition
import RilAccess.Examples.Draft
import RilAccess.Examples.Graph
import RilAccess.Examples.Handoff
import RilAccess.Examples.RecursiveStorage
import RilAccess.Examples.ResolvedProvenance
import RilAccess.Examples.Results
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

structure JsonModeAxis where
  parameter : Nat
  path : List Json
  deriving FromJson

structure JsonModeCall where
  receiver : JsonModeAxis
  arguments : List (JsonModeAxis × Json)
  recursive_path : Option (List Json)
  deriving FromJson

def JsonModeCall.contract (call : JsonModeCall) :
    RilAccess.CallbackModeCall (Nat × List String) String :=
  ⟨(call.receiver.parameter, call.receiver.path.map Json.compress),
   (call.arguments.map fun (axis, mode) =>
    ((axis.parameter, axis.path.map Json.compress),
     match mode with
     | .str "Unknown" => none
     | other => some other.compress)),
   call.recursive_path.map (·.map Json.compress)⟩

def legacyModeCalls (invocations : List JsonInvocation) : List JsonModeCall :=
  (invocations.map (·.receiver)).eraseDups.flatMap fun receiver =>
    let calls := invocations.filter (·.receiver == receiver)
    let parameters := (calls.map (·.parameter)).eraseDups.mergeSort (· ≤ ·)
    let offers := parameters.map fun parameter =>
      (calls.filter (·.parameter == parameter)).map fun call =>
        let mode := match call.formal with
          | some formal => Json.mkObj [("Axis", Json.mkObj [
              ("parameter", toJson formal), ("path", .arr #[])])]
          | none => Json.mkObj [("Input", toJson (call.input.getD ""))]
        (⟨parameter, []⟩, mode)
    let combinations := offers.foldr
      (fun modes suffixes => modes.flatMap fun mode => suffixes.map (mode :: ·)) [[]]
    combinations.map fun arguments => ⟨⟨receiver, []⟩, arguments, none⟩

structure JsonSnapshotOrigin where
  shape : Json
  provider : Option Nat
  deriving FromJson

structure JsonSnapshotProjection where
  shape : Json
  origin : JsonSnapshotOrigin
  live_callable_state : Option Bool
  deriving FromJson

structure JsonCallbackReturn where
  shape : Json
  projections : List (List JsonSnapshotProjection)
  deriving FromJson

structure JsonStorageUpdate where
  formal : Nat
  path : List JsonCoordinate
  sources : List JsonSource
  callback_returns : List JsonCallbackReturn
  snapshot_projections : List JsonSnapshotProjection
  allocations : List Json
  definite : Bool
  constructs : Bool
  deriving FromJson

def JsonStorageUpdate.contract (update : JsonStorageUpdate) :
    RilAccess.StorageUpdate (Nat × List JsonCoordinate) JsonSource :=
  ⟨(update.formal, update.path), update.sources, update.callback_returns.map (·.shape.compress),
    update.allocations.map Json.compress, update.definite, update.constructs⟩

structure JsonStorageOperand where
  shape : Json
  projections : List JsonSnapshotProjection
  callback_returns : List JsonCallbackReturn
  deriving FromJson

structure JsonStorageInvocation where
  receiver : JsonStorageOperand
  arguments : List JsonStorageOperand
  deriving FromJson

structure JsonStorageRead where
  shape : Json
  base : JsonStorageOperand
  deriving FromJson

structure JsonStorageObservedWrite where
  shape : Json
  value : JsonStorageOperand
  definite : Bool
  deriving FromJson

structure JsonStorageDerivation where
  index : Nat
  base : JsonStorageOperand
  updater : JsonStorageOperand
  deriving FromJson

structure JsonStorageStep where
  write : Option JsonStorageUpdate
  invoke : Option JsonStorageInvocation
  read : Option JsonStorageRead
  write_observed : Option JsonStorageObservedWrite
  derivation : Option JsonStorageDerivation
  deriving FromJson

structure JsonStorageFlow where
  interleaved : Bool
  paths : List (List JsonStorageStep)
  deriving FromJson

structure JsonEffectUse where
  effect : String
  operation : Option String
  deriving FromJson, DecidableEq

structure JsonSnapshotInput where
  formal : Nat
  path : List JsonCoordinate
  replaced : List (List JsonCoordinate)
  deriving FromJson

def JsonSnapshotInput.contract (input : JsonSnapshotInput) :
    RilAccess.SnapshotInput JsonCoordinate :=
  ⟨input.formal, input.path, input.replaced⟩

structure JsonSnapshotNode where
  shape : Json
  roots : List JsonSnapshotOrigin
  deriving FromJson

structure JsonSnapshotArgument where
  shape : Json
  graph : List JsonSnapshotNode
  deriving FromJson

structure JsonSnapshotFactoryStep where
  shape : Json
  arguments : List JsonSnapshotArgument
  deriving FromJson

structure JsonSnapshotCall where
  shape : Json
  arguments : List JsonSnapshotArgument
  factory_steps : List JsonSnapshotFactoryStep
  deriving FromJson

structure JsonSnapshotProvider where
  via_parameters : List Bool
  inputs : List JsonSnapshotInput
  calls : List JsonSnapshotCall
  captured_slots : List Bool
  storage_updates : List JsonStorageUpdate
  storage_flow : Option JsonStorageFlow
  returns : List JsonSnapshotProjection
  callback_returns : List JsonCallbackReturn
  returns_new : Bool
  deriving FromJson

abbrev ProviderPairs := List (Nat × Nat)

def snapshotOriginsSubsumed (pairs : ProviderPairs) (old new : List JsonSnapshotOrigin) : Bool :=
  new.all fun required => old.any fun offered => offered.shape.compress == required.shape.compress &&
    match offered.provider, required.provider with
    | none, none => true
    | some i, some j => pairs.contains (i, j)
    | _, _ => false

def snapshotProjectionsSubsumed (pairs : ProviderPairs) (old new : List JsonSnapshotProjection) : Bool :=
  new.all fun required => old.any fun offered =>
    offered.shape.compress == required.shape.compress &&
      (offered.live_callable_state.getD false || !required.live_callable_state.getD false) &&
      snapshotOriginsSubsumed pairs [offered.origin] [required.origin]

def snapshotCallbackReturnsSubsumed (pairs : ProviderPairs) (old new : List JsonCallbackReturn) : Bool :=
  new.all fun required => old.any fun offered =>
    offered.shape.compress == required.shape.compress &&
    offered.projections.length == required.projections.length &&
    (offered.projections.zip required.projections).all fun (left, right) =>
      snapshotProjectionsSubsumed pairs left right

def snapshotStorageUpdatesSubsumed (pairs : ProviderPairs) (old new : List JsonStorageUpdate) : Bool :=
  RilAccess.storageUpdatesSubsumed (old.map JsonStorageUpdate.contract)
    (new.map JsonStorageUpdate.contract) &&
  new.all fun update => old.any fun allowed =>
    allowed.contract.permits update.contract &&
      snapshotCallbackReturnsSubsumed pairs allowed.callback_returns update.callback_returns &&
      snapshotProjectionsSubsumed pairs allowed.snapshot_projections update.snapshot_projections

def storageOperandSubsumed (pairs : ProviderPairs) (old new : JsonStorageOperand) : Bool :=
  old.shape.compress == new.shape.compress &&
    snapshotProjectionsSubsumed pairs old.projections new.projections &&
    old.callback_returns.length == new.callback_returns.length &&
    (old.callback_returns.zip new.callback_returns).all fun (left, right) =>
      snapshotCallbackReturnsSubsumed pairs [left] [right]

def storageStepSubsumed (pairs : ProviderPairs) (old new : JsonStorageStep) : Bool :=
  match old.write, new.write, old.invoke, new.invoke, old.read, new.read with
  | some left, some right, _, _, _, _ => snapshotStorageUpdatesSubsumed pairs [left] [right]
  | none, none, some left, some right, _, _ =>
      storageOperandSubsumed pairs left.receiver right.receiver &&
      left.arguments.length == right.arguments.length &&
      (left.arguments.zip right.arguments).all fun (left, right) => storageOperandSubsumed pairs left right
  | none, none, none, none, some left, some right =>
      left.shape.compress == right.shape.compress && storageOperandSubsumed pairs left.base right.base
  | none, none, none, none, none, none =>
      match old.write_observed, new.write_observed, old.derivation, new.derivation with
      | some left, some right, _, _ => left.shape.compress == right.shape.compress &&
          (!left.definite || right.definite) && storageOperandSubsumed pairs left.value right.value
      | none, none, some left, some right => left.index == right.index &&
          storageOperandSubsumed pairs left.base right.base &&
          storageOperandSubsumed pairs left.updater right.updater
      | _, _, _, _ => false
  | _, _, _, _, _, _ => false

def storageFlowsSubsumed (pairs : ProviderPairs) (old new : Option JsonStorageFlow) : Bool :=
  match old, new with
  | none, none => true
  | some left, some right =>
      if left.interleaved then
        right.paths.flatten.all fun required => left.paths.flatten.any fun allowed =>
          storageStepSubsumed pairs allowed required
      else
        !right.interleaved && right.paths.all fun path => left.paths.any fun allowed =>
          allowed.length == path.length && (allowed.zip path).all fun (left, right) =>
            storageStepSubsumed pairs left right
  | _, _ => false

def snapshotArgsSubsumed (pairs : ProviderPairs) (old new : List JsonSnapshotArgument) : Bool :=
  old.length == new.length && (old.zip new).all fun (offered, required) =>
    offered.shape.compress == required.shape.compress && offered.graph.length == required.graph.length &&
    (offered.graph.zip required.graph).all fun (left, right) =>
      left.shape.compress == right.shape.compress && snapshotOriginsSubsumed pairs left.roots right.roots

def snapshotCallsSubsumed (pairs : ProviderPairs) (old new : List JsonSnapshotCall) : Bool :=
  new.all fun required => old.any fun offered =>
    offered.shape.compress == required.shape.compress &&
      snapshotArgsSubsumed pairs offered.arguments required.arguments &&
      offered.factory_steps.length == required.factory_steps.length &&
      (offered.factory_steps.zip required.factory_steps).all fun (left, right) =>
        left.shape.compress == right.shape.compress && snapshotArgsSubsumed pairs left.arguments right.arguments

def pruneSnapshotProviders (old new : Array JsonSnapshotProvider) : Nat → ProviderPairs → ProviderPairs
  | 0, pairs => pairs
  | fuel + 1, pairs =>
    let next := pairs.filter fun (i, j) =>
      match old[i]?, new[j]? with
      | some left, some right => snapshotCallsSubsumed pairs left.calls right.calls &&
          (!left.returns_new || right.returns_new) &&
          ((right.storage_updates.isEmpty && right.storage_flow.isNone) || left.captured_slots == right.captured_slots) &&
          snapshotStorageUpdatesSubsumed pairs left.storage_updates right.storage_updates &&
          storageFlowsSubsumed pairs left.storage_flow right.storage_flow &&
          snapshotProjectionsSubsumed pairs left.returns right.returns &&
          snapshotCallbackReturnsSubsumed pairs left.callback_returns right.callback_returns
      | _, _ => false
    if next.length == pairs.length then pairs else pruneSnapshotProviders old new fuel next

def compareSnapshotProviders (old new : List JsonSnapshotProvider) : ProviderPairs :=
  let seed := old.zipIdx.flatMap fun (left, i) => new.zipIdx.filterMap fun (right, j) =>
    if left.via_parameters == right.via_parameters &&
       RilAccess.snapshotInputsSubsumed (left.inputs.map JsonSnapshotInput.contract)
         (right.inputs.map JsonSnapshotInput.contract)
    then some (i, j) else none
  pruneSnapshotProviders old.toArray new.toArray seed.length seed

structure JsonSummary where
  writes : List Nat
  retained : List Nat
  independent_retention : List Nat
  snapshot_inputs : List JsonSnapshotInput
  snapshot_calls : List JsonSnapshotCall
  snapshot_providers : List JsonSnapshotProvider
  snapshot_returns : List JsonSnapshotProjection
  return_sources : List JsonSource
  return_allocations : List Json
  effects : List Nat
  effect_uses : List JsonEffectUse
  invocations : List JsonInvocation
  mode_calls : Option (List JsonModeCall)
  invoked : List Nat
  callback_returns : List JsonCallbackReturn
  storage_updates : List JsonStorageUpdate
  storage_flow : Option JsonStorageFlow
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
  let providers := compareSnapshotProviders baseline.snapshot_providers revision.snapshot_providers
  RilAccess.SummaryOf.subsumesBy (fun _ => false) baseline.formal revision.formal &&
    decide (baseline.return_allocations.map Json.compress = revision.return_allocations.map Json.compress) &&
    revision.independent_retention.all baseline.independent_retention.contains &&
    RilAccess.snapshotInputsSubsumed (baseline.snapshot_inputs.map JsonSnapshotInput.contract)
      (revision.snapshot_inputs.map JsonSnapshotInput.contract) &&
    snapshotCallsSubsumed providers baseline.snapshot_calls revision.snapshot_calls &&
    snapshotProjectionsSubsumed providers baseline.snapshot_returns revision.snapshot_returns &&
    revision.effect_uses.all (fun effect => baseline.effect_uses.any fun old =>
      old.effect == effect.effect && (old.operation.isNone || old.operation == effect.operation)) &&
    RilAccess.callbackInvocationsSubsumed (baseline.invocations.map JsonInvocation.contract)
      (revision.invocations.map JsonInvocation.contract) &&
    RilAccess.callbackModeCallsSubsumed
      ((baseline.mode_calls.getD (legacyModeCalls baseline.invocations)).map JsonModeCall.contract)
      ((revision.mode_calls.getD (legacyModeCalls revision.invocations)).map JsonModeCall.contract) &&
    revision.invoked.all baseline.invoked.contains &&
    snapshotCallbackReturnsSubsumed providers baseline.callback_returns revision.callback_returns &&
    snapshotStorageUpdatesSubsumed providers baseline.storage_updates revision.storage_updates &&
    storageFlowsSubsumed providers baseline.storage_flow revision.storage_flow &&
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
   ("snapshot_of_handed_off_new_parameter_checks_call_entry_sources",
     immutableConsistent handedOffBeforeStore),
   ("an_indirect_freeze_checks_retained_authority_in_the_actual_argument",
     immutableConsistent handedOffBeforeStore),
   ("passing_a_freezing_callback_accepts_a_complete_new_argument",
     immutableConsistent handedOffAfterStore),
   ("snapshot_checks_follow_callback_receivers_in_recursive_data",
     immutableConsistent handedOffBeforeStore),
   ("snapshot_checks_converge_when_recursive_calls_wrap_an_argument",
     immutableConsistent frozenNestedSources),
   ("a_call_scoped_writer_cannot_be_frozen_by_handoff", immutableConsistent immutableAndWriter),
   ("conditional_store_keeps_the_original_snapshot_requirement",
     immutableConsistent handedOffBeforeStore && immutableConsistent handedOffAfterStore),
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

open RilAccess.CoreConcurrency RilAccess.CoreConcurrency.Examples in
def taskJoinCases : List (String × Bool) :=
  [("plain_task_join_is_memoized_and_rooted",
    ((joinTask taskScope 1 7 false).bind (joinTask · 1 7 false)).isSome),
   ("new_handoff_task_join_preserves_fresh_payload", (joinTask taskScope 2 7 true).isSome),
   ("new_handoff_join_ends_the_task_path", (joinTask afterExclusiveJoin 2 7 true).isSome),
   ("every_memoized_fallible_join_requires_inspection", memoizedJoinLoop false),
   ("memoized_join_loop_cannot_discard_an_earlier_result", memoizedJoinLoop false),
   ("memoized_join_loop_can_inspect_each_result", memoizedJoinLoop true)]

open RilAccess.CoreBoundary RilAccess.CoreBoundary.Examples in
def boundaryCases : List (String × Bool) :=
  [("confined_new_container_writes_discharge", (outward privateBoundary 7 9).isEmpty),
   ("handler_contains_effect", (handled privateBoundary 3).effects.isEmpty),
   ("installed_handler_does_not_cover_its_own_arm", (handled handlerEffect 3).effects.isEmpty),
   ("outer_handler_covers_inner_arm", (handled outerHandler 3).effects.isEmpty),
   ("cleanup_uses_evidence_at_resource_binding", (handled cleanupEffect 3).effects.isEmpty),
   ("stateful_handler_cannot_cross_fiber_boundary",
     concurrentShareableFnHandler pureSources [10] { pureFnHandler with writes := [external] } [])]

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
   ("shared_chain_keeps_deep_aliases_after_the_loop", sharedLoopSeparated 0),
   ("loops_can_grow_shared_recursive_data", sharedLoopSeparated 3),
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
   ("scoped_resource_cannot_be_handed_off_before_cleanup", accepted scopedCallNewHandoffRejected)] ++
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
  else if args == ["access-ledger"] then
    stdout.putStrLn (toJson RilAccess.Integrated.Examples.sourceChecks).compress
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
    stdout.putStrLn (toJson RilAccess.Calls.Examples.sourceChecks).compress
  else if args == ["call-obligations"] then
    stdout.putStrLn (toJson RilAccess.Calls.Examples.publishedObligations).compress
  else if args == ["summary-signatures"] then
    stdout.putStrLn (toJson (RilAccess.CoreSummary.Examples.signatureCases.map
      fun (name, verdict, _) => (name, verdict))).compress
  else if args == ["task-joins"] then
    stdout.putStrLn (toJson taskJoinCases).compress
  else if args == ["result-patterns"] then
    stdout.putStrLn (toJson (RilAccess.ResultInspection.Examples.cases.map
      fun (name, accepted, _) => (name, accepted))).compress
  else if args == ["boundary"] then
    stdout.putStrLn (toJson boundaryCases).compress
  else if args == ["draft"] then
    stdout.putStrLn (toJson RilAccess.Draft.Examples.runtimeObservations).compress
  else if args == ["draft-roots"] then
    stdout.putStrLn (toJson RilAccess.Draft.Examples.sourceChecks).compress
  else if args == ["draft-via-domains"] then
    stdout.putStrLn (toJson RilAccess.Draft.Examples.viaSnapshotDomains).compress
  else if args == ["handoff"] then
    stdout.putStrLn (toJson handoffCases).compress
  else if args == ["provenance"] then
    stdout.putStrLn (toJson provenanceCases).compress
  else if args == ["callback-graph"] then
    let .ok cases := fromJson? (α := List (Nat × Nat)) json
      | throw (IO.userError "expected a JSON array of projection depths and outside objects")
    stdout.putStrLn (toJson (cases.map fun (depth, outside) =>
      RilAccess.Provenance.Examples.callbackProjectionSeparated depth outside)).compress
  else if args == ["scoped"] then
    stdout.putStrLn (toJson scopedCases).compress
  else if args == ["visibility"] then
    stdout.putStrLn (toJson visibilityCases).compress
  else
    let .ok entries := fromJson? (α := List JsonRule) json
      | throw (IO.userError "expected a JSON array of Horn rules")
    stdout.putStrLn (toJson (solve entries)).compress
