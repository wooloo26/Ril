import Lean
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

structure JsonSummary where
  writes : List Nat
  retained : List Nat
  return_sources : List JsonSource
  effects : List Nat
  captures : Bool
  constructs : Bool
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

def compare (case : JsonComparison) : Bool :=
  RilAccess.SummaryOf.subsumesBy (fun _ => false) case.baseline.formal case.revision.formal &&
    (!case.baseline.constructs || case.revision.constructs)

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
    stdout.putStrLn (toJson (cases.map compare)).compress
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
  else if args == ["task-joins"] then
    stdout.putStrLn (toJson taskJoinCases).compress
  else if args == ["visibility"] then
    stdout.putStrLn (toJson visibilityCases).compress
  else
    let .ok entries := fromJson? (α := List JsonRule) json
      | throw (IO.userError "expected a JSON array of Horn rules")
    stdout.putStrLn (toJson (solve entries)).compress
