import Lean
import RilAccess.Examples.Summary
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
  else
    let .ok entries := fromJson? (α := List JsonRule) json
      | throw (IO.userError "expected a JSON array of Horn rules")
    stdout.putStrLn (toJson (solve entries)).compress
