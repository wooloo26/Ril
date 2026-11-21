import Lean
import RilAccess.Signatures
import RilAccess.Solver

open Lean

structure JsonRule where
  premises : List Nat
  conclusion : Nat
  deriving FromJson

structure JsonSummary where
  writes : List Nat
  retained : List Nat
  roots : List Nat
  contained : List (Nat × Nat)
  effects : List Nat
  captures : Bool
  constructs : Bool
  deriving FromJson

def JsonSummary.formal (summary : JsonSummary) : RilAccess.SummaryOf (Nat × Nat) :=
  { rootReturn := summary.roots.map (0, ·)
    contained := summary.contained
    writes := summary.writes.map (0, ·)
    retained := summary.retained.map (0, ·)
    createdEnvironments := if summary.captures then [(0, 0)] else []
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
  else
    let .ok entries := fromJson? (α := List JsonRule) json
      | throw (IO.userError "expected a JSON array of Horn rules")
    stdout.putStrLn (toJson (solve entries)).compress
