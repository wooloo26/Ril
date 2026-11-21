import Lean
import RilAccess.Solver

open Lean

structure JsonRule where
  premises : List Nat
  conclusion : Nat
  deriving FromJson

def main : IO Unit := do
  let stdin ← IO.getStdin
  let source ← stdin.readToEnd
  let parse : Except String (List JsonRule) := do
    let data ← Json.parse source
    fromJson? data
  let .ok entries := parse
    | throw (IO.userError "expected a JSON array of Horn rules")
  let rules : List (RilAccess.Rule Nat) :=
    entries.map fun rule => ⟨rule.premises, rule.conclusion⟩
  let facts := (RilAccess.solve rules).mergeSort
  let stdout ← IO.getStdout
  stdout.putStrLn (toJson facts).compress
