import RilAccess
import RilAccess.Examples.All

def main : IO UInt32 := do
  let examples := RilAccess.Examples.allExamples
  let mut failed := 0
  for (name, passed) in examples do
    IO.println s!"{if passed then "PASS" else "FAIL"} {name}"
    unless passed do failed := failed + 1
  IO.println s!"{examples.length - failed}/{examples.length} core examples passed."
  return if failed = 0 then 0 else 1
