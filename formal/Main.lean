import RilAccess
import RilAccess.Examples.All

def main : IO UInt32 := do
  let fixtures := RilAccess.Examples.allFixtures
  let mut failed := 0
  for (name, passed) in fixtures do
    IO.println s!"{if passed then "PASS" else "FAIL"} {name}"
    unless passed do failed := failed + 1
  IO.println s!"{fixtures.length - failed}/{fixtures.length} core fixtures passed."
  return if failed = 0 then 0 else 1
