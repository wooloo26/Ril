namespace RilAccess.ResultInspection

abbrev Path := List Nat

structure Constructor where
  path : Path
  tag : String
  obligation : Option Nat := none

structure World where
  constructors : List Constructor
  pending : List Nat

structure Arm where
  tests : List (Path × String)
  guard : Bool := true

/-- A constructor test examines its own tag even when it fails. Testing
a containing tag reaches the payload tests only when it succeeds. -/
def test (world : World) : List (Path × String) → Bool × List Nat
  | [] => (true, [])
  | (path, expected) :: remaining =>
    match world.constructors.find? (·.path == path) with
    | none => (false, [])
    | some current =>
      let inspected := current.obligation.toList
      if current.tag == expected then
        let (matched, nested) := test world remaining
        (matched, inspected ++ nested)
      else (false, inspected)

def inspections (world : World) : List Arm → List Nat
  | [] => []
  | arm :: remaining =>
    let (matched, inspected) := test world arm.tests
    if matched && arm.guard then inspected
    else inspected ++ inspections world remaining

def canExit (world : World) (arms : List Arm) : Bool :=
  let inspected := inspections world arms
  world.pending.all (inspected.contains ·)

end RilAccess.ResultInspection
