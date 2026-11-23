namespace RilAccess.ResultInspection

abbrev Path := List Nat

structure Constructor where
  path : Path
  tag : String
  obligation : Option Nat := none

structure World where
  constructors : List Constructor
  pending : List Nat

def receive (constructors : List Constructor) : World :=
  ⟨constructors, constructors.filterMap Constructor.obligation⟩

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

/-- Each visited element is tested independently. Stopping traversal leaves
the obligations at unvisited positions pending. -/
def canExitAfterTraversal (world : World) (indices : List Nat) : Bool :=
  let inspected := indices.flatMap (fun index => (test world [([index], "Ok")]).2)
  world.pending.all (inspected.contains ·)

/-- Propagation either continues or transfers the failed value to a normal
exit. Any remaining obligation must be among that value's constructors. -/
def canPropagate (world : World) : Bool :=
  match world.constructors.find? (·.path.isEmpty) with
  | some root =>
    if root.tag == "Err" || root.tag == "None" then
      let returned := world.constructors.filterMap Constructor.obligation
      world.pending.all (returned.contains ·)
    else true
  | none => false

end RilAccess.ResultInspection
