namespace RilAccess.RecursiveStorage.Examples

inductive Branch where
  | unchanged
  | store (formal : Nat)
  | call (callee : Nat) (arguments : List Nat)

-- Each outcome describes the final value of one slot on a finite normal path.
-- `none` preserves the entry value. An empty outcome list has no normal exit.
def outcomes : Nat → List (List Branch) → Nat → List (Option Nat)
  | 0, _, _ => []
  | fuel + 1, bodies, owner => (bodies[owner]?.getD []).flatMap fun
    | .unchanged => [none]
    | .store formal => [some formal]
    | .call callee arguments => (outcomes fuel bodies callee).filterMap fun
      | none => some none
      | some formal => arguments[formal]?.map some

def observe (fuel : Nat) (bodies : List (List Branch)) : Bool × List Nat :=
  let exits := outcomes fuel bodies 0
  let sources := exits.filterMap id
  let formals := List.range (sources.foldl max 0 + 1)
  (!exits.isEmpty && exits.all Option.isSome, formals.filter sources.contains)

def cases : List (String × List (List Branch)) :=
  [("recursion_can_keep_a_guaranteed_storage_contract", [[.call 0 [0, 1], .store 1]]),
   ("mutual_recursion_publishes_both_replacement_sources",
     [[.call 1 [0, 2, 1], .store 1], [.call 0 [0, 1, 2]]]),
   ("alias_dispatch_can_write_one_of_two_destinations",
     [[.call 1 [0, 1], .call 2 [0, 1]], [.store 1], [.unchanged]]),
   ("recursive_store_can_preserve_the_entry_value", [[.call 0 [0, 1], .store 1, .unchanged]]),
   ("propagation_can_exit_before_a_storage_update", [[.store 1, .unchanged]])]

def contracts : List (String × (Bool × List Nat)) :=
  cases.map fun (name, bodies) => (name, observe 8 bodies)

def examples : List (String × Bool) :=
  ("recursive storage: only finite normal executions contribute writes",
    decide (outcomes 8 [[.call 0 [0, 1]]] 0 = [])) ::
  ("recursive storage: finite examples stabilize", cases.all fun (_, bodies) =>
    decide (observe 8 bodies = observe 9 bodies)) ::
  (cases.zip [(true, [1]), (true, [1, 2]), (false, [1]), (false, [1]), (false, [1])]).map
    fun ((name, bodies), expected) => (name, decide (observe 8 bodies = expected))

theorem examples_all_pass : examples.all Prod.snd = true := by decide +kernel

end RilAccess.RecursiveStorage.Examples
