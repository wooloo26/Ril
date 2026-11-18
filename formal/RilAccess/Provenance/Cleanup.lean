import RilAccess.Provenance.Machine

namespace RilAccess.Provenance

structure CleanupSlot where
  register : Register
  site : Nat
  closer : Nat
  captured : List Argument := []
  deriving Repr, DecidableEq

/-- Resolved synchronous cleanup dispatch. Each registration captures the
    handler that is active at that declaration. The target accepts one mutable
    resource parameter and completes normally on the supported slice. -/
inductive ScopeDeclaration where
  | handler (effect target : Nat)
  | resource (slot : CleanupSlot) (effect : Option Nat := none)
  deriving Repr, DecidableEq

def resolveCleanups (handlers : List (Nat × Nat)) : List ScopeDeclaration → List CleanupSlot
  | [] => []
  | .handler effect target :: rest => resolveCleanups (putSlot handlers effect target) rest
  | .resource slot effect :: rest =>
    let closer := (effect.bind (getSlot handlers)).getD slot.closer
    { slot with closer } :: resolveCleanups handlers rest

def cleanupRoute (first : Nat) (resources : List CleanupSlot) : List Instruction :=
  resources.reverse.zipIdx.flatMap fun (slot, index) =>
    let pc := first + 2 * index
    [.invoke slot.closer (⟨slot.register, .mutable⟩ :: slot.captured) none (pc + 1),
      .step [.expire slot.register] (pc + 2)]

def cleanupInvocations (code : List Instruction) : List Nat :=
  code.filterMap fun
    | .invoke target _ _ _ _ => some target
    | _ => none

theorem cleanupRoute_lifo (first : Nat) (resources : List CleanupSlot) :
    cleanupInvocations (cleanupRoute first resources) = resources.reverse.map CleanupSlot.closer := by
  unfold cleanupInvocations cleanupRoute
  rw [List.filterMap_flatMap]
  simp only [List.filterMap_cons, List.filterMap_nil]
  have mapped (pairs : List (CleanupSlot × Nat)) :
      pairs.flatMap (fun pair => [pair.1.closer]) = pairs.map (fun pair => pair.1.closer) := by
    induction pairs <;> simp_all
  rw [mapped]
  change resources.reverse.zipIdx.map (CleanupSlot.closer ∘ Prod.fst) = _
  rw [← List.map_map, List.zipIdx_map_fst]

/-- The abort continuation enters the same checked cleanup sequence as normal
    exit and then continues unwinding. Registration and expiry are erased. -/
def lowerScope (declarations : List ScopeDeclaration) (body : Nat)
    (arguments : List Argument) : List Instruction :=
  let resources := resolveCleanups [] declarations
  let allocation := resources.flatMap fun slot => [.alloc slot.register slot.site, .scope slot.register]
  let setup := allocation.zipIdx.map fun (operation, pc) => Instruction.step [operation] (pc + 1)
  let normal := setup.length + 1
  let unwinding := normal + 2 * resources.length + 1
  setup ++ [.invoke body arguments none normal (some unwinding)] ++
    cleanupRoute normal resources ++ [.ret none] ++ cleanupRoute unwinding resources ++ [.abort]

theorem later_handler_does_not_replace_saved_cleanup (slot : CleanupSlot) (effect above below : Nat) :
    resolveCleanups [] [.handler effect above, .resource slot (some effect), .handler effect below] =
      [{ slot with closer := above }] := by
  simp [resolveCleanups, putSlot, getSlot]

end RilAccess.Provenance
