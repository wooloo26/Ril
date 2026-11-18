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
    resource parameter. The route advances to the next resource when the call
    returns normally. Panics raised by cleanup routines are outside this model. -/
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

/-- A cleanup call saves a normal continuation to resource expiry. Unwinding
    skips this continuation because the call supplies no abort target. -/
theorem cleanupRoute_call_continuation
    (member : Instruction.invoke target args destination next onAbort ∈ cleanupRoute first resources) :
    onAbort = none ∧
      ∃ register, Instruction.step [.expire register] (next + 1) ∈ cleanupRoute first resources := by
  unfold cleanupRoute at *
  obtain ⟨⟨slot, index⟩, found, instruction⟩ := List.mem_flatMap.mp member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at instruction
  rcases instruction with call | expiry
  · cases call
    refine ⟨rfl, slot.register, List.mem_flatMap.mpr ⟨(slot, index), found, ?_⟩⟩
    simp
  · cases expiry

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
