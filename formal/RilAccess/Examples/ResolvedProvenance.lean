import RilAccess.Provenance.Machine
import RilAccess.Provenance.Kernel

set_option maxRecDepth 8192
set_option maxHeartbeats 12000000

namespace RilAccess.Provenance.Examples

def localCode (actions : List Primitive) : List Instruction :=
  actions.zipIdx.map (fun (action, pc) => .step [action] (pc + 1))

def single (actions : List Primitive) : Program :=
  ⟨[⟨[], {}, localCode actions ++ [.ret none]⟩], []⟩

def accepts (program : Program) : Bool := (check program).isOk

def diagnoses (program : Program) (error : Error) : Bool :=
  match check program with
  | .ok _ => false
  | .error diagnostic => diagnostic.error == error

def overwrite : Program := single [.alloc 0 10, .alloc 0 20, .write 0]
def future : Program := single [.read 0, .alloc 0 10]
def looping : Program := ⟨[⟨[], {}, [.step [.alloc 0 10] 1, .step [.write 0] 2, .branch [0, 3], .abort]⟩], []⟩
def divergentLoop : Program := ⟨[{ code := [.branch [0]] }], []⟩
def divergentRecursion : Program := ⟨[{ code := [.invoke 0 [] none 1, .ret none] }], []⟩

def beforeWrites (program : Program) (pc : Nat) (register : Register) : List Object :=
  match check program with
  | .error _ => []
  | .ok certificate =>
    (certificate.facts.filterMap fun
      | .point entry point world =>
        if entry.function == 0 && point == pc then (world.view register).map Prod.fst else none
      | _ => none).eraseDups

def mutWorker : Function :=
  ⟨[.mutable, .mutable], { writes := true }, localCode [.write 0, .write 1] ++ [.ret none]⟩

def sameSite (summarizedPair : Bool) : Program :=
  let caller : Function := ⟨[], {}, localCode [.alloc 0 10, .alloc 1 10, .alloc 2 10] ++ [
    .invoke 1 [⟨if summarizedPair then 2 else 0, .mutable⟩, ⟨1, .mutable⟩] none 4, .ret none]⟩
  ⟨[caller, mutWorker], []⟩

def fields (dynamic : Bool) : Program :=
  let setup := localCode [
    .alloc 0 10, .alloc 1 11, .alloc 2 12, .store 0 0 1 true, .store 0 1 2 true, .select 3 0 0]
  let select := if dynamic then [.select 4 0 0, .select 4 0 1] else [.select 4 0 1]
  let main : Function := ⟨[], {}, setup ++
    [.step select 7, .invoke 1 [⟨3, .mutable⟩, ⟨4, .mutable⟩] none 8, .ret none]⟩
  ⟨[main, mutWorker], [⟨10, 0, ⟨false, .mut⟩⟩, ⟨10, 1, ⟨false, .mut⟩⟩]⟩

def permutedFields : Program :=
  let setup := localCode [.alloc 0 10, .alloc 1 11, .alloc 2 12, .store 0 0 1 true, .store 0 1 2 true]
  let main : Function := ⟨[], {}, setup ++ [
    .branch [6, 8],
    .step [.select 3 0 0] 7, .step [.select 4 0 1] 10,
    .step [.select 3 0 1] 9, .step [.select 4 0 0] 10,
    .invoke 1 [⟨3, .mutable⟩, ⟨4, .mutable⟩] none 11, .ret none]⟩
  ⟨[main, mutWorker], [⟨10, 0, ⟨false, .mut⟩⟩, ⟨10, 1, ⟨false, .mut⟩⟩]⟩

def cycle : Program :=
  let setup := localCode [
    .alloc 0 10, .alloc 1 11, .alloc 2 12, .bind 0 0 .shared, .bind 1 1 .shared, .bind 2 2 .shared,
    .store 0 0 2, .store 1 0 2, .store 2 0 0]
  let caller : Function := ⟨[], {}, setup ++ [.invoke 1 [⟨0, .retained⟩, ⟨1, .retained⟩] none 10, .ret none]⟩
  let callee : Function := ⟨[.retained, .retained], { retains := true },
    localCode [.publish 0, .publish 1] ++ [.ret none]⟩
  ⟨[caller, callee], [⟨10, 0, ⟨false, .shared⟩⟩, ⟨11, 0, ⟨false, .shared⟩⟩, ⟨12, 0, ⟨false, .shared⟩⟩]⟩

def entryReturn (replace : Bool) : Program :=
  let setup := localCode [.alloc 0 10, .alloc 1 11, .bind 0 0 .shared, .bind 1 1 .shared, .store 0 0 1]
  let caller : Function := ⟨[], {}, setup ++ [.invoke 1 [⟨0, .retained⟩] (some (2, .shared)) 6, .ret none]⟩
  let update := if replace then [.alloc 1 12, .bind 1 1 .shared, .store 0 0 1] else []
  let select := localCode (update ++ [.select 2 0 0])
  let callee : Function := ⟨[.retained], { result := .retained 0, writes := replace }, select ++ [.ret (some 2)]⟩
  ⟨[caller, callee], [⟨10, 0, ⟨true, .shared⟩⟩]⟩

def wrapOld (operation : Primitive) : Program :=
  let caller : Function := ⟨[], {}, [
    .step [.alloc 0 10] 1,
    .invoke 1 [⟨0, .observe⟩] (some (1, .mut)) 2,
    .step [.select 2 1 0] 3,
    .step [.handoff 3 1] 4,
    .step [operation] 5,
    .ret none]⟩
  let factory : Function := ⟨[.observe], { result := .construction, contained := [⟨0, .ref⟩] },
    localCode [.alloc 1 11, .store 1 0 0] ++ [.ret (some 1)]⟩
  ⟨[caller, factory], [⟨11, 0, ⟨false, .ref⟩⟩]⟩

def upgradeOld : Program :=
  let wrapped := wrapOld (.read 0)
  let caller := wrapped.functions[0]?.getD ⟨[], {}, []⟩
  let updated := { caller with code := caller.code.set 3 (.step [.write 2] 4) }
  { wrapped with functions := wrapped.functions.set 0 updated }

def freezeOldView : Program :=
  let wrapped := wrapOld (.read 0)
  let caller := wrapped.functions[0]?.getD ⟨[], {}, []⟩
  let instruction := Instruction.invoke 1 [⟨0, .observe⟩] (some (1, .immutable)) 2
  let updated := { caller with code := caller.code.set 1 instruction }
  { wrapped with functions := wrapped.functions.set 0 updated }

def completeNewGraph (mode : Access) : Program :=
  let caller : Function := ⟨[], {}, [
    .invoke 1 [] (some (0, mode)) 1, .step [.select 1 0 0] 2, .step [.read 1] 3, .ret none]⟩
  let factory : Function := ⟨[], { result := .construction },
    localCode [.alloc 0 10, .alloc 1 11, .store 0 0 1 true] ++ [.ret (some 0)]⟩
  ⟨[caller, factory], [⟨10, 0, ⟨false, .immutable⟩⟩]⟩

def endedArgument : Program :=
  let caller : Function := ⟨[], {}, [
    .step [.alloc 0 10] 1, .invoke 1 [⟨0, .construction⟩, ⟨0, .observe⟩] none 2, .ret none]⟩
  ⟨[caller, ⟨[.construction, .observe], {}, [.ret none]⟩], []⟩

def recursiveWriter (grounded : Bool) : Program :=
  let caller : Function := ⟨[], {}, [
    .step [.alloc 0 10] 1, .invoke 1 [⟨0, .mutable⟩] none 2, .ret none]⟩
  let body : Function := ⟨[.mutable], { writes := true }, [
    .branch (if grounded then [1, 3] else [3]),
    .step [.write 0] 2, .ret none,
    .invoke 1 [⟨0, .mutable⟩] none 4, .ret none]⟩
  ⟨[caller, body], []⟩

def retention (overwritten : Bool) : Program :=
  let setup := localCode [.alloc 0 10, .alloc 1 11, .alloc 2 12, .bind 1 1 .shared, .bind 2 2 .shared]
  let caller : Function := ⟨[], {}, setup ++
    [.invoke 1 [⟨0, .mutable⟩, ⟨1, .retained⟩, ⟨2, .retained⟩] none 6, .ret none]⟩
  let stores := [.store 0 0 1, .store 0 (if overwritten then 0 else 1) 2]
  let callee : Function := ⟨[.mutable, .retained, .retained], { writes := true, retains := true },
    localCode stores ++ [.ret none]⟩
  ⟨[caller, callee], [⟨10, 0, ⟨true, .shared⟩⟩, ⟨10, 1, ⟨true, .shared⟩⟩]⟩

def writeThroughWrapper (declared : Bool) : Program :=
  let main : Function := ⟨[], { retains := true }, localCode [.alloc 0 10, .bind 0 0 .shared] ++
    [.invoke 1 [⟨0, .retained⟩] none 3, .ret none]⟩
  let wrapper : Function := ⟨[.retained], { writes := declared, retains := true }, [
    .step [.alloc 1 11] 1, .step [.store 1 0 0] 2,
    .invoke 2 [⟨1, .mutable⟩] none 3, .step [.publish 0] 4, .ret none]⟩
  let writer : Function := ⟨[.mutable], { writes := true },
    localCode [.select 1 0 0, .write 1] ++ [.ret none]⟩
  ⟨[main, wrapper, writer], [⟨11, 0, ⟨false, .shared⟩⟩]⟩

def temporaryForward : Program :=
  let main : Function := ⟨[], {}, localCode [.alloc 0 10, .alloc 1 11] ++
    [.invoke 1 [⟨0, .mutable⟩, ⟨1, .mutable⟩] none 3, .ret none]⟩
  let forwarding : Function := ⟨[.mutable, .mutable], { writes := true }, [
    .step [.write 0] 1, .invoke 2 [⟨0, .observe⟩, ⟨1, .mutable⟩] none 2, .ret none]⟩
  let storing : Function := ⟨[.observe, .mutable], { writes := true }, localCode [.store 1 0 0] ++ [.ret none]⟩
  ⟨[main, forwarding, storing], [⟨11, 0, ⟨false, .ref⟩⟩]⟩

def abortingWriter (declared : Bool) : Program :=
  let main : Function := ⟨[], {}, [
    .step [.alloc 0 10] 1, .invoke 1 [⟨0, .mutable⟩] none 2, .ret none]⟩
  let callee : Function := ⟨[.mutable], { writes := declared }, [.step [.write 0] 1, .abort]⟩
  ⟨[main, callee], []⟩

def localFactoryWrite (declared : Bool) : Program :=
  let main : Function := ⟨[], {}, [
    .invoke 2 [] (some (0, .mut)) 1, .invoke 2 [] (some (1, .mut)) 2,
    .invoke 1 [⟨1, .construction⟩] none 3, .ret none]⟩
  let callee : Function := ⟨[.construction], { writes := declared }, [
    .step [.alloc 0 11] 1, .invoke 2 [] (some (1, .mut)) 2, .step [.write 1] 3, .ret none]⟩
  let factory : Function := ⟨[], { result := .construction }, [.step [.alloc 0 10] 1, .ret (some 0)]⟩
  ⟨[main, callee, factory], []⟩

def examples : List (String × Bool) :=
  [("resolved provenance: root replacement removes prior origin",
    decide (beforeWrites overwrite 2 0 = [⟨20, none⟩])),
   ("resolved provenance: future allocation cannot justify earlier access", diagnoses future .unavailable),
   ("resolved provenance: statically pruned branch cannot justify an authority use",
    diagnoses (recursiveWriter false) .unusedParameter),
   ("resolved provenance: accepts loops and recursion without a normal exit",
    accepts divergentLoop && accepts divergentRecursion),
   ("resolved provenance: repeated allocation at one site converges",
    agrees (beforeWrites looping 1 0) [⟨10, none⟩, ⟨10, some 0⟩]),
   ("resolved provenance: the first object at a site is distinct from later allocations", accepts (sameSite false)),
   ("resolved provenance: summarized objects at a site do not establish separation", diagnoses (sameSite true) .overlap),
   ("resolved provenance: exact fields support disjoint mutable calls", accepts (fields false)),
   ("resolved provenance: branches preserve correlation when swapping disjoint fields", accepts permutedFields),
   ("resolved provenance: unknown index must check all possible selections", diagnoses (fields true) .overlap),
   ("resolved provenance: cyclic heap exposes the common descendant", diagnoses cycle .overlap),
   ("resolved provenance: a root return may select an old entry child", accepts (entryReturn false)),
   ("resolved provenance: post-entry insertion cannot fabricate an entry source", diagnoses (entryReturn true) .returnSource),
   ("resolved provenance: new wrapper composes old ref provenance with live independent path",
    accepts (wrapOld (.read 0))),
   ("resolved provenance: a projection derived from a handed-off wrapper expires",
    diagnoses (wrapOld (.read 2)) .unavailable),
   ("resolved provenance: a new wrapper cannot upgrade an old read-only member", diagnoses upgradeOld .access),
   ("resolved provenance: an old live ref prevents immutable reception", diagnoses freezeOldView .construction),
   ("resolved provenance: a newly allocated child in a plain slot belongs to the complete new graph",
    accepts (completeNewGraph .immutable) && accepts (completeNewGraph .mut)),
   ("resolved provenance: new argument expires before a later argument", diagnoses endedArgument .unavailable),
   ("resolved provenance: base-case write grounds recursion", accepts (recursiveWriter true)),
   ("resolved provenance: outward shared stores keep parameter retention alive", accepts (retention false)),
   ("resolved provenance: overwritten shared store cannot justify retention", diagnoses (retention true) .unusedParameter),
   ("resolved provenance: a write through a nested call and new wrapper reaches the old formal",
    accepts (writeThroughWrapper true) && diagnoses (writeThroughWrapper false) .signature),
   ("resolved provenance: forwarding a call-scoped ref view cannot publish it",
    diagnoses temporaryForward .schema),
   ("resolved provenance: a write on an aborting prefix still requires its signature clause",
    accepts (abortingWriter true) && diagnoses (abortingWriter false) .signature),
   ("resolved provenance: writes to a later factory instance discharge locally",
    accepts (localFactoryWrite false) && diagnoses (localFactoryWrite true) .signature)]

theorem examples_pass : examples.all Prod.snd = true := by decide +kernel

theorem divergent_loop_steps :
    ∃ run : Nat → Machine,
      run 0 = .running 0 0 {} [] ∧
      ∀ n, run n = .running 0 0 {} [] ∧ MachineStep divergentLoop.erase (run n) (run (n + 1)) := by
  exact ⟨fun _ => .running 0 0 {} [], rfl, fun _ => ⟨rfl, .branch rfl (by decide)⟩⟩

theorem divergent_recursion_steps :
    ∃ run : Nat → Machine,
      run 0 = .running 0 0 {} [] ∧
      ∀ n, (∃ stack, run n = .running 0 0 {} stack ∧ stack.length = n) ∧
        MachineStep divergentRecursion.erase (run n) (run (n + 1)) := by
  let continuation : Continuation := ⟨0, 1, none, {}, none⟩
  refine ⟨fun n => .running 0 0 {} (List.replicate n continuation), rfl, ?_⟩
  intro n
  exact ⟨⟨_, rfl, List.length_replicate⟩, .enter rfl rfl⟩

/-- Non-vacuity of the main theorem on an actual allocation and reassignment. -/
theorem overwrite_executes :
    Executes overwrite.erase 0 {} (.returned none
      ((RawFrame.allocate (RawFrame.allocate {} 0 10) 0 20))) := by
  have first : Executes overwrite.erase 0 {} (.at 1 (RawFrame.allocate {} 0 10)) :=
    .step (action := .alloc 0 10) .start (by rfl) (by decide) (by rfl)
  have second : Executes overwrite.erase 0 {} (.at 2 ((RawFrame.allocate {} 0 10).allocate 0 20)) :=
    .step (action := .alloc 0 20) first (by rfl) (by decide) (by rfl)
  have write : Executes overwrite.erase 0 {} (.at 3 ((RawFrame.allocate {} 0 10).allocate 0 20)) :=
    .step (action := .write 0) second (by rfl) (by decide) (by rfl)
  exact .ret write (by rfl) (by rfl)

theorem recursive_executes :
    let program := recursiveWriter true
    let caller := RawFrame.allocate {} 0 10
    MachineTrace program.erase (.finished none caller) := by
  let program := recursiveWriter true
  let caller := RawFrame.allocate {} 0 10
  let entry : RawFrame := ⟨[(0, ⟨10, none⟩)], caller.memory⟩
  let first : Continuation := ⟨0, 2, none, caller, none⟩
  let second : Continuation := ⟨1, 4, none, entry, none⟩
  have allocated : MachineTrace program.erase (.running 0 1 caller []) :=
    .tail .start (.primitive (action := .alloc 0 10) rfl (by decide) rfl)
  have called : MachineTrace program.erase (.running 1 0 entry [first]) :=
    .tail allocated (.enter rfl rfl)
  have recurse : MachineTrace program.erase (.running 1 3 entry [first]) :=
    .tail called (.branch rfl (by decide))
  have nested : MachineTrace program.erase (.running 1 0 entry [second, first]) :=
    .tail recurse (.enter rfl rfl)
  have base : MachineTrace program.erase (.running 1 1 entry [second, first]) :=
    .tail nested (.branch rfl (by decide))
  have wrote : MachineTrace program.erase (.running 1 2 entry [second, first]) :=
    .tail base (.primitive (action := .write 0) rfl (by decide) rfl)
  have innerDone : MachineTrace program.erase (.running 1 4 entry [first]) :=
    .tail wrote (.leave rfl rfl rfl)
  have outerDone : MachineTrace program.erase (.running 0 2 caller []) :=
    .tail innerDone (.leave rfl rfl rfl)
  exact .tail outerDone (.finish rfl rfl)

end RilAccess.Provenance.Examples
