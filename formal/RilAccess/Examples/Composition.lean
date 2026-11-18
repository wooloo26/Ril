import RilAccess.Provenance.Cleanup
import RilAccess.Provenance.Module

set_option maxRecDepth 8192
set_option maxHeartbeats 16000000

namespace RilAccess.Provenance.Examples

def closingWorker : Function :=
  ⟨[.mutable], { writes := true }, [.step [.write 0] 1, .ret none]⟩

def writingHandler : Function :=
  ⟨[.mutable, .mutable], { writes := true }, [.step [.write 0] 1, .step [.write 1] 2, .ret none]⟩

def declarations : List ScopeDeclaration :=
  [.handler 7 3, .resource ⟨1, 10, 4, [⟨0, .mutable⟩]⟩ (some 7),
    .resource ⟨2, 11, 2, []⟩, .handler 7 4]

def cleanupProgram (writes : Bool) : Program :=
  let main : Function := ⟨[], {}, [
    .step [.alloc 0 9] 1, .invoke 1 [⟨0, .mutable⟩] none 2, .ret none]⟩
  let wrapper : Function := ⟨[.mutable], { writes }, lowerScope declarations 5 []⟩
  let failing : Function := ⟨[], {}, [.abort]⟩
  ⟨[main, wrapper, closingWorker, writingHandler, failing, failing], []⟩

def divergingCleanupProgram : Program :=
  let resources := [.resource ⟨0, 10, 1, []⟩, .resource ⟨1, 11, 2, []⟩]
  let main : Function := { code := lowerScope resources 3 [] }
  let diverging : Function := { closingWorker with code := [.step [.write 0] 1, .branch [1]] }
  ⟨[main, closingWorker, diverging, { code := [.ret none] }], []⟩

def replaceCleanupInstruction (pc : Nat) (instruction : Instruction) : Program :=
  let program := cleanupProgram true
  let wrapper := program.functions[1]?.getD ⟨[], {}, []⟩
  let broken := { wrapper with code := wrapper.code.set pc instruction }
  { program with functions := program.functions.set 1 broken }

def summaryReuse (mismatch : Bool) : Bool :=
  let producer : Program := ⟨[closingWorker], []⟩
  let consumer : Program := ⟨[], []⟩
  let arguments : List Argument := [⟨0, .mutable⟩]
  match primitive consumer (.alloc 0 9) {} with
  | .error _ => false
  | .ok (before, _) =>
    match prepare closingWorker before arguments with
    | .error _ => false
    | .ok call =>
      match summarize producer ⟨0, call.entered⟩ with
      | .error _ => false
      | .ok summary =>
        let input := if mismatch then
          (primitive consumer (.alloc 1 10) before).toOption.map Prod.fst |>.getD before
          else before
        match summary.apply consumer startEntry 1 2 input arguments none with
        | .error .summaryEntry => mismatch
        | .ok results => !mismatch && results.any (fun
            | .point _ 2 _ => true
            | _ => false) && (failures results).isEmpty
        | .error _ => false

def compositionFixtures : List (String × Bool) :=
  [("composition: exceptional exit closes both resources through the installed handler",
    (check (cleanupProgram true)).isOk),
   ("composition: the checker accepts a synchronous cleanup that diverges",
    (check divergingCleanupProgram).isOk),
   ("composition: an outer write by a cleanup handler requires its caller's state row",
    match check (cleanupProgram false) with
    | .error err => err.function == 1 && err.error == .contract
    | _ => false),
   ("composition: scoped paths must expire in LIFO order",
    match check (replaceCleanupInstruction 11 (.step [.expire 1] 12)) with
    | .error err => err.error == .scopeOrder
    | _ => false),
   ("composition: a cleaned resource is unavailable in the next handler",
    match check (replaceCleanupInstruction 12 (.step [.read 2] 13)) with
    | .error err => err.error == .unavailable
    | _ => false),
   ("composition: an abort cannot bypass pending cleanup",
    match check (replaceCleanupInstruction 4 (.invoke 5 [] none 5)) with
    | .error err => err.error == .scopeOrder
    | _ => false),
   ("composition: a body-derived summary applies without the provider's code", summaryReuse false),
   ("composition: an incompatible abstract entry cannot reuse the summary", summaryReuse true)]

theorem compositionFixtures_pass : compositionFixtures.all Prod.snd = true := by decide +kernel

theorem diverging_cleanup_stays_in_first_cleanup_call :
    ∃ (frame : RawFrame) (continuation : Continuation),
      continuation.function = 0 ∧ continuation.next = 6 ∧
      let state := Machine.running 2 1 frame [continuation]
      MachineTrace divergingCleanupProgram.erase state ∧
      MachineStep divergingCleanupProgram.erase state state ∧
      ∀ next, MachineStep divergingCleanupProgram.erase state next → next = state := by
  let code := divergingCleanupProgram.erase
  let first := RawFrame.allocate {} 0 10
  let both := first.allocate 1 11
  let body : RawFrame := ⟨[], both.memory⟩
  let closeFrame : RawFrame := ⟨[(0, ⟨11, none⟩)], both.memory⟩
  let afterBody : Continuation := ⟨0, 5, none, both, some 10⟩
  let afterClose : Continuation := ⟨0, 6, none, both, none⟩
  have allocated₁ : MachineTrace code (.running 0 1 first []) :=
    .tail .start (.primitive (action := .alloc 0 10) rfl (by decide) rfl)
  have scoped₁ : MachineTrace code (.running 0 2 first []) :=
    .tail allocated₁ (.primitive (action := .skip) rfl (by decide) rfl)
  have allocated₂ : MachineTrace code (.running 0 3 both []) :=
    .tail scoped₁ (.primitive (action := .alloc 1 11) rfl (by decide) rfl)
  have scoped₂ : MachineTrace code (.running 0 4 both []) :=
    .tail allocated₂ (.primitive (action := .skip) rfl (by decide) rfl)
  have enteredBody : MachineTrace code (.running 3 0 body [afterBody]) :=
    .tail scoped₂ (.enter rfl rfl)
  have returning : MachineTrace code (.running 0 5 both []) :=
    .tail enteredBody (.leave rfl rfl rfl)
  have closing : MachineTrace code (.running 2 0 closeFrame [afterClose]) :=
    .tail returning (.enter rfl rfl)
  have wrote : MachineTrace code (.running 2 1 closeFrame [afterClose]) :=
    .tail closing (.primitive (action := .write 0) rfl (by decide) rfl)
  refine ⟨closeFrame, afterClose, rfl, rfl, wrote, .branch rfl (by decide), ?_⟩
  intro next step
  have instruction : rawInstruction divergingCleanupProgram.erase 2 1 = some (.branch [1]) := rfl
  cases step <;> simp_all

theorem exceptional_cleanup_executes :
    let program := cleanupProgram true
    let main := RawFrame.allocate {} 0 9
    let withResources := (main.allocate 1 10).allocate 2 11
    MachineTrace program.erase (.panicked withResources.memory) := by
  let program := cleanupProgram true
  let main := RawFrame.allocate {} 0 9
  let saved : Continuation := ⟨0, 2, none, main, none⟩
  let entered : RawFrame := ⟨[(0, ⟨9, none⟩)], main.memory⟩
  let first := entered.allocate 1 10
  let second := first.allocate 2 11
  let body : RawFrame := ⟨[], second.memory⟩
  let panicTarget : Continuation := ⟨1, 5, none, second, some 10⟩
  have started : MachineTrace program.erase (.running 0 1 main []) :=
    .tail .start (.primitive (action := .alloc 0 9) rfl (by decide) rfl)
  have wrapper : MachineTrace program.erase (.running 1 0 entered [saved]) :=
    .tail started (.enter rfl rfl)
  have initialized₁ : MachineTrace program.erase (.running 1 1 first [saved]) :=
    .tail wrapper (.primitive (action := .alloc 1 10) rfl (by decide) rfl)
  have held₁ : MachineTrace program.erase (.running 1 2 first [saved]) :=
    .tail initialized₁ (.primitive (action := .skip) rfl (by decide) rfl)
  have initialized₂ : MachineTrace program.erase (.running 1 3 second [saved]) :=
    .tail held₁ (.primitive (action := .alloc 2 11) rfl (by decide) rfl)
  have held₂ : MachineTrace program.erase (.running 1 4 second [saved]) :=
    .tail initialized₂ (.primitive (action := .skip) rfl (by decide) rfl)
  have inBody : MachineTrace program.erase (.running 5 0 body [panicTarget, saved]) :=
    .tail held₂ (.enter rfl rfl)
  have unwinding : MachineTrace program.erase (.running 1 10 second [saved]) :=
    .tail inBody (.abort rfl)
  let close₂ : RawFrame := ⟨[(0, ⟨11, none⟩)], second.memory⟩
  let after₂ : Continuation := ⟨1, 11, none, second, none⟩
  have closing₂ : MachineTrace program.erase (.running 2 0 close₂ [after₂, saved]) :=
    .tail unwinding (.enter rfl rfl)
  have wrote₂ : MachineTrace program.erase (.running 2 1 close₂ [after₂, saved]) :=
    .tail closing₂ (.primitive (action := .write 0) rfl (by decide) rfl)
  have closed₂ : MachineTrace program.erase (.running 1 11 second [saved]) :=
    .tail wrote₂ (.leave rfl rfl rfl)
  have expired₂ : MachineTrace program.erase (.running 1 12 second [saved]) :=
    .tail closed₂ (.primitive (action := .skip) rfl (by decide) rfl)
  let close₁ : RawFrame := ⟨[(0, ⟨10, none⟩), (1, ⟨9, none⟩)], second.memory⟩
  let after₁ : Continuation := ⟨1, 13, none, second, none⟩
  have inHandler : MachineTrace program.erase (.running 3 0 close₁ [after₁, saved]) :=
    .tail expired₂ (.enter rfl rfl)
  have localWrite : MachineTrace program.erase (.running 3 1 close₁ [after₁, saved]) :=
    .tail inHandler (.primitive (action := .write 0) rfl (by decide) rfl)
  have outerWrite : MachineTrace program.erase (.running 3 2 close₁ [after₁, saved]) :=
    .tail localWrite (.primitive (action := .write 1) rfl (by decide) rfl)
  have closed₁ : MachineTrace program.erase (.running 1 13 second [saved]) :=
    .tail outerWrite (.leave rfl rfl rfl)
  have expired₁ : MachineTrace program.erase (.running 1 14 second [saved]) :=
    .tail closed₁ (.primitive (action := .skip) rfl (by decide) rfl)
  exact .tail expired₁ (.abort rfl)

end RilAccess.Provenance.Examples
