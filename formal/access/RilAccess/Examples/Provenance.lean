import RilAccess.Contracts
import RilAccess.Provenance.Limits

set_option maxRecDepth 4096
set_option maxHeartbeats 8000000

namespace RilAccess.Examples

def parameter : Source := ⟨.parameter, 0⟩
def ambient : Source := ⟨.module, 1⟩
def freshA : Source := ⟨.allocation, 2⟩
def freshB : Source := ⟨.allocation, 3⟩

def straight (actions : List Action) (checks : List Check := []) : ResolvedProgram :=
  ⟨0, actions.zipIdx.map (fun (action, pc) =>
    ⟨pc, action, [if pc + 1 < actions.length then some (pc + 1) else none]⟩), checks⟩

def accepts (p : ResolvedProgram) : Bool := (analyze p).isOk

def aliasWrite : ResolvedProgram := straight
  [.seed 0 parameter, .copy 0 1 .binding, .emit .write 1 false .binding]
  [.exactEvents [.event .write parameter]]

def hiddenAlias : ResolvedProgram := { aliasWrite with checks := [.exactEvents []] }

def rootless : ResolvedProgram := straight [.copy 0 1 .higherOrder, .emit .write 1 false .binding]

def cyclicGraph : ResolvedProgram := straight
  [.seed 0 freshA, .seed 1 parameter, .store 0 0 1, .store 1 0 0,
    .emit .retain 0 true .aggregate]
  [.present (.event .retain freshA), .present (.event .retain parameter)]

def hiddenClosure : ResolvedProgram := straight
  [.seed 0 ambient, .copy 0 1 .closure, .emit .capture 1 false .closure,
    .emit .write 1 false .higherOrder]
  [.exactEvents []]

def containedReturn : ResolvedProgram := straight
  [.seed 0 freshA, .seed 1 parameter, .store 0 0 1,
    .emit .rootReturn 0 false .returnValue, .emit .containedReturn 0 true .returnValue]
  [.present (.event .rootReturn freshA), .absent (.event .rootReturn parameter),
    .present (.event .containedReturn parameter)]

def unknownSelection : ResolvedProgram := straight
  [.seed 0 freshA, .seed 1 freshB, .seed 2 parameter,
    .store 2 0 0, .store 2 1 1, .project 2 0 3, .emit .write 3 false .projection]
  [.present (.event .write freshA), .present (.event .write freshB)]

/-- Field-insensitivity is deliberately visible as a precision loss. -/
def unsupportedSeparation : ResolvedProgram :=
  { unknownSelection with checks := [.absent (.event .write freshB)] }

def cleanupWrite : ResolvedProgram :=
  ⟨0, [⟨0, .seed 0 parameter, [some 1]⟩,
    ⟨1, .enter .cleanup 7, [some 3]⟩,
    ⟨2, .emit .read 0 false .binding, [none]⟩,
    ⟨3, .emit .write 0 false .cleanup, [some 4]⟩,
    ⟨4, .leave .cleanup, [none]⟩],
    [.present (.event .write parameter), .absent (.event .read parameter)]⟩

def handlerWrite : ResolvedProgram := straight
  [.seed 0 parameter, .enter .handler 3, .emit .write 0 false .handler,
    .leave .resume, .leave .handler]
  [.present (.event .write parameter)]

def namedModuleRead : ResolvedProgram := straight
  [.seed 0 ambient, .copy 0 1 .module, .emit .read 1 false .higherOrder]
  [.exactEvents [.event .read ambient]]

def hiddenTaskSource : ResolvedProgram := straight
  [.seed 0 ambient, .copy 0 1 .closure, .enter .task 1,
    .emit .read 1 false .higherOrder]
  [.absent (.event .read ambient)]

def recursiveUseRules : List (Rule Nat) := [⟨[0], 1⟩, ⟨[1], 0⟩]

def groundedUseRules : List (Rule Nat) := ⟨[], 0⟩ :: recursiveUseRules

def staleRoot : ResolvedProgram := straight
  [.seed 0 parameter, .seed 0 freshA, .emit .read 0 false .binding]
  [.present (.event .read parameter), .present (.event .read freshA)]

def OverwriteInvariant (c : Configuration) : Prop :=
  (c.pc = some 2 → ∀ o ∈ c.roots 0, o.source = freshA) ∧
  (∀ e ∈ c.events, e.origin.source = freshA)

theorem overwrite_step_preserves (hm : OverwriteInvariant c) (hs : Step staleRoot c d) :
    OverwriteInvariant d := by
  cases hs with
  | @next i c d target hi hpc hex hn =>
    have code : i = ⟨0, .seed 0 parameter, [some 1]⟩ ∨
        i = ⟨1, .seed 0 freshA, [some 2]⟩ ∨
        i = ⟨2, .emit .read 0 false .binding, [none]⟩ := by
      simpa [staleRoot, straight] using hi
    rcases code with rfl | rfl | rfl
    · simp only [List.mem_singleton] at hn
      subst target
      cases hex
      exact ⟨by simp, hm.2⟩
    · simp only [List.mem_singleton] at hn
      subst target
      cases hex
      refine ⟨?_, hm.2⟩
      intro _ o ho
      simp [setRoot] at ho
      subst o
      rfl
    · simp only [List.mem_singleton] at hn
      subst target
      cases hex with
      | @emitRoot o k r m c ho =>
        refine ⟨by simp, ?_⟩
        intro e he
        rcases List.mem_cons.mp he with rfl | he
        · exact hm.1 hpc o ho
        · exact hm.2 e he

theorem overwrite_only_new_source (ht : Trace staleRoot (initial staleRoot.entry) c)
    (he : e ∈ c.events) : e.origin.source = freshA := by
  have hm : OverwriteInvariant (initial staleRoot.entry) := by
    simp [OverwriteInvariant, initial, staleRoot, straight]
  have final : OverwriteInvariant c := by
    clear he
    induction ht with
    | refl => exact hm
    | tail _ step ih => exact overwrite_step_preserves ih step
  exact final.2 e he

theorem overwrite_old_source_spurious :
    Fact.event .read parameter ∈ solve staleRoot.rules := by decide +kernel

def sampleOrigin : Origin := ⟨freshA, 0, 0, 0, 0⟩
def externalOrigin : Origin := ⟨parameter, 0, 1, 0, 0⟩
def writeEvent : Event := ⟨.write, sampleOrigin, .binding⟩
def privateFootprint : Footprint := ⟨[sampleOrigin], [], []⟩

/-- A nonempty accepted execution, rather than just an accepted dead program. -/
def witness : ResolvedProgram :=
  ⟨0, [⟨0, .seed 0 parameter, [some 1]⟩,
    ⟨1, .emit .write 0 false .binding, [none]⟩], [.present (.event .write parameter)]⟩

def witnessStart := initial witness.entry
def witnessOrigin := freshOrigin witnessStart parameter
def witnessSeeded : Configuration :=
  { setRoot witnessStart 0 witnessOrigin with nextObject := 1, pc := some 1 }
def witnessEvent : Event := ⟨.write, witnessOrigin, .binding⟩
def witnessEnd : Configuration :=
  { witnessSeeded with events := [witnessEvent], pc := none }

theorem witness_accepted : accepts witness = true := by decide +kernel

theorem witness_executes : Trace witness witnessStart witnessEnd := by
  have first : Step witness witnessStart witnessSeeded :=
    .next (i := ⟨0, .seed 0 parameter, [some 1]⟩) (by simp [witness]) rfl
      .seed (by simp)
  have second : Step witness witnessSeeded witnessEnd :=
    .next (i := ⟨1, .emit .write 0 false .binding, [none]⟩) (by simp [witness]) rfl
      (.emitRoot (by simp [witnessSeeded, setRoot])) (by simp)
  exact .tail (.tail .refl first) second

theorem witness_event_present : witnessEvent ∈ witnessEnd.events := by
  simp [witnessEnd]

def fixtures : List (String × Bool) :=
  [("shared alias accepted", accepts aliasWrite),
   ("hidden alias rejected", !accepts hiddenAlias),
   ("missing origin rejected", !accepts rootless),
   ("cycles and contained origins", accepts cyclicGraph),
   ("hidden closure rejected", !accepts hiddenClosure),
   ("root/contained distinction", accepts containedReturn),
   ("unknown index union", accepts unknownSelection),
   ("unproved separation rejected", !accepts unsupportedSeparation),
   ("abort cleanup state", accepts cleanupWrite),
   ("handler state", accepts handlerWrite),
   ("module identity", accepts namedModuleRead),
   ("hidden task source rejected", !accepts hiddenTaskSource),
   ("ungrounded recursive use", decide (solve recursiveUseRules = [])),
   ("grounded recursive use", decide (1 ∈ solve groundedUseRules)),
   ("visible conservative overwrite", accepts staleRoot),
   ("joint permute relation", correlatedSeparated [([0], [1]), ([1], [0])]),
   ("unknown selections overlap", !disjointUnknownSelections [0, 1] [1, 2]),
   ("confined write discharged", decide (discharge 0 0 0 privateFootprint [writeEvent] = [])),
   ("nonempty execution", accepts witness)]

theorem fixtures_all_pass : fixtures.all Prod.snd = true := by decide +kernel

end RilAccess.Examples
