import RilAccess.Effects.Boundary
import RilAccess.Call.Summary

namespace RilAccess.CoreBoundary.Examples

def localOrigin : Origin := ⟨⟨.allocation, 1⟩, 7, 3, 9⟩
def external : Origin := ⟨⟨.module, 17⟩, 0, 1, 0⟩
def captured : Origin := ⟨⟨.capture, 4⟩, 5, 8, 2⟩
def foreign : Origin := ⟨⟨.foreign, 11⟩, 0, 2, 0⟩
def emptySummary : Summary := ⟨[], [], [], [], [], [], []⟩
def emptyRoots : Footprint := ⟨[], [], []⟩

def privateBoundary : Boundary :=
  ⟨{ emptySummary with writes := [localOrigin], effects := [3] }, emptySummary, emptySummary,
    ⟨[localOrigin], [], []⟩, emptyRoots, emptyRoots, [], []⟩

def handlerEnvironment : Boundary := { privateBoundary with handlerEnvironment := [external] }
def cleanupEnvironment : Boundary := { privateBoundary with cleanupEnvironment := [captured] }
def handlerState : Boundary := { privateBoundary with handler := { emptySummary with writes := [external] } }
def cleanupState : Boundary := { privateBoundary with cleanup := { emptySummary with writes := [foreign] } }

def handlerEffect : Boundary := { privateBoundary with handler := { emptySummary with effects := [3] } }
def cleanupEffect : Boundary := { privateBoundary with cleanup := { emptySummary with effects := [3] } }
def mixedEffects : Boundary :=
  { privateBoundary with
    body := { emptySummary with effects := [3, 4] },
    handler := { emptySummary with effects := [3, 5] },
    cleanup := { emptySummary with effects := [3, 6] } }
def outerHandler : Boundary := { privateBoundary with body := handled handlerEffect 3 }

def callInstance : CoreSummary.CallInstance := ⟨(fun _ _ => localOrigin), [1, 3, 9], 12, 14⟩

def pureSources : List Source := [external.source, captured.source]
def pureFnHandler : Summary := { emptySummary with namedReads := [external], effects := [10] }
def branchSummary : Summary := { emptySummary with writes := [localOrigin], effects := [3, 10] }
def dischargedBranch : Summary := dischargeSharedFnEffect branchSummary pureFnHandler 3

def atomStep (w : Integrated.World) (op : Integrated.Atom) : Integrated.World :=
  (Integrated.checkAtom op w).toOption.getD w

def fnOpAuthority : Integrated.World :=
  let w := atomStep Integrated.initialWorld (.allocate 0 ⟨false, .mut⟩ [])
  let w := atomStep w (.bind ⟨0, []⟩ 1 ⟨false, .shared⟩)
  let w := atomStep w (.retain ⟨1, []⟩)
  let w := atomStep w .enterScope
  let w := atomStep w (.parameter ⟨1, []⟩ 2 .mutable)
  let w := atomStep w (.parameter ⟨2, []⟩ 3 .observe)
  let w := atomStep w .activateParameters
  let w := atomStep w (.write ⟨2, []⟩)
  atomStep w (.read ⟨3, []⟩)

def afterFnOp : Integrated.World := (completeFnOp fnOpAuthority 1).getD fnOpAuthority
def regLive (w : Integrated.World) (r : Nat) : Bool := (Integrated.resolve w ⟨r, []⟩).any Integrated.live

def fixtures : List (String × Bool) :=
  [("core boundary: closed local state can discharge", (outward privateBoundary 7 9).isEmpty),
   ("core boundary: hidden handler environment blocks discharge", !(outward handlerEnvironment 7 9).isEmpty),
   ("core boundary: hidden cleanup environment blocks discharge", !(outward cleanupEnvironment 7 9).isEmpty),
   ("core boundary: handling eliminates its effect only", (handled handlerState 3).effects.isEmpty &&
      decide (external ∈ (handled handlerState 3).writes)),
   ("core boundary: handler's own-family effect remains outward", decide ((handled handlerEffect 3).effects = [3])),
   ("core boundary: residual cleanup effect remains outward", decide ((handled cleanupEffect 3).effects = [3])),
   ("core boundary: only protected body effects are eliminated", decide ((handled mixedEffects 3).effects = [4, 3, 5, 3, 6])),
   ("core boundary: outer handler may discharge the inner arm's effect", (handled outerHandler 3).effects.isEmpty),
   ("core boundary: actual handler state survives handling and discharge", (outward handlerState 7 9).any
      (fun event => decide (event.kind = .write ∧ event.origin = external))),
   ("core boundary: actual cleanup state survives handling and discharge", (outward cleanupState 7 9).any
      (fun event => decide (event.kind = .write ∧ event.origin = foreign))),
   ("core boundary: module identity cannot be rebound by call substitution", decide (CoreSummary.resolve callInstance (.concrete external) = external)),
   ("core boundary: selected capture identity cannot be rebound", decide (CoreSummary.resolve callInstance (.concrete captured) = captured)),
   ("core boundary: foreign identity cannot be rebound", decide (CoreSummary.resolve callInstance (.concrete foreign) = foreign)),
   ("core boundary: local allocation cannot impersonate an entry object", decide ((CoreSummary.resolve callInstance (.fresh localOrigin.source localOrigin.object)).object ∉ callInstance.existingObjects)),
   ("core boundary: local allocation keeps its producer source", decide ((CoreSummary.resolve callInstance (.fresh localOrigin.source localOrigin.object)).source = localOrigin.source)),
   ("core boundary: fn op arm completion revokes temporary mut parameter and derived observer",
      regLive fnOpAuthority 2 && regLive fnOpAuthority 3 &&
      (completeFnOp fnOpAuthority 1).isSome &&
      !regLive afterFnOp 2 && !regLive afterFnOp 3),
   ("core boundary: fn op arm completion deactivates operation loans and releases outer writer",
      afterFnOp.loans.all (fun loan => !loan.active) &&
      (Integrated.checkAtom (.write ⟨1, []⟩) afterFnOp).isOk),
   ("core boundary: fn op arm completion preserves outer and retained tokens",
      (Integrated.lookupToken afterFnOp 0).any Integrated.Token.active &&
      (Integrated.lookupToken afterFnOp 2).any Integrated.Token.active),
   ("core boundary: pure stateless fn handler is concurrently shareable",
      concurrentShareableFnHandler pureSources [10] pureFnHandler [captured]),
   ("core boundary: stateful or foreign-reading fn handler rejected across fibers (E0615)",
      !concurrentShareableFnHandler pureSources [10] { pureFnHandler with writes := [external] } [] &&
      !concurrentShareableFnHandler pureSources [10] { pureFnHandler with namedReads := [foreign] } []),
   ("core boundary: parallel boundary rejects effectful fn handler (E0615)",
      !concurrentShareableFnHandler pureSources [] pureFnHandler [captured]),
   ("core boundary: shared fn handler discharges effect without polluting branch writes",
      decide (dischargedBranch.effects = [10, 10] ∧ dischargedBranch.writes = [localOrigin]))]

theorem fixtures_all_pass : fixtures.all Prod.snd = true := by decide +kernel

end RilAccess.CoreBoundary.Examples
