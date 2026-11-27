import RilAccess.Effects.Boundary
import RilAccess.Call.Summary

namespace RilAccess.CoreBoundary.Examples

def localInstance : SourceInstance := ⟨⟨.allocation, 1⟩, 7, 3, 9⟩
def external : SourceInstance := ⟨⟨.module, 17⟩, 0, 1, 0⟩
def captured : SourceInstance := ⟨⟨.capture, 4⟩, 5, 8, 2⟩
def cleanupTarget : SourceInstance := ⟨⟨.capture, 11⟩, 0, 2, 0⟩
def emptySummary : Summary := ⟨[], [], [], [], [], [], []⟩
def emptyRoots : Footprint := ⟨[], [], []⟩

def privateBoundary : Boundary :=
  ⟨{ emptySummary with writes := [localInstance], effects := [3] }, emptySummary, emptySummary,
    ⟨[localInstance], [], []⟩, emptyRoots, emptyRoots, [], []⟩

def handlerEnvironment : Boundary := { privateBoundary with handlerEnvironment := [external] }
def cleanupEnvironment : Boundary := { privateBoundary with cleanupEnvironment := [captured] }
def handlerState : Boundary := { privateBoundary with handler := { emptySummary with writes := [external] } }
def cleanupState : Boundary := { privateBoundary with cleanup := { emptySummary with writes := [cleanupTarget] } }

def handlerEffect : Boundary := { privateBoundary with handler := { emptySummary with effects := [3] } }
def cleanupEffect : Boundary := { privateBoundary with cleanup := { emptySummary with effects := [3] } }
def mixedEffects : Boundary :=
  { privateBoundary with
    body := { emptySummary with effects := [3, 4] },
    handler := { emptySummary with effects := [3, 5] },
    cleanup := { emptySummary with effects := [3, 6] } }
def outerHandler : Boundary := { privateBoundary with body := handled handlerEffect 3 }

def callInstance : CoreSummary.CallInstance := ⟨(fun _ _ => localInstance), [1, 3, 9], 12, 14⟩

def pureSources : List Source := [external.source, captured.source]
def pureBody : Summary := { emptySummary with namedReads := [external] }

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

def examples : List (String × Bool) :=
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
      (fun event => decide (event.kind = .write ∧ event.srcInst = external))),
   ("core boundary: actual cleanup state survives handling and discharge", (outward cleanupState 7 9).any
      (fun event => decide (event.kind = .write ∧ event.srcInst = cleanupTarget))),
   ("core boundary: module identity cannot be rebound by call substitution", decide (CoreSummary.resolve callInstance (.concrete external) = external)),
   ("core boundary: selected capture identity cannot be rebound", decide (CoreSummary.resolve callInstance (.concrete captured) = captured)),
   ("core boundary: cleanup capture identity cannot be rebound", decide (CoreSummary.resolve callInstance (.concrete cleanupTarget) = cleanupTarget)),
   ("core boundary: local allocation cannot impersonate an entry object", decide ((CoreSummary.resolve callInstance (.allocated localInstance.source localInstance.object)).object ∉ callInstance.existingObjects)),
   ("core boundary: local allocation keeps its producer source", decide ((CoreSummary.resolve callInstance (.allocated localInstance.source localInstance.object)).source = localInstance.source)),
   ("core boundary: fn op arm completion revokes call-scoped mut parameter and derived view",
      regLive fnOpAuthority 2 && regLive fnOpAuthority 3 &&
      (completeFnOp fnOpAuthority 1).isSome &&
      !regLive afterFnOp 2 && !regLive afterFnOp 3),
   ("core boundary: fn op arm completion deactivates operation holds and releases outer writer",
      afterFnOp.holds.all (fun hold => !hold.active) &&
      (Integrated.checkAtom (.write ⟨1, []⟩) afterFnOp).isOk),
   ("core boundary: fn op arm completion preserves outer and retained tokens",
      (Integrated.lookupToken afterFnOp 0).any Integrated.Token.active &&
      (Integrated.lookupToken afterFnOp 2).any Integrated.Token.active),
   ("core boundary: handler arm matches fn/ctl prefix (E0623)",
      validHandlerArm .directFn false &&
      validHandlerArm .algebraicCtl true &&
      !validHandlerArm .algebraicCtl false &&
      !validHandlerArm .directFn true),
   ("core boundary: absorb_panic accepts pure body and rejects outer ctl, must-consume, or outward effects (E0608)",
      absorbPanicAdmissible pureSources pureBody [captured] false false &&
      !absorbPanicAdmissible pureSources pureBody [captured] true false &&
      !absorbPanicAdmissible pureSources pureBody [captured] false true &&
      !absorbPanicAdmissible pureSources { pureBody with effects := [3] } [captured] false false &&
      !absorbPanicAdmissible pureSources { pureBody with writes := [external] } [] false false),
   ("core boundary: derive callback rejects outer or unhandled ctl (E0607)",
      deriveCallbackAdmissible false false &&
      !deriveCallbackAdmissible true false &&
      !deriveCallbackAdmissible false true)]

theorem examples_all_pass : examples.all Prod.snd = true := by decide +kernel

end RilAccess.CoreBoundary.Examples
