import RilAccess.Effects.Boundary
import RilAccess.Call.Summary

namespace RilAccess.CoreBoundary.Examples

def localOrigin : Origin := ⟨⟨.allocation, 1⟩, 7, 3, 0, 9⟩
def external : Origin := ⟨⟨.module, 17⟩, 0, 1, 0, 0⟩
def captured : Origin := ⟨⟨.capture, 4⟩, 5, 8, 0, 2⟩
def foreign : Origin := ⟨⟨.foreign, 11⟩, 0, 2, 0, 0⟩
def emptySummary : Summary := ⟨[], [], [], [], [], [], []⟩
def emptyRoots : Footprint := ⟨[], [], []⟩

def privateBoundary : Boundary :=
  ⟨{ emptySummary with writes := [localOrigin], effects := [3] }, emptySummary, emptySummary,
    ⟨[localOrigin], [], []⟩, emptyRoots, emptyRoots, [], []⟩

def handlerEnvironment : Boundary := { privateBoundary with handlerEnvironment := [external] }
def cleanupEnvironment : Boundary := { privateBoundary with cleanupEnvironment := [captured] }
def handlerState : Boundary := { privateBoundary with handler := { emptySummary with writes := [external] } }
def cleanupState : Boundary := { privateBoundary with cleanup := { emptySummary with writes := [foreign] } }

def callInstance : CoreSummary.CallInstance := ⟨(fun _ _ => localOrigin), [1, 3, 9], 12, 2, 14⟩

def fixtures : List (String × Bool) :=
  [("core boundary: closed local state can discharge", (outward privateBoundary 7 0 9).isEmpty),
   ("core boundary: hidden handler environment blocks discharge", !(outward handlerEnvironment 7 0 9).isEmpty),
   ("core boundary: hidden cleanup environment blocks discharge", !(outward cleanupEnvironment 7 0 9).isEmpty),
   ("core boundary: handling eliminates its effect only", (handled handlerState 3).effects.isEmpty &&
      decide (external ∈ (handled handlerState 3).writes)),
   ("core boundary: actual handler state survives handling and discharge", (outward handlerState 7 0 9).any
      (fun event => decide (event.kind = .write ∧ event.origin = external))),
   ("core boundary: actual cleanup state survives handling and discharge", (outward cleanupState 7 0 9).any
      (fun event => decide (event.kind = .write ∧ event.origin = foreign))),
   ("core boundary: module identity cannot be rebound by call substitution", decide (CoreSummary.resolve callInstance (.concrete external) = external)),
   ("core boundary: selected capture identity cannot be rebound", decide (CoreSummary.resolve callInstance (.concrete captured) = captured)),
   ("core boundary: foreign identity cannot be rebound", decide (CoreSummary.resolve callInstance (.concrete foreign) = foreign)),
   ("core boundary: local allocation cannot impersonate an entry object", decide ((CoreSummary.resolve callInstance (.fresh localOrigin.source localOrigin.object)).object ∉ callInstance.existingObjects)),
   ("core boundary: local allocation keeps its producer source", decide ((CoreSummary.resolve callInstance (.fresh localOrigin.source localOrigin.object)).source = localOrigin.source)),
   ("core boundary: immutable task data without latent authority accepted", taskCrossing ⟨[.immutable], [], false, false, false⟩),
   ("core boundary: live task data rejected", !taskCrossing ⟨[.ref], [], false, false, false⟩),
   ("core boundary: immutable data does not hide latent cross-task state", !taskCrossing ⟨[.immutable], [external], false, false, false⟩)]

theorem fixtures_all_pass : fixtures.all Prod.snd = true := by decide +kernel

end RilAccess.CoreBoundary.Examples
