import RilAccess.Call.Summary

namespace RilAccess.CoreSummary.Examples

def saved : Origin := ⟨⟨.allocation, 1⟩, 4, 1, 0, 5⟩
def child : Origin := ⟨⟨.module, 2⟩, 0, 2, 0, 0⟩
def inserted : Origin := ⟨⟨.allocation, 3⟩, 4, 3, 0, 5⟩
def parameterCapture : Origin := ⟨⟨.parameter, 7⟩, 4, 4, 0, 5⟩
def sameObject : Origin := { inserted with object := saved.object }
def heap : List HeapEdge := [⟨saved, 0, child⟩, ⟨child, 0, saved⟩]
def laterHeap : List HeapEdge := ⟨saved, 1, inserted⟩ :: heap
def arguments : List (Nat × List Origin) := [(0, [saved])]
def entries := CoreEntry.capturePrepared heap arguments

def actual : CallInstance :=
  ⟨(fun _ selection => if selection = 0 then saved else if selection = 1 then child else inserted),
    [1, 2, 3, 4], 9, 0, 10⟩

def projected : Template := { rootReturn := [.parameter 0 1] }
def forged : Template := { rootReturn := [.parameter 0 2] }
def captured : Template := { createdEnvironments := [.concrete saved, .concrete parameterCapture] }
def freshReference : Reference := .fresh saved.source 0
def sharedFresh : Template := { rootReturn := [freshReference], contained := [freshReference] }
def distinctFresh : Template := { rootReturn := [freshReference, .fresh inserted.source 1] }
def collision : Template := { rootReturn := [freshReference, .fresh inserted.source 0] }
def allFields : Template :=
  ⟨[.parameter 0 0], [.parameter 0 1], [.parameter 0 1], [.concrete saved],
    [.concrete parameterCapture], [freshReference], [6]⟩

def fixtures : List (String × Bool) :=
  [("core entry: cyclic graph closure includes exactly both entry objects",
      decide ((CoreEntry.capture 0 heap [saved]).origins.length = 2 ∧
        saved ∈ (CoreEntry.capture 0 heap [saved]).origins ∧ child ∈ (CoreEntry.capture 0 heap [saved]).origins)),
   ("core summary: projected child names its original formal", (checkAtEntry actual heap arguments projected).isOk),
   ("core summary: later insertion cannot fabricate frozen entry origin", !(check actual entries forged).isOk),
   ("core summary: snapshot at a later call legitimately includes prior insertion",
      (checkAtEntry actual laterHeap arguments forged).isOk),
   ("core entry: argument preparation finishes before graph capture",
      decide (inserted ∈ (CoreEntry.capture 0 laterHeap [saved]).origins)),
   ("core entry: saved argument remains distinct from a subsequently rebound slot",
      !(checkAtEntry actual heap [(0, [inserted])] projected).isOk),
   ("core summary: allocation-origin and parameter-origin captures are accepted", (check actual entries captured).isOk),
   ("core summary: allocation-origin capture keeps its full identity",
      decide ((instantiate actual captured).createdEnvironments = [saved, parameterCapture])),
   ("core summary: fresh template at a captured allocation site remains fresh",
      decide (resolve actual freshReference ≠ saved)),
   ("core summary: independent fresh templates remain separate", (check actual entries distinctFresh).isOk &&
      decide ((resolve actual freshReference).object ≠ (resolve actual (.fresh inserted.source 1)).object)),
   ("core summary: two templates cannot reuse one allocation serial", !(check actual entries collision).isOk),
   ("core summary: repeated reference preserves an intentional alias", (check actual entries sharedFresh).isOk &&
      decide ((instantiate actual sharedFresh).rootReturn = (instantiate actual sharedFresh).contained)),
   ("core summary: missing formal entry rejected", !(check actual [] projected).isOk),
   ("core summary: duplicate formal entries rejected", !(check actual (entries ++ entries) projected).isOk),
   ("core summary: incomplete old-object coverage rejected",
      !(check { actual with existingObjects := [1] } entries projected).isOk),
   ("core summary: concrete capture absent from old-object coverage rejected",
      !(check actual entries { captured with namedReads := [.concrete { child with object := 77 }] }).isOk),
   ("core summary: reused callee ownership context rejected",
      !(check { actual with activation := 4, scope := 5 } entries projected).isOk),
   ("core summary: fresh reference must describe an allocation source",
      !(check actual entries { rootReturn := [.fresh child.source 0] }).isOk),
   ("core summary: all six state components and effect row compose", (check actual entries allFields).isOk &&
      decide (instantiate actual allFields = ⟨[saved], [child], [child], [saved], [parameterCapture],
        [resolve actual freshReference], [6]⟩)),
   ("core graph: disjoint cyclic region accepted", CoreEntry.separated heap [saved] [inserted]),
   ("core graph: shared descendant defeats separation", !CoreEntry.separated heap [saved] [child]),
   ("core graph: later insertion changes separation", !CoreEntry.separated laterHeap [saved] [inserted]),
   ("core graph: unknown index includes every possible selection",
      !CoreEntry.separated heap [saved, inserted] [inserted]),
   ("core graph: different provenance descriptions cannot hide object alias",
      !CoreEntry.separated heap [saved] [sameObject])]

theorem fixtures_all_pass : fixtures.all Prod.snd = true := by decide +kernel

end RilAccess.CoreSummary.Examples
