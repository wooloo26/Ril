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
def emptyFrozen : CoreEntry.Frozen := ⟨[], [], by decide⟩
def freeze (sourceHeap : List HeapEdge) (args : List (Nat × List Origin)) : CoreEntry.Frozen :=
  (CoreEntry.capturePrepared sourceHeap args).toOption.getD emptyFrozen

def capturedOrigins (sourceHeap : List HeapEdge) (roots : List Origin) : List Origin :=
  (((freeze sourceHeap [(0, roots)]).snapshots.head?).map CoreEntry.Snapshot.origins).getD []

def entries := freeze heap arguments
def parentAlias : Origin := { saved with source := ⟨.capture, 98⟩ }
def conflictingOwner : Origin := { parentAlias with activation := 99 }

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
      decide ((capturedOrigins heap [saved]).length = 2 ∧
        saved ∈ capturedOrigins heap [saved] ∧ child ∈ capturedOrigins heap [saved])),
   ("core summary: projected child names its original formal", (checkAtEntry actual heap arguments projected).isOk),
   ("core summary: later insertion cannot fabricate frozen entry origin", !(check actual entries forged).isOk),
   ("core summary: snapshot at a later call legitimately includes prior insertion",
      (checkAtEntry actual laterHeap arguments forged).isOk),
   ("core entry: argument preparation finishes before graph capture",
      decide (inserted ∈ capturedOrigins laterHeap [saved])),
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
   ("core summary: missing formal entry rejected", !(check actual (freeze heap []) projected).isOk),
   ("core summary: duplicate formal entries rejected", !(check actual (freeze heap (arguments ++ arguments)) projected).isOk),
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
   ("identity: source labels cannot hide a child alias", !CoreEntry.separated heap [child] [parentAlias]),
   ("identity: aliased parent traversal retains child", decide (child ∈ capturedOrigins heap [parentAlias])),
   ("identity: every source explanation survives normalization", decide
      (saved ∈ capturedOrigins heap [parentAlias] ∧ parentAlias ∈ capturedOrigins heap [parentAlias])),
   ("identity: aliased formal still has physical entry origins",
      (checkAtEntry actual heap [(0, [parentAlias])] projected).isOk),
   ("identity: conflicting ownership fails entry validation",
      !(CoreEntry.capturePrepared heap [(0, [conflictingOwner])]).isOk),
   ("identity: conflicting ownership cannot prove separation",
      !CoreEntry.separated heap [inserted] [conflictingOwner]),
   ("core graph: different provenance descriptions cannot hide object alias",
      !CoreEntry.separated heap [saved] [sameObject])]

theorem fixtures_all_pass : fixtures.all Prod.snd = true := by decide +kernel

end RilAccess.CoreSummary.Examples
