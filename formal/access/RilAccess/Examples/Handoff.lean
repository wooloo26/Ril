import RilAccess.Access.Handoff

namespace RilAccess.Integrated.HandoffExamples

def p (register : Nat) : Path := ⟨register, []⟩
def atom (world : World) (operation : Atom) : World := (checkAtom operation world).toOption.getD world
def before : World :=
  let world := atom initialWorld (.allocate 0 ⟨false, .mut⟩ [])
  let world := atom world (.allocate 4 ⟨false, .immutable⟩ [])
  atom world (.bind (p 0) 1 ⟨false, .ref⟩)
def after := atom before (.move 0 2)
def currentLive (world : World) (register : Nat) : Bool := (resolve world (p register)).any live

def fixtures : List (String × Bool) :=
  [("handoff: real checked transfer accepted", (checkAtom (.move 0 2) before).isOk),
   ("handoff: complete pointer identity preserved", rawLookup after.raw 2 == rawLookup before.raw 0),
   ("handoff: original source lifetime ends", !currentLive after 0),
   ("handoff: derived observer lifetime ends", !currentLive after 1),
   ("handoff: new construction path is live", currentLive after 2),
   ("handoff: unrelated authority record unchanged", lookupToken after 1 == lookupToken before 1),
   ("handoff: consumed source cannot transfer twice", !(checkAtom (.move 0 3) after).isOk),
   ("handoff: malformed token counter cannot authorize transfer",
      !(checkAtom (.move 0 2) { before with nextToken := 0 }).isOk),
   ("regions: sibling coordinates remain different identities",
      decide ((Pointer.mk 0 [0] ⟨.allocation, 0⟩).regionKey ≠ (Pointer.mk 0 [1] ⟨.allocation, 0⟩).regionKey)),
   ("regions: ancestor overlap is retained", overlaps ⟨0, [], ⟨.allocation, 0⟩⟩ ⟨0, [0], ⟨.allocation, 0⟩⟩)]

theorem fixtures_all_pass : fixtures.all Prod.snd = true := by decide +kernel

end RilAccess.Integrated.HandoffExamples
