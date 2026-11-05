import RilAccess.Graph.Authority

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

namespace RilAccess.GraphAuthority.Examples

def fixed (mode : Access) : MemberMode := ⟨false, mode⟩
def variableMode (mode : Access) : MemberMode := ⟨true, mode⟩

def cycle : Graph :=
  ⟨[⟨0, 0, .mut⟩], [⟨0, 0, 1, fixed .mut, .mut⟩, ⟨1, 0, 0, fixed .mut, .mut⟩]⟩

def repeated : Graph :=
  ⟨[⟨0, 0, .mut⟩], [⟨0, 0, 1, fixed .mut, .mut⟩, ⟨0, 1, 1, fixed .mut, .mut⟩]⟩

def readonlySibling : Graph :=
  ⟨[⟨0, 0, .mut⟩], [⟨0, 0, 1, fixed .ref, .mut⟩, ⟨0, 1, 1, fixed .mut, .mut⟩]⟩

def frozenRoot : Graph := { cycle with roots := [⟨0, 0, .immutable⟩] }

def mixedAliases : Graph :=
  ⟨[⟨0, 0, .mut⟩], [⟨0, 0, 1, fixed .immutable, .mut⟩, ⟨0, 1, 1, fixed .mut, .mut⟩]⟩

def liveObserver : Graph :=
  ⟨[⟨0, 0, .ref⟩, ⟨1, 0, .shared⟩], []⟩

def immutableAndWriter : Graph :=
  ⟨[⟨0, 0, .immutable⟩, ⟨1, 0, .shared⟩], []⟩

def mutableSlot : Graph :=
  ⟨[⟨0, 0, .mut⟩, ⟨1, 2, .mut⟩], [⟨0, 0, 1, variableMode .mut, .mut⟩]⟩

def fixedSlot : Graph :=
  ⟨mutableSlot.roots, [⟨0, 0, 1, fixed .mut, .mut⟩]⟩

def referenceSlot : Graph :=
  ⟨mutableSlot.roots, [⟨0, 0, 1, variableMode .ref, .ref⟩]⟩

def checkedShared := checkedReplace mutableSlot 0 [] 0 1 [] true
def checkedRef := checkedReplace referenceSlot 0 [] 0 1 [] false

def fixtures : List (String × Bool) :=
  [("graph: cyclic authority closure", decide (Fact.mk 0 1 .mut ∈ analyze cycle)),
   ("graph: cycle returns to original identity", decide (resolvePath cycle.edges 0 .mut [0, 0] = some (0, .mut))),
   ("graph: repeated paths preserve alias", decide (resolvePath repeated.edges 0 .mut [0] = resolvePath repeated.edges 0 .mut [1])),
   ("graph: readonly sibling cannot borrow another path's writer", !canWritePath readonlySibling 0 [0]),
   ("graph: writable sibling remains writable", canWritePath readonlySibling 0 [1]),
   ("graph: summary records a writer without upgrading readonly path", hasWriter readonlySibling 1),
   ("graph: immutable root suppresses cyclic writes", !hasWriter frozenRoot 1),
   ("graph: mixed immutable/writable aliases rejected", !immutableConsistent mixedAliases),
   ("graph: live ref and writer can coexist", immutableConsistent liveObserver),
   ("graph: plain immutable and writer conflict", !immutableConsistent immutableAndWriter),
   ("graph: writable shared field replacement", checkedShared.isSome),
   ("graph: field replacement does not change declared member mode", decide (checkedShared.map
      (fun graph => (graph.edges.head?).map Edge.member) = some (some (variableMode .mut)))),
   ("graph: fixed object field cannot be replaced", !(checkedReplace fixedSlot 0 [] 0 1 [] true).isSome),
   ("graph: retained storage requires acknowledgment", !(checkedReplace mutableSlot 0 [] 0 1 [] false).isSome),
   ("graph: readonly stored reference remains readonly", decide (checkedRef.map
      (fun graph => canWritePath graph 0 [0]) = some false)),
   ("graph: shared marker cannot be idle at readonly reception", !(checkedReplace referenceSlot 0 [] 0 1 [] true).isSome),
   ("graph: post-entry edge cannot fabricate old entry origin", decide (2 ∉ entryObjects mutableSlot 0)),
   ("graph: current reachability includes newly stored object", decide (checkedShared.map
      (fun graph => decide (2 ∈ entryObjects graph 0)) = some true))]

theorem fixtures_all_pass : fixtures.all Prod.snd = true := by decide +kernel

theorem erased_cycle : RawPath (eraseEdges cycle.edges) 0 [0, 0] 0 := by
  exact path_erases (resolve_path_sound (by decide +kernel :
    resolvePath cycle.edges 0 .mut [0, 0] = some (0, .mut)))

end RilAccess.GraphAuthority.Examples
