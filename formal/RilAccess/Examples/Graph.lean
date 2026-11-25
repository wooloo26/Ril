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
  ⟨[⟨0, 0, .mut⟩], [⟨0, 0, 1, fixed .ref, .ref⟩, ⟨0, 1, 1, fixed .mut, .mut⟩]⟩

def frozenRoot : Graph := { cycle with roots := [⟨0, 0, .immutable⟩] }

def mixedAliases : Graph :=
  ⟨[⟨0, 0, .mut⟩], [⟨0, 0, 1, fixed .immutable, .mut⟩, ⟨0, 1, 1, fixed .mut, .mut⟩]⟩

def liveObserver : Graph :=
  ⟨[⟨0, 0, .ref⟩, ⟨1, 0, .shared⟩], []⟩

def immutableAndWriter : Graph :=
  ⟨[⟨0, 0, .immutable⟩, ⟨1, 0, .shared⟩], []⟩

def mutableSlot : Graph :=
  ⟨[⟨0, 0, .mut⟩, ⟨1, 2, .mut⟩], [⟨0, 0, 1, variableMode .mut, .mut⟩]⟩

def sharedSlot : Graph :=
  ⟨mutableSlot.roots, [⟨0, 0, 1, variableMode .shared, .shared⟩]⟩

def fixedSlot : Graph :=
  ⟨sharedSlot.roots, [⟨0, 0, 1, fixed .shared, .shared⟩]⟩

def referenceSlot : Graph :=
  ⟨mutableSlot.roots ++ [⟨2, 2, .ref⟩], [⟨0, 0, 1, variableMode .ref, .ref⟩]⟩

def checkedShared := checkedReplace sharedSlot 0 [] 0 1 [] true
def checkedRef := checkedReplace referenceSlot 0 [] 0 2 [] false

/-- The outer nodes represent assembled wrappers around existing source objects.
These examples check path authority and identity, not construction reception or
the separate scope conditions of stored sources. -/
def nestedSources : Graph :=
  ⟨[⟨0, 0, .mut⟩, ⟨1, 3, .shared⟩, ⟨2, 3, .ref⟩, ⟨3, 4, .immutable⟩],
   [⟨0, 0, 1, fixed .mut, .mut⟩,
    ⟨1, 0, 2, fixed .mut, .mut⟩,
    ⟨2, 0, 5, variableMode .shared, .shared⟩,
    ⟨2, 1, 3, fixed .shared, .shared⟩,
    ⟨2, 2, 3, fixed .ref, .ref⟩,
    ⟨2, 3, 4, fixed .immutable, .immutable⟩]⟩

def nestedSharedStored := checkedReplace nestedSources 0 [0, 0] 0 1 [] true

def frozenNestedSources : Graph :=
  { nestedSources with
    roots := nestedSources.roots.map fun root =>
      if root.view = 0 then { root with access := .immutable } else root }

def frozenSelected : Graph :=
  ⟨[⟨0, 1, .immutable⟩, ⟨1, 2, .shared⟩],
   [⟨0, 0, 1, fixed .mut, .mut⟩, ⟨0, 1, 2, fixed .shared, .shared⟩]⟩

def handedOffBeforeStore : Graph :=
  ⟨[⟨0, 0, .immutable⟩, ⟨1, 2, .shared⟩], [⟨0, 0, 2, variableMode .shared, .shared⟩]⟩

def handedOffAfterStore : Graph :=
  { handedOffBeforeStore with edges := [⟨0, 0, 3, variableMode .shared, .shared⟩] }

def examples : List (String × Bool) :=
  [("graph: cyclic authority closure", decide (Fact.mk 0 1 .mut ∈ analyze cycle)),
   ("graph: cycle returns to original identity", decide (resolvePath cycle.edges 0 .mut [0, 0] = some (0, .mut))),
   ("graph: repeated paths preserve alias", decide (resolvePath repeated.edges 0 .mut [0] = resolvePath repeated.edges 0 .mut [1])),
   ("graph: readonly sibling cannot acquire another path's writer", !canWritePath readonlySibling 0 [0]),
   ("graph: writable sibling remains writable", canWritePath readonlySibling 0 [1]),
   ("graph: summary records a writer without upgrading readonly path", hasWriter readonlySibling 1),
   ("graph: immutable root suppresses cyclic writes", !hasWriter frozenRoot 1),
   ("graph: mixed immutable/writable aliases rejected", !immutableConsistent mixedAliases),
   ("graph: live ref and writer can coexist", immutableConsistent liveObserver),
   ("graph: plain immutable and writer conflict", !immutableConsistent immutableAndWriter),
   ("graph: writable shared field replacement", checkedShared.isSome),
   ("graph: field replacement does not change declared member mode", decide (checkedShared.map
      (fun graph => (graph.edges.head?).map Edge.member) = some (some (variableMode .shared)))),
   ("graph: fixed object field cannot be replaced", !(checkedReplace fixedSlot 0 [] 0 1 [] true).isSome),
   ("graph: retained storage requires acknowledgment", !(checkedReplace sharedSlot 0 [] 0 1 [] false).isSome),
   ("graph: shared reception requires shared storage rather than mut storage",
      (receiveStored .mut .shared true).isNone &&
      (receiveStored .mut .mut true).isNone &&
      !(checkedReplace mutableSlot 0 [] 0 1 [] true).isSome),
   ("graph: readonly stored reference remains readonly", decide (checkedRef.map
      (fun graph => canWritePath graph 0 [0]) = some false)),
   ("graph: reference storage rejects implicit mode conversion",
      (receiveStored .ref .mut false).isNone &&
      (receiveStored .ref .shared false).isNone &&
      (receiveStored .ref .immutable false).isNone &&
      !(checkedReplace referenceSlot 0 [] 0 1 [] false).isSome),
   ("graph: shared marker cannot be idle at readonly reception", !(checkedReplace referenceSlot 0 [] 0 1 [] true).isSome),
   ("graph: post-entry edge cannot fabricate old entry origin", decide (2 ∉ entryObjects mutableSlot 0)),
   ("graph: current reachability includes newly stored object", decide (checkedShared.map
      (fun graph => decide (2 ∈ entryObjects graph 0)) = some true)),
   ("graph: nested wrappers remain writable above existing source boundaries",
      canWritePath nestedSources 0 [] && canWritePath nestedSources 0 [0] &&
      canWritePath nestedSources 0 [0, 0] && immutableConsistent nestedSources),
   ("graph: nested shared member preserves shared mode and outside object identity",
      decide (resolveView nestedSources 0 [0, 0, 1] = some (3, .shared)) &&
      decide (resolveView nestedSources 1 [] = some (3, .shared))),
   ("graph: outer writers cannot upgrade a nested ref to the same shared object",
      decide (resolveView nestedSources 0 [0, 0, 2] = some (3, .ref)) &&
      decide (resolveView nestedSources 2 [] = some (3, .ref)) &&
      hasWriter nestedSources 3 && !canWritePath nestedSources 0 [0, 0, 2]),
   ("graph: outer writers cannot upgrade a nested immutable source",
      decide (resolveView nestedSources 0 [0, 0, 3] = some (4, .immutable)) &&
      decide (resolveView nestedSources 3 [] = some (4, .immutable)) &&
      !canWritePath nestedSources 0 [0, 0, 3]),
   ("graph: explicit shared reception matches shared storage exactly",
      decide (receiveStored .shared .shared true = some .shared) &&
      decide (nestedSharedStored.map (fun graph => resolveView graph 0 [0, 0, 0]) =
        some (some (3, .shared)))),
   ("graph: nested shared reception preserves declared replaceable shared schema",
      decide (nestedSharedStored.map (fun graph =>
        (graph.edges.find? fun edge => decide (edge.parent = 2 ∧ edge.field = 0)).map
          Edge.member) = some (some (variableMode .shared)))),
   ("graph: nested storage cannot omit shared acknowledgment or upgrade readonly sources",
      !(checkedReplace nestedSources 0 [0, 0] 0 1 [] false).isSome &&
      !(checkedReplace nestedSources 0 [0, 0] 0 2 [] true).isSome &&
      !(checkedReplace nestedSources 0 [0, 0] 0 3 [] true).isSome),
   ("graph: two nested element paths retain their alias after shared storage",
      decide (nestedSharedStored.map (fun graph =>
        decide (resolveView graph 0 [0, 0, 0] = some (3, .shared) ∧
          resolveView graph 0 [0, 0, 1] = some (3, .shared))) = some true)),
   ("graph: freezing the outer root cannot coexist with an outside nested writer",
      !canWritePath frozenNestedSources 0 [0, 0, 1] &&
      hasWriter frozenNestedSources 3 && !immutableConsistent frozenNestedSources),
   ("graph: freezing a selected child preserves a writer to its sibling",
      immutableConsistent frozenSelected && hasWriter frozenSelected 2),
   ("graph: freezing after replacement no longer reaches the previous writer",
      !immutableConsistent handedOffBeforeStore && immutableConsistent handedOffAfterStore &&
      hasWriter handedOffAfterStore 2)]

theorem examples_all_pass : examples.all Prod.snd = true := by decide +kernel

theorem erased_cycle : RawPath (eraseEdges cycle.edges) 0 [0, 0] 0 := by
  exact path_erases (resolve_path_sound (by decide +kernel :
    resolvePath cycle.edges 0 .mut [0, 0] = some (0, .mut)))

end RilAccess.GraphAuthority.Examples
