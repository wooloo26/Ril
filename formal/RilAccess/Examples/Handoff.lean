import RilAccess.Access.Handoff

namespace RilAccess.Integrated.HandoffExamples

def p (register : Nat) : Path := ⟨register, []⟩
def atom (world : World) (operation : Atom) : World := (checkAtom operation world).toOption.getD world
def before : World :=
  let world := atom initialWorld (.allocate 0 ⟨false, .mut⟩ [])
  let world := atom world (.allocate 4 ⟨false, .immutable⟩ [])
  atom world (.bind (p 0) 1 ⟨false, .ref⟩)
def after := atom before (.handoff 0 2)
def currentLive (world : World) (register : Nat) : Bool := (resolve world (p register)).any live

def receiveCallback (handsOff : Bool) (source destination : Nat) (world : World) :
    Except Error World :=
  if handsOff then checkAtom (.handoff source destination) world else .ok world

def afterCallback := (receiveCallback true 0 2 before).toOption.getD before

def afterIndependentCallbacks :=
  let world := atom before (.allocate 5 ⟨false, .mut⟩ [])
  ((receiveCallback false 0 2 world).bind (receiveCallback true 5 3)).toOption.getD world

def afterTwoHandoffs :=
  ((checkAtom (.handoff 0 2) before).bind (receiveCallback true 2 3)).toOption.getD before

def callbackChecks : List (String × Bool × Bool) :=
  [("consuming_callback_revokes_the_forwarded_argument_in_the_invoker", currentLive afterCallback 0, false),
   ("consuming_callback_revokes_old_views_across_wrappers", currentLive afterCallback 1, false),
   ("callback_handoffs_from_separate_calls_do_not_revoke_a_readers_path",
     currentLive afterIndependentCallbacks 0 && !currentLive afterIndependentCallbacks 5, true),
   ("consuming_callback_may_return_the_new_path", currentLive afterCallback 2, true),
   ("callback_explicit_handoff_result_survives_the_argument_path",
     currentLive afterTwoHandoffs 3 && !currentLive afterTwoHandoffs 0 &&
       !currentLive afterTwoHandoffs 2, true)]

def examples : List (String × Bool) :=
  [("handoff: real checked handoff accepted", (checkAtom (.handoff 0 2) before).isOk),
   ("handoff: complete pointer identity preserved", rawLookup after.raw 2 == rawLookup before.raw 0),
   ("handoff: original source valid scope ends", !currentLive after 0),
   ("handoff: derived view valid scope ends", !currentLive after 1),
   ("handoff: new construction path is live", currentLive after 2),
   ("handoff: unrelated authority record unchanged", lookupToken after 1 == lookupToken before 1),
   ("handoff: ended source cannot hand off twice", !(checkAtom (.handoff 0 3) after).isOk),
   ("handoff: malformed token counter cannot authorize handoff",
      !(checkAtom (.handoff 0 2) { before with nextToken := 0 }).isOk),
   ("regions: sibling coordinates remain different identities",
      decide ((Pointer.mk 0 [0] ⟨.allocation, 0⟩).regionKey ≠ (Pointer.mk 0 [1] ⟨.allocation, 0⟩).regionKey)),
   ("regions: ancestor overlap is retained", overlaps ⟨0, [], ⟨.allocation, 0⟩⟩ ⟨0, [0], ⟨.allocation, 0⟩⟩)] ++
  callbackChecks.map (fun (name, accepted, expected) => (name, accepted == expected))

theorem examples_all_pass : examples.all Prod.snd = true := by decide +kernel

end RilAccess.Integrated.HandoffExamples
