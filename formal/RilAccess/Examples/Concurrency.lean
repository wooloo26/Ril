import RilAccess.Effects.Concurrency

namespace RilAccess.CoreConcurrency.Examples
open Integrated

def p (register : Nat) : Path := ⟨register, []⟩
def atom (world : World) (operation : Atom) : World := (checkAtom operation world).toOption.getD world

def baseWorld : World :=
  let world := atom initialWorld .enterScope
  let world := atom world (.allocate 0 ⟨false, .immutable⟩ [⟨[0], ⟨false, .immutable⟩, true⟩])
  let world := atom world (.allocate 1 ⟨false, .mut⟩ [⟨[0], ⟨false, .mut⟩, true⟩])
  let world := atom world (.allocate 2 ⟨false, .mut⟩ [⟨[0], ⟨false, .mut⟩, true⟩])
  let world := atom world (.bind (p 2) 5 ⟨true, .shared⟩)
  let world := atom world (.allocateResource 3 [])
  let world := atom world (.allocateScoped 4 true [])
  let world := atom world (.bind (p 0) 6 ⟨false, .ref⟩)
  let world := atom world (.allocate 7 ⟨true, .immutable⟩ [])
  let world := atom world (.allocate 8 ⟨false, .mut⟩
    [⟨[0], ⟨false, .mut⟩, true⟩, ⟨[0, 0], ⟨false, .ref⟩, true⟩])
  atom world (.allocate 9 ⟨false, .mut⟩ [⟨[0], ⟨false, .shared⟩, true⟩])

def afterShared : World := (spawnSharedCapture baseWorld (p 0) 10).toOption.getD baseWorld
def afterHandoff : World := (spawnHandoffCapture baseWorld 1 11).toOption.getD baseWorld

def taskScope : ScopeState :=
  ⟨7,
   [{ id := 1, regionSigma := 7, mode := .sharedImmutable },
    { id := 2, regionSigma := 7, mode := .exclusiveSingleShot },
    { id := 3, regionSigma := 7, mode := .exclusiveSingleShot, fallibleResult := true }]⟩

def afterPlainJoin : ScopeState := (joinTask taskScope 1 7 false).getD taskScope
def afterExclusiveJoin : ScopeState := (joinTask taskScope 2 7 true).getD taskScope
def afterFallibleJoined : ScopeState := (joinTask taskScope 3 7 true).getD taskScope

def memoizedFallible : ScopeState :=
  ⟨7, [{ id := 1, regionSigma := 7, mode := .sharedImmutable, fallibleResult := true }]⟩

def memoizedJoinLoop (inspectEach : Bool) : Bool :=
  let join (state : ScopeState) := joinTask state 1 7 false
  let inspect (state : ScopeState) := inspectJoinedResult state 1 7
  let ready := (join memoizedFallible).bind inspect
  let first := ready.bind join
  let next := if inspectEach then first.bind inspect else first
  ((next.bind join).bind inspect |>.bind drainPlainTasks).isSome

def examples : List (String × Bool) :=
  [("concurrency: base ledger with immutable, mut, shared, resource, and scoped bindings is valid",
      ledgerValid baseWorld),
   ("concurrency: deeply immutable binding accepted for cross-fiber shared capture",
      (resolve baseWorld (p 0)).any (eligibleSharedCapture baseWorld)),
   ("concurrency: shared mutable, resource, and scoped bindings rejected by shared capture (E0601)",
      !(resolve baseWorld (p 5)).any (eligibleSharedCapture baseWorld) &&
      !(resolve baseWorld (p 3)).any (eligibleSharedCapture baseWorld) &&
      !(resolve baseWorld (p 4)).any (eligibleSharedCapture baseWorld)),
   ("concurrency: shared capture binds read-only view and forbids child writes",
      (spawnSharedCapture baseWorld (p 0) 10).isOk &&
      (checkAtom (.read (p 10)) afterShared).isOk &&
      !(checkAtom (.write (p 10)) afterShared).isOk),
   ("concurrency: shared capture rejects ref and var bindings of immutable objects (E0601)",
      (resolve baseWorld (p 6)).any deepImmutable &&
      (resolve baseWorld (p 7)).any deepImmutable &&
      !(spawnSharedCapture baseWorld (p 6) 10).isOk &&
      !(spawnSharedCapture baseWorld (p 7) 10).isOk),
   ("concurrency: single-shot move transfers exclusive binding and ends parent path (E0549)",
      (spawnHandoffCapture baseWorld 1 11).isOk &&
      !(resolve afterHandoff (p 1)).any live &&
      (resolve afterHandoff (p 11)).any live &&
      !(spawnHandoffCapture afterHandoff 1 12).isOk),
   ("concurrency: single-shot moves across fibers reject foreign and scoped resources",
      (checkAtom (.handoff 3 13) baseWorld).isOk &&
      !(spawnHandoffCapture baseWorld 3 13).isOk &&
      !(spawnHandoffCapture baseWorld 4 14).isOk),
   ("concurrency: transfer rejects foreign handles and data containing ref or shared members",
      !(resolve baseWorld (p 3)).any (eligibleChannelSend true baseWorld) &&
      !(resolve baseWorld (p 8)).any (eligibleChannelSend true baseWorld) &&
      !(resolve baseWorld (p 9)).any (eligibleChannelSend true baseWorld) &&
      !(spawnHandoffCapture baseWorld 8 10).isOk &&
      !(spawnHandoffCapture baseWorld 9 10).isOk),
   ("concurrency: channel send rejects frozen immutable object for writable schema (E0548)",
      !(resolve baseWorld (p 0)).any (eligibleChannelSend true baseWorld) &&
      (resolve baseWorld (p 1)).any (eligibleChannelSend true baseWorld) &&
      (resolve baseWorld (p 0)).any (eligibleChannelSend false baseWorld)),
   ("concurrency: cross-scope task join and cancel rejected (E0604)",
      (joinTask taskScope 1 99 false).isNone && (cancelTask taskScope 2 99).isNone),
   ("concurrency: plain let task supports idempotent memoized join",
      (joinTask taskScope 1 7 false).isSome && (joinTask afterPlainJoin 1 7 false).isSome),
   ("concurrency: exclusive task handle rejects duplicate join or cancel (E0549)",
      (joinTask taskScope 2 7 true).isSome &&
      (joinTask afterExclusiveJoin 2 7 true).isNone &&
      (cancelTask afterExclusiveJoin 2 7).isNone),
   ("concurrency: cancel settles exclusive task handle",
      (cancelTask taskScope 2 7).isSome && (cancelTask taskScope 3 7).isSome),
   ("concurrency: uninspected Result blocks scope exit even after join (E0720)",
      (inspectJoinedResult taskScope 3 7).isNone &&
      (drainPlainTasks taskScope).isNone &&
      (joinTask taskScope 3 7 true).isSome &&
      (drainPlainTasks afterFallibleJoined).isNone &&
      (inspectJoinedResult afterFallibleJoined 3 99).isNone),
   ("concurrency: inspecting the joined Result or cancelling enables the normal-exit drain",
      ((inspectJoinedResult afterFallibleJoined 3 7).bind drainPlainTasks).any canExitScope &&
      ((cancelTask taskScope 3 7).bind drainPlainTasks).any canExitScope),
   ("concurrency: each memoized join returning a Result requires inspection",
      let twice := (joinTask memoizedFallible 1 7 false).bind fun once => joinTask once 1 7 false
      match twice.bind (inspectJoinedResult · 1 7) with
      | none => false
      | some inspectedOnce =>
        !canExitScope inspectedOnce &&
          (drainPlainTasks inspectedOnce).isNone &&
          (inspectJoinedResult inspectedOnce 1 7).any canExitScope),
   ("concurrency: a loop cannot discard an earlier join Result", !memoizedJoinLoop false),
   ("concurrency: a loop can inspect each join Result before replacement", memoizedJoinLoop true)]

theorem examples_all_pass : examples.all Prod.snd = true := by decide +kernel

end RilAccess.CoreConcurrency.Examples
