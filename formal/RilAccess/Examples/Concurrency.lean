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
  atom world (.allocateScoped 4 true [])

def afterShared : World := (spawnSharedCapture baseWorld (p 0) 10).toOption.getD baseWorld
def afterMove : World := (spawnMoveCapture baseWorld 1 11).toOption.getD baseWorld
def afterResourceMove : World := (spawnMoveCapture baseWorld 3 13).toOption.getD baseWorld

def nursery : NurseryState :=
  ⟨7,
   [⟨1, 7, .sharedImmutable, false, false, false⟩,
    ⟨2, 7, .exclusiveSingleShot, false, false, false⟩,
    ⟨3, 7, .exclusiveSingleShot, true, false, false⟩]⟩

def afterPlainJoin : NurseryState := (joinTask nursery 1 7 false).getD nursery
def afterExclusiveJoin : NurseryState := (joinTask nursery 2 7 true).getD nursery
def afterFallibleJoined : NurseryState := (joinTask nursery 3 7 true).getD nursery

def fixtures : List (String × Bool) :=
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
   ("concurrency: single-shot move transfers exclusive binding and ends parent path (E0549)",
      (spawnMoveCapture baseWorld 1 11).isOk &&
      !(resolve afterMove (p 1)).any live &&
      (resolve afterMove (p 11)).any live &&
      !(spawnMoveCapture afterMove 1 12).isOk),
   ("concurrency: single-shot move transfers foreign resource handle and rejects scoped binding (E0604)",
      (spawnMoveCapture baseWorld 3 13).isOk &&
      !(resolve afterResourceMove (p 3)).any live &&
      (resolve afterResourceMove (p 13)).any live &&
      !(spawnMoveCapture baseWorld 4 14).isOk),
   ("concurrency: channel send rejects frozen immutable object for writable schema (E0548)",
      !(resolve baseWorld (p 0)).any (eligibleChannelSend true baseWorld) &&
      (resolve baseWorld (p 1)).any (eligibleChannelSend true baseWorld) &&
      (resolve baseWorld (p 0)).any (eligibleChannelSend false baseWorld)),
   ("concurrency: cross-scope task join and cancel rejected (E0604)",
      (joinTask nursery 1 99 false).isNone && (cancelTask nursery 2 99).isNone),
   ("concurrency: plain let task supports idempotent memoized join",
      (joinTask nursery 1 7 false).isSome && (joinTask afterPlainJoin 1 7 false).isSome),
   ("concurrency: exclusive task handle rejects duplicate join or cancel (E0549)",
      (joinTask nursery 2 7 true).isSome &&
      (joinTask afterExclusiveJoin 2 7 true).isNone &&
      (cancelTask afterExclusiveJoin 2 7).isNone),
   ("concurrency: cancel settles exclusive task handle",
      (cancelTask nursery 2 7).isSome && (cancelTask nursery 3 7).isSome),
   ("concurrency: uninspected Result task blocks scope exit (E0720)",
      !canExitScope nursery && (drainPlainTasks nursery).isNone),
   ("concurrency: settling Result task enables automatic plain-task nursery drain",
      (drainPlainTasks afterFallibleJoined).any canExitScope)]

theorem fixtures_all_pass : fixtures.all Prod.snd = true := by decide +kernel

end RilAccess.CoreConcurrency.Examples
