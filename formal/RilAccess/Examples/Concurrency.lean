import RilAccess.Effects.Concurrency

namespace RilAccess.CoreConcurrency.Examples
open Integrated

def p (register : Nat) : Path := ⟨register, []⟩
def atom (world : World) (operation : Atom) : World := (checkAtom operation world).toOption.getD world

def baseWorld : World :=
  let world := atom initialWorld .enterScope
  let world := atom world (.allocate 0 ⟨false, .immutable⟩ [⟨[0], ⟨false, .immutable⟩, true⟩])
  let world := atom world (.allocate 1 ⟨false, .mut⟩ [⟨[0], ⟨false, .mut⟩, true⟩])
  let world := atom world (.allocate 2 ⟨true, .shared⟩ [⟨[0], ⟨false, .mut⟩, true⟩])
  atom world (.allocateLinear 3 [])

def afterShared : World := (spawnSharedCapture baseWorld (p 0) 10).toOption.getD baseWorld
def afterMove : World := (spawnMoveCapture baseWorld 1 11).toOption.getD baseWorld
def afterLinearMove : World := (spawnMoveCapture baseWorld 3 13).toOption.getD baseWorld

def nursery : NurseryState :=
  ⟨7,
   [⟨1, 7, .sharedImmutable, false, false, false, false⟩,
    ⟨2, 7, .exclusiveSingleShot, false, false, false, false⟩,
    ⟨3, 7, .exclusiveSingleShot, true, false, false, false⟩,
    ⟨4, 7, .sharedImmutable, false, true, false, false⟩]⟩

def afterPlainJoin : NurseryState := (joinTask nursery 1 7 false).getD nursery
def afterExclusiveJoin : NurseryState := (joinTask nursery 2 7 true).getD nursery
def afterMandatoryJoined : NurseryState :=
  let n := (joinTask nursery 3 7 true).getD nursery
  (joinTask n 4 7 false).getD n

def fixtures : List (String × Bool) :=
  [("concurrency: base ledger with immutable, mut, shared, and linear bindings is valid",
      ledgerValid baseWorld),
   ("concurrency: deeply immutable binding accepted for cross-fiber shared capture",
      (resolve baseWorld (p 0)).any (eligibleSharedCapture baseWorld)),
   ("concurrency: shared mutable and linear bindings rejected by shared capture (E0601)",
      !(resolve baseWorld (p 2)).any (eligibleSharedCapture baseWorld) &&
      !(resolve baseWorld (p 3)).any (eligibleSharedCapture baseWorld)),
   ("concurrency: shared capture binds read-only view and forbids child writes",
      (spawnSharedCapture baseWorld (p 0) 10).isOk &&
      (checkAtom (.read (p 10)) afterShared).isOk &&
      !(checkAtom (.write (p 10)) afterShared).isOk),
   ("concurrency: single-shot move transfers exclusive binding and ends parent path (E0549)",
      (spawnMoveCapture baseWorld 1 11).isOk &&
      !(resolve afterMove (p 1)).any live &&
      (resolve afterMove (p 11)).any live &&
      !(spawnMoveCapture afterMove 1 12).isOk),
   ("concurrency: single-shot move transfers linear obligation to child fiber",
      (spawnMoveCapture baseWorld 3 13).isOk &&
      !(resolve afterLinearMove (p 3)).any live &&
      (resolve afterLinearMove (p 13)).any live),
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
   ("concurrency: cancel accepted on non-linear exclusive task and rejected on linear task",
      (cancelTask nursery 2 7).isSome && (cancelTask nursery 3 7).isNone),
   ("concurrency: unjoined linear or Result task blocks scope exit (E0721 / E0720)",
      !canExitScope nursery && (drainPlainTasks nursery).isNone &&
      (drainPlainTasks ((joinTask nursery 3 7 true).getD nursery)).isNone),
   ("concurrency: joining linear and Result tasks enables automatic plain-task nursery drain",
      (drainPlainTasks afterMandatoryJoined).any canExitScope),
   ("concurrency: unshielded async suspension blocked by active inner linear while uncancellable permits (E0721)",
      !canSuspendAsync false 0 baseWorld && canSuspendAsync true 0 baseWorld)]

theorem fixtures_all_pass : fixtures.all Prod.snd = true := by decide +kernel

end RilAccess.CoreConcurrency.Examples
