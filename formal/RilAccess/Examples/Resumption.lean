import RilAccess.Effects.Resumption

namespace RilAccess.CoreResumption.Examples
open Integrated

def p (register : Nat) : Path := ⟨register, []⟩
def atom (world : World) (operation : Atom) : World := (checkAtom operation world).toOption.getD world

/-- Build the ledger through the actual checker. The observer depends on the
mutable operation formal; the retained writer has independent lifetime roots. -/
def authority : World :=
  let world := atom initialWorld (.allocate 0 ⟨false, .mut⟩ [])
  let world := atom world (.bind (p 0) 1 ⟨false, .shared⟩)
  let world := atom world (.retain (p 1))
  let world := atom world .enterScope
  let world := atom world (.parameter (p 1) 2 .mutable)
  let world := atom world (.parameter (p 2) 3 .observe)
  let world := atom world .activateParameters
  let world := atom world (.write (p 2))
  atom world (.read (p 3))

def origin : Origin := ⟨⟨.module, 1⟩, 0, 1, 0, 0⟩
def start : State := ⟨[⟨7, ⟨1, 2, 0⟩, 1⟩, ⟨8, ⟨1, 2, 0⟩, 1⟩], ⟨1, 2, 0⟩,
  authority, [⟨.write, origin, .handler⟩], []⟩
def afterFirst := (resume start 7).getD start
def afterOther := (resume afterFirst 8).getD start
def currentLive (world : World) (register : Nat) : Bool := (resolve world (p register)).any live
def currentWrite (world : World) (register : Nat) : Bool := (checkAtom (.write (p register)) world).isOk

def withIndependentRead : World :=
  let world := atom authority (.allocate 9 ⟨false, .immutable⟩ [])
  let world := atom world (.parameter (p 9) 4 .observe)
  atom world .activateParameters
def readState : State := { start with authority := withIndependentRead }
def afterRead := (resume readState 7).getD readState
def missingDependency : State :=
  { start with authority := { authority with permissions := authority.permissions.map (fun permission =>
      if permission.register = 3 then { permission with dependencies := [4] } else permission) } }

def fixtures : List (String × Bool) :=
  [("core resume: actual operation ledger is valid", ledgerValid authority),
   ("core resume: mutable parameter and derived observer initially live", currentLive authority 2 && currentLive authority 3),
   ("core resume: independent writer is suspended during operation", !currentWrite authority 1),
   ("core resume: first use accepted", (resume start 7).isSome),
   ("core resume: alias to consumed identity rejected", (resume afterFirst 7).isNone),
   ("core resume: another operation has independent affine identity", (resume afterFirst 8).isSome),
   ("core resume: intervening operation cannot revive old alias", (resume afterOther 7).isNone),
   ("core resume: actual temporary parameter ends", !currentLive afterFirst.authority 2),
   ("core resume: derived observer lifetime ends", !currentLive afterFirst.authority 3),
   ("core resume: ended dependent loans release independent writer", currentWrite afterFirst.authority 1),
   ("core resume: retained authority survives", (lookupToken afterOther.authority 2).any Token.active),
   ("core resume: outer function authority survives", (lookupToken afterFirst.authority 0).any Token.active),
   ("core resume: historical evidence remains valid without authorizing new access",
      certified afterFirst.authority && !currentLive afterFirst.authority 3),
   ("core resume: independent ref observation survives resumption", currentLive afterRead.authority 4),
   ("core resume: incomplete lifetime dependency metadata rejected", (resume missingDependency 7).isNone),
   ("core resume: operation and dependent loans are inactive",
      afterFirst.authority.loans.all (fun loan => !loan.active)),
   ("core resume: previously committed write survives", decide (afterOther.committed = start.committed)),
   ("core resume: other arm cannot use escaped handle", (resume { start with current := ⟨9, 2, 0⟩ } 7).isNone),
   ("core resume: callable boundary rejects escaped handle", (resume { start with current := ⟨1, 9, 0⟩ } 7).isNone),
   ("core resume: task boundary rejects escaped handle", (resume { start with current := ⟨1, 2, 9⟩ } 7).isNone),
   ("core resume: unavailable identity rejected", (resume start 99).isNone)]

theorem fixtures_all_pass : fixtures.all Prod.snd = true := by decide +kernel

end RilAccess.CoreResumption.Examples
