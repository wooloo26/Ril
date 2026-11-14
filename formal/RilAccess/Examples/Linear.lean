import RilAccess.Access.Linear
import RilAccess.Effects.Resumption

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

namespace RilAccess.Examples.LinearExamples

open Integrated

def p (register : Nat) : Path := ⟨register, []⟩
def fixed (access : Access) : MemberMode := ⟨false, access⟩
def slot (access : Access) : MemberMode := ⟨true, access⟩

def accessCmd (operations : List Atom) : Calls.Syntax :=
  Calls.Syntax.access (operations.foldr (fun op rest => Integrated.Syntax.sequence (.command op) rest) (.command .skip))

def seq (items : List Calls.Syntax) : Calls.Syntax :=
  items.foldr Calls.Syntax.sequence (accessCmd [])

def accepted (program : Calls.Syntax) : Bool := (Calls.check program).isOk

def directConsume : Calls.Syntax :=
  accessCmd [.allocateLinear 0 [], .destructure 0]

def unconsumedTopLevel : Calls.Syntax :=
  accessCmd [.allocateLinear 0 [], .write (p 0)]

def unconsumedInnerBlock : Calls.Syntax :=
  Calls.Syntax.access (.block (.sequence (.command (.allocateLinear 0 [])) (.command (.write (p 0)))))

def chainedMoveConsume : Calls.Syntax :=
  accessCmd [.allocateLinear 0 [], .move 0 1, .move 1 2, .destructure 2]

def doubleConsumeRejected : Calls.Syntax :=
  accessCmd [.allocateLinear 0 [], .destructure 0, .destructure 0]

def useAfterMoveRejected : Calls.Syntax :=
  accessCmd [.allocateLinear 0 [], .move 0 1, .destructure 0, .destructure 1]

def refObserverAllowedThenConsumed : Calls.Syntax :=
  accessCmd [.allocateLinear 0 [], .bind (p 0) 1 (fixed .ref), .read (p 1), .destructure 0]

def refObserverExpiredAfterDestructure : Calls.Syntax :=
  accessCmd [.allocateLinear 0 [], .bind (p 0) 1 (fixed .ref), .destructure 0, .read (p 1)]

def plainLetCopyRejected : Calls.Syntax :=
  accessCmd [.allocateLinear 0 [], .bind (p 0) 1 (fixed .immutable), .destructure 0]

def sharedCopyRejected : Calls.Syntax :=
  accessCmd [.allocateLinear 0 [], .bind (p 0) 1 (fixed .shared), .write (p 1), .destructure 0]

def retainRejected : Calls.Syntax :=
  accessCmd [.allocateLinear 0 [], .retain (p 0), .destructure 0]

def varMutSlotRejected : Calls.Syntax :=
  accessCmd [.allocate 0 (slot .mut) [], .allocateLinear 1 [], .assign (p 1) 0, .write (p 0)]

def branchSymmetricConsume : Calls.Syntax :=
  seq [accessCmd [.allocateLinear 0 []],
    .branch (accessCmd [.destructure 0]) (accessCmd [.move 0 1, .destructure 1])]

def branchAsymmetricLeak : Calls.Syntax :=
  seq [accessCmd [.allocateLinear 0 []],
    .branch (accessCmd [.destructure 0]) (accessCmd [.write (p 0)])]

def callHandoffConsumed : Calls.Syntax :=
  seq [accessCmd [.allocateLinear 0 []],
    .invoke [⟨p 0, 10, .construction, .construction⟩] [] (accessCmd [.destructure 10])]

def callHandoffLeaked : Calls.Syntax :=
  seq [accessCmd [.allocateLinear 0 []],
    .invoke [⟨p 0, 10, .construction, .construction⟩] [] (accessCmd [.write (p 10)])]

def callMutBorrowCallerConsumes : Calls.Syntax :=
  seq [accessCmd [.allocateLinear 0 []],
    .invoke [⟨p 0, 10, .mutable, .mutable⟩] [] (accessCmd [.write (p 10)]),
    accessCmd [.destructure 0]]

def callMutBorrowCalleeCannotConsume : Calls.Syntax :=
  seq [accessCmd [.allocateLinear 0 []],
    .invoke [⟨p 0, 10, .mutable, .mutable⟩] [] (accessCmd [.write (p 10), .destructure 10])]

def callPlainParamRejected : Calls.Syntax :=
  seq [accessCmd [.allocateLinear 0 []],
    .invoke [⟨p 0, 10, .immutable, .immutable⟩] [] (accessCmd [.read (p 10)]),
    accessCmd [.destructure 0]]

def callClosureCaptureRejected : Calls.Syntax :=
  seq [accessCmd [.allocateLinear 0 []],
    .invoke [] [0] (accessCmd [.destructure 0])]

def atomStep (world : World) (op : Atom) : World := (checkAtom op world).toOption.getD world

def innerLinearWorld : World :=
  let w := atomStep initialWorld (.allocateLinear 0 [])
  let w := atomStep w .enterScope
  atomStep w (.allocateLinear 1 [])

def innerLinearConsumedWorld : World :=
  atomStep innerLinearWorld (.destructure 1)

def fixtures : List (String × Bool) :=
  [("linear: direct terminal destructuring satisfies consumption and reachable use", accepted directConsume),
   ("linear: unconsumed top-level linear local rejected (E0721)", !accepted unconsumedTopLevel),
   ("linear: unconsumed block-local linear value rejected at scope exit (E0721)", !accepted unconsumedInnerBlock),
   ("linear: chained new handoff transfers single obligation", accepted chainedMoveConsume),
   ("linear: double terminal destructuring rejected", !accepted doubleConsumeRejected),
   ("linear: consuming moved-from linear source rejected", !accepted useAfterMoveRejected),
   ("linear: live ref observation before consumption accepted", accepted refObserverAllowedThenConsumed),
   ("linear: live ref observer expires upon destructuring", !accepted refObserverExpiredAfterDestructure),
   ("linear: plain immutable binding copy rejected (E0603)", !accepted plainLetCopyRejected),
   ("linear: shared ^mut reception rejected (E0603)", !accepted sharedCopyRejected),
   ("linear: ^mut retention rejected on linear allocation", !accepted retainRejected),
   ("linear: var mut slot assignment rejected (E0603)", !accepted varMutSlotRejected),
   ("linear: branch-symmetric consumption across all paths accepted", accepted branchSymmetricConsume),
   ("linear: branch-asymmetric leak rejected (E0721)", !accepted branchAsymmetricLeak),
   ("linear: new parameter handoff consumed by callee accepted", accepted callHandoffConsumed),
   ("linear: new parameter handoff leaked by callee rejected (E0721)", !accepted callHandoffLeaked),
   ("linear: mut parameter borrow followed by caller consumption accepted", accepted callMutBorrowCallerConsumes),
   ("linear: callee cannot destructure borrowed mut parameter", !accepted callMutBorrowCalleeCannotConsume),
   ("linear: plain immutable parameter rejects linear argument (E0603)", !accepted callPlainParamRejected),
   ("linear: closure environment capture of outer linear local rejected (E0721)", !accepted callClosureCaptureRejected),
   ("linear: active linear local inside delimited scope blocks effect suspension (E0721)",
      !CoreResumption.canSuspendEffect 0 innerLinearWorld && (CoreResumption.abortDelimiter 0 innerLinearWorld).isNone),
   ("linear: consuming inner linear local permits delimiter abort while preserving outer linear obligation",
      CoreResumption.canSuspendEffect 0 innerLinearConsumedWorld &&
      decide (((CoreResumption.abortDelimiter 0 innerLinearConsumedWorld).bind (fun after => lookupToken after 0)).any
        (fun tok => tok.linear && tok.active)))]

theorem fixtures_all_pass : fixtures.all Prod.snd = true := by decide +kernel

end RilAccess.Examples.LinearExamples
