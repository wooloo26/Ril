import RilAccess.Access.Scoped
import RilAccess.Call.Proofs

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

namespace RilAccess.Examples.ScopedExamples

open Integrated

def p (register : Nat) : Path := ⟨register, []⟩
def fixed (access : Access) : MemberMode := ⟨false, access⟩
def slot (access : Access) : MemberMode := ⟨true, access⟩

def accessCmd (operations : List Atom) : Calls.Syntax :=
  Calls.Syntax.access (operations.foldr (fun op rest => Integrated.Syntax.sequence (.command op) rest) (.command .skip))

def seq (items : List Calls.Syntax) : Calls.Syntax :=
  items.foldr Calls.Syntax.sequence (accessCmd [])

def accepted (program : Calls.Syntax) : Bool := (Calls.check program).isOk

-- Foreign `.d.ril` `opaque type` affine handle fixtures:
def resourceImplicitDropOk : Calls.Syntax :=
  Calls.Syntax.access (.block (.sequence (.command (.allocateResource 0 [])) (.command (.write (p 0)))))

def resourceChainedHandoff : Calls.Syntax :=
  accessCmd [.allocateResource 0 [], .move 0 1, .move 1 2, .write (p 2)]

def resourceUseAfterMoveRejected : Calls.Syntax :=
  accessCmd [.allocateResource 0 [], .move 0 1, .write (p 0)]

def resourcePlainSnapshotRejected : Calls.Syntax :=
  accessCmd [.allocateResource 0 [], .bind (p 0) 1 (fixed .immutable)]

def resourceSharedCopyRejected : Calls.Syntax :=
  accessCmd [.allocateResource 0 [], .bind (p 0) 1 (fixed .shared), .write (p 1)]

def resourceRetainRejected : Calls.Syntax :=
  accessCmd [.allocateResource 0 [], .retain (p 0)]

def resourceVarMutOverwriteRejected : Calls.Syntax :=
  accessCmd [.allocate 0 (slot .mut) [], .allocateResource 1 [], .assign (p 1) 0]

def resourceCallBorrowAndConsume : Calls.Syntax :=
  seq [accessCmd [.allocateResource 0 []],
    .invoke [⟨p 0, 10, .mutable, .mutable⟩] [] (accessCmd [.write (p 10)]),
    .invoke [⟨p 0, 11, .construction, .construction⟩] [] (accessCmd [.write (p 11)])]

def resourceClosureCaptureRejected : Calls.Syntax :=
  seq [accessCmd [.allocateResource 0 []],
    .invoke [] [0] (accessCmd [.write (p 0)])]

-- `use` / `use mut` (`use(<fn>)` cleanup contract) fixtures:
def scopedReadOnlyResourceObserveOk : Calls.Syntax :=
  seq [accessCmd [.allocateScoped 0 false [] true],
    .invoke [⟨p 0, 10, .observe, .observe⟩] [] (accessCmd [.read (p 10)])]

def scopedReadOnlyUnusedOk : Calls.Syntax :=
  Calls.Syntax.access (.block (.command (.allocateScoped 0 false [] true)))

def scopedMutBlockUseAndBorrow : Calls.Syntax :=
  Calls.Syntax.access (.block
    (Integrated.Syntax.sequence (.command (.allocateScoped 0 true []))
      (.borrow (p 0) 1 (.command (.write (p 1))))))

def scopedCallRefAndMutBorrows : Calls.Syntax :=
  seq [accessCmd [.allocateScoped 0 true []],
    .invoke [⟨p 0, 10, .observe, .observe⟩] [] (accessCmd [.read (p 10)]),
    .invoke [⟨p 0, 11, .mutable, .mutable⟩] [] (accessCmd [.write (p 11)])]

def scopedReadOnlyRejectsWrite : Calls.Syntax :=
  accessCmd [.allocateScoped 0 false [], .write (p 0)]

def scopedReassignRejected : Calls.Syntax :=
  accessCmd [.allocateScoped 0 true [], .allocate 1 (fixed .mut) [], .assign (p 1) 0]

def scopedMoveEscapeRejected : Calls.Syntax :=
  accessCmd [.allocateScoped 0 false [], .move 0 1]

def scopedRebindEscapeRejected : Calls.Syntax :=
  accessCmd [.allocateScoped 0 false [], .bind (p 0) 1 (fixed .ref)]

def scopedRetainEscapeRejected : Calls.Syntax :=
  accessCmd [.allocateScoped 0 true [], .retain (p 0)]

def scopedCallNewHandoffRejected : Calls.Syntax :=
  seq [accessCmd [.allocateScoped 0 false []],
    .invoke [⟨p 0, 10, .construction, .construction⟩] [] (accessCmd [.write (p 10)])]

def scopedClosureCaptureRejected : Calls.Syntax :=
  seq [accessCmd [.allocateScoped 0 false []],
    .invoke [] [0] (accessCmd [.read (p 0)])]

def scopedExpiredAfterBlockExit : Calls.Syntax :=
  Calls.Syntax.access (.sequence
    (.block (.sequence (.command (.allocateScoped 0 true [])) (.command (.write (p 0)))))
    (.command (.read (p 0))))

def scopedIdleMutRejected : Calls.Syntax :=
  Calls.Syntax.access (.block (.sequence (.command (.allocateScoped 0 true [])) (.command (.read (p 0)))))

def scopedBodyMutAccepted : Calls.Syntax :=
  Calls.Syntax.access (.block (.sequence (.command (.allocateScoped 0 true [])) (.command (.write (p 0)))))

def fixtures : List (String × Bool) :=
  [("resource: affine handle permits scope exit without mandatory E0721 consumption", accepted resourceImplicitDropOk),
   ("resource: chained new handoff transfers exclusive handle", accepted resourceChainedHandoff),
   ("resource: accessing moved-from resource handle rejected (E0549)", !accepted resourceUseAfterMoveRejected),
   ("resource: plain immutable snapshot binding rejected", !accepted resourcePlainSnapshotRejected),
   ("resource: shared ^mut reception rejected", !accepted resourceSharedCopyRejected),
   ("resource: ^mut retention rejected on resource handle", !accepted resourceRetainRejected),
   ("resource: var mut slot overwrite rejected", !accepted resourceVarMutOverwriteRejected),
   ("resource: mut call borrow followed by new consumption accepted", accepted resourceCallBorrowAndConsume),
   ("resource: closure environment capture of resource handle rejected (E0604)", !accepted resourceClosureCaptureRejected),
   ("scoped: plain use on foreign resource handle permits ref observation", accepted scopedReadOnlyResourceObserveOk),
   ("scoped: plain use without body reads requires no E0527 write use", accepted scopedReadOnlyUnusedOk),
   ("scoped: use mut permits interior writes and lexical borrows", accepted scopedMutBlockUseAndBorrow),
   ("scoped: use mut permits ref and mut call borrows inside declaring scope", accepted scopedCallRefAndMutBorrows),
   ("scoped: plain use forbids mutation (E0520)", !accepted scopedReadOnlyRejectsWrite),
   ("scoped: reassigning use binding rejected (E0532)", !accepted scopedReassignRejected),
   ("scoped: moving use binding via new handoff rejected (E0604)", !accepted scopedMoveEscapeRejected),
   ("scoped: rebinding use binding to local alias rejected (E0604)", !accepted scopedRebindEscapeRejected),
   ("scoped: retaining use binding rejected (E0604)", !accepted scopedRetainEscapeRejected),
   ("scoped: passing use binding to new cleanup/consumer inside block rejected (E0604)", !accepted scopedCallNewHandoffRejected),
   ("scoped: capturing use binding in closure rejected (E0604)", !accepted scopedClosureCaptureRejected),
   ("scoped: accessing use binding after block exit rejected", !accepted scopedExpiredAfterBlockExit),
   ("scoped: use mut rejects idle writer without body mutation (E0527)", !accepted scopedIdleMutRejected),
   ("scoped: use mut accepts body write", accepted scopedBodyMutAccepted),
   ("scoped: cleanup contract accepts ref/mut/new () and rejects @fiber, ^mut, plain, or non-() (E0541/E0616)",
      validScopedCleanupContract { mode := .observe } &&
      validScopedCleanupContract { mode := .mutable, writes := true } &&
      validScopedCleanupContract { mode := .construction } &&
      !validScopedCleanupContract { mode := .mutable, writes := true, hasFiberEffect := true } &&
      !validScopedCleanupContract { mode := .retained } &&
      !validScopedCleanupContract { mode := .immutable } &&
      !validScopedCleanupContract { mode := .mutable, writes := true, returnsUnit := false }),
   ("scoped: cleanup writes require mut Self and retained sharing and captures are prohibited (E0541)",
      !validScopedCleanupContract { mode := .mutable } &&
      !validScopedCleanupContract { mode := .observe, writes := true } &&
      !validScopedCleanupContract { mode := .construction, writes := true } &&
      !validScopedCleanupContract { mode := .mutable, writes := true, retains := true } &&
      !validScopedCleanupContract { mode := .observe, captures := true })]

theorem fixtures_all_pass : fixtures.all Prod.snd = true := by decide +kernel

end RilAccess.Examples.ScopedExamples
