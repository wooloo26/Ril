import RilAccess.Access.Footprints

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

namespace RilAccess.Integrated.Examples

def fixed (access : Access) : MemberMode := ⟨false, access⟩
def replaceableMode (access : Access) : MemberMode := ⟨true, access⟩
def path (register : Nat) (fields : List Nat := []) : Path := ⟨register, fields⟩
def command (atom : Atom) : Syntax := .command atom
def sequence (commands : List Syntax) : Syntax :=
  commands.foldr Syntax.sequence (.command .skip)
def atoms (operations : List Atom) : Syntax := sequence (operations.map command)
def accepted (program : Syntax) : Bool := (check program).isOk

def immutableRead := atoms [.allocate 0 (fixed .immutable) [], .read (path 0)]
def immutableWrite := atoms [.allocate 0 (fixed .immutable) [], .write (path 0)]
def localWrite := atoms [.allocate 0 (fixed .mut) [], .write (path 0)]
def idleWriter := atoms [.allocate 0 (fixed .mut) [], .read (path 0)]
def liveObserver := atoms [.allocate 0 (fixed .mut) [], .bind (path 0) 1 (fixed .ref),
  .write (path 0), .read (path 1)]
def observerUpgrade := atoms [.allocate 0 (fixed .mut) [], .bind (path 0) 1 (fixed .ref), .write (path 1)]
def sharedWriter := atoms [.allocate 0 (fixed .mut) [], .bind (path 0) 1 (fixed .shared), .write (path 1)]
def exclusiveAlias := atoms [.allocate 0 (fixed .mut) [], .bind (path 0) 1 (fixed .mut), .write (path 1)]
def livePublication := atoms [.allocate 0 (fixed .mut) [], .bind (path 0) 1 (fixed .immutable)]
def fixedReplacement := atoms [.allocate 0 (fixed .immutable) [], .allocate 1 (fixed .immutable) [],
  .assign (path 1) 0]
def variableImmutable := atoms [.allocate 0 (replaceableMode .immutable) [], .allocate 1 (fixed .immutable) [],
  .assign (path 1) 0, .read (path 0)]
def variableConstruction := atoms [.allocate 0 (replaceableMode .mut) [], .allocate 1 (fixed .mut) [],
  .assign (path 1) 0, .write (path 0)]
def variableCannotMove := atoms [.allocate 0 (replaceableMode .mut) [], .move 0 1, .write (path 1)]
def variableNotPinned := atoms [.allocate 0 (replaceableMode .mut) [], .bind (path 0) 1 (fixed .ref)]
def oldSharedAliasSurvives := atoms [.allocate 0 (replaceableMode .mut) [],
  .bind (path 0) 1 (fixed .shared), .write (path 1), .allocate 2 (fixed .mut) [],
  .assign (path 2) 0, .write (path 0), .write (path 1)]
def validMove := atoms [.allocate 0 (fixed .mut) [], .bind (path 0) 1 (fixed .ref),
  .move 0 2, .write (path 2)]
def movedSource := atoms [.allocate 0 (fixed .mut) [], .move 0 1, .write (path 0)]
def movedObserver := atoms [.allocate 0 (fixed .mut) [], .bind (path 0) 1 (fixed .ref),
  .move 0 2, .write (path 2), .read (path 1)]
def sharedPreventsMove := atoms [.allocate 0 (fixed .mut) [],
  .bind (path 0) 1 (fixed .shared), .write (path 1), .move 0 2]

def validBorrow := sequence [command (.allocate 0 (fixed .mut) []),
  .borrow (path 0) 1 (command (.write (path 1))), command (.write (path 0))]
def independentBorrowWrite := sequence [command (.allocate 0 (fixed .mut) []),
  .borrow (path 0) 1 (command (.write (path 0)))]
def independentBorrowRead := sequence [command (.allocate 0 (fixed .mut) []),
  .borrow (path 0) 1 (atoms [.write (path 1), .read (path 0)])]
def nestedBorrow := sequence [command (.allocate 0 (fixed .mut) []),
  .borrow (path 0) 1 (sequence [.borrow (path 1) 2 (command (.write (path 2))),
    command (.write (path 1))]), command (.write (path 0))]
def temporarySharing := sequence [command (.allocate 0 (fixed .mut) []),
  .borrow (path 0) 1 (atoms [.bind (path 1) 2 (fixed .shared), .write (path 2)])]
def temporaryRetention := sequence [command (.allocate 0 (fixed .mut) []),
  .borrow (path 0) 1 (command (.retain (path 1)))]
def idleBorrow := sequence [command (.allocate 0 (fixed .mut) []),
  .borrow (path 0) 1 (command (.read (path 1)))]
def endedBorrowObserver := sequence [command (.allocate 0 (fixed .mut) []),
  .borrow (path 0) 1 (atoms [.bind (path 1) 2 (fixed .ref), .read (path 2), .write (path 1)]),
  command (.read (path 2))]
def escapingBorrowObserver := sequence [command (.allocate 0 (fixed .mut) []),
  command (.bind (path 0) 2 (replaceableMode .ref)),
  .borrow (path 0) 1 (atoms [.write (path 1), .assign (path 1) 2])]
def suspendedReplacement := sequence [command (.allocate 0 (replaceableMode .mut) []),
  .borrow (path 0) 1 (atoms [.allocate 2 (fixed .mut) [], .assign (path 2) 0, .write (path 1)])]

def scalarSchema (replaceable : Bool) : Schema :=
  [⟨[0], ⟨replaceable, .immutable⟩, false⟩]
def scalarReplacement := atoms [.allocate 0 (fixed .mut) (scalarSchema true),
  .replaceScalar (path 0 [0])]
def fixedScalarReplacement := atoms [.allocate 0 (fixed .mut) (scalarSchema false),
  .replaceScalar (path 0 [0])]
def scalarNotObject := atoms [.allocate 0 (fixed .mut) (scalarSchema true), .write (path 0 [0])]
def immutableSuppressesSlot := atoms [.allocate 0 (fixed .immutable) (scalarSchema true),
  .replaceScalar (path 0 [0])]
def observerSuppressesSlot := atoms [.allocate 0 (fixed .mut) (scalarSchema true),
  .bind (path 0) 1 (fixed .ref), .replaceScalar (path 1 [0])]
def defaultMember := atoms [.allocate 0 (fixed .mut) [⟨[0], fixed .immutable, true⟩],
  .bind (path 0 [0]) 1 (fixed .shared), .write (path 1)]
def disjointMembers := atoms [.allocate 0 (fixed .mut)
  [⟨[0], fixed .mut, true⟩, ⟨[1], fixed .mut, true⟩],
  .pairWrite (path 0 [0]) (path 0 [1])]
def overlappingPair := atoms [.allocate 0 (fixed .mut) [],
  .bind (path 0) 1 (fixed .shared), .pairWrite (path 0) (path 1)]
def nestedMember := atoms [.allocate 0 (fixed .mut)
  [⟨[0], fixed .mut, true⟩, ⟨[0, 0], ⟨true, .immutable⟩, false⟩],
  .replaceScalar (path 0 [0, 0])]
def missingMember := atoms [.allocate 0 (fixed .mut) [], .write (path 0 [99])]

def permute := sequence [command (.allocate 0 (fixed .mut) []),
  command (.allocate 1 (fixed .mut) []),
  command (.bind (path 0) 2 (replaceableMode .shared)),
  command (.bind (path 1) 3 (replaceableMode .shared)),
  .branch (atoms [.assign (path 0) 2, .assign (path 1) 3])
    (atoms [.assign (path 1) 2, .assign (path 0) 3]),
  command (.pairWrite (path 2) (path 3))]
def uncertainOverlap := sequence [command (.allocate 0 (fixed .mut) []),
  command (.allocate 1 (fixed .mut) []),
  command (.bind (path 0) 2 (replaceableMode .shared)),
  command (.bind (path 1) 3 (replaceableMode .shared)),
  .branch (atoms [.assign (path 0) 2, .assign (path 1) 3])
    (atoms [.assign (path 0) 2, .assign (path 0) 3]),
  command (.pairWrite (path 2) (path 3))]
def scopeEnded := sequence [.block (atoms [.allocate 0 (fixed .mut) [], .write (path 0)]),
  command (.read (path 0))]
def retainedPreventsMove := atoms [.allocate 0 (fixed .mut) [], .retain (path 0), .move 0 1]
def scopedRetention : Syntax := .block (atoms [.allocate 0 (fixed .mut) [], .retain (path 0)])
def possibleUse := sequence [command (.allocate 0 (fixed .mut) []),
  .branch (command (.write (path 0))) (command (.read (path 0)))]
def unclosed := atoms [.enterScope, .allocate 0 (fixed .immutable) []]
def rootless := atoms [.write (path 0)]

def injectedScopeEnd := sequence [command (.allocate 0 (fixed .mut) []),
  .borrow (path 0) 1 (atoms [.leaveScope, .write (path 0), .enterScope])]

def duplicatedDeclaration := Syntax.branch
  (atoms [.allocate 0 (fixed .mut) [], .write (path 0)])
  (atoms [.allocate 0 (fixed .mut) [], .read (path 0)])
def orphanField := atoms [.allocate 0 (fixed .immutable) [⟨[0, 1], fixed .mut, true⟩]]
def duplicateField := atoms [.allocate 0 (fixed .immutable)
  [⟨[0], fixed .mut, true⟩, ⟨[0], fixed .immutable, true⟩]]
def scalarObserver := atoms [.allocate 0 (fixed .mut) (scalarSchema true),
  .bind (path 0 [0]) 1 (fixed .ref)]
def scopeSharedEscape := sequence [command (.allocate 0 (fixed .mut) []),
  command (.bind (path 0) 1 (replaceableMode .shared)),
  .block (atoms [.allocate 2 (fixed .mut) [], .assign (path 2) 1]), command (.write (path 1))]
def scopeEscapePreventsMove := sequence [command (.allocate 0 (fixed .mut) []),
  command (.bind (path 0) 1 (replaceableMode .shared)),
  .block (atoms [.allocate 2 (fixed .mut) [], .assign (path 2) 1, .move 2 3]),
  command (.write (path 1))]
def chainedHandoff := atoms [.allocate 0 (fixed .mut) [], .bind (path 0) 1 (fixed .ref),
  .move 0 2, .move 2 3, .write (path 3)]
def laterSharedReception := atoms [.allocate 0 (replaceableMode .shared) [],
  .write (path 0), .allocate 1 (fixed .mut) [], .assign (path 1) 0, .write (path 0)]
def sharedWriterWithoutReception := atoms [.allocate 0 (replaceableMode .shared) [], .write (path 0)]

def confinedResult (program : Syntax) (scope : Nat) : Bool :=
  match check program with
  | .error _ => false
  | .ok analysis => analysis.worlds.all fun world =>
      confinedTo world scope ⟨0, [], ⟨.allocation, 0⟩⟩

def forgedMemberRejected : Bool :=
  let schema := [Field.mk [0] (fixed .immutable) true]
  let world := (transfer initialWorld (.allocate 0 (fixed .mut) schema)).getD initialWorld
  match resolve world (path 0 [0]) with
  | none => false
  | some resolved =>
    let forged := { resolved with
      members := [], effective := .shared,
      permission := { resolved.permission with mode := fixed .shared } }
    let evidence : Evidence := ⟨⟨.write, resolved.pointer⟩, .write, forged, [], []⟩
    authorizedLocal evidence && !authorized evidence

def fixtures : List (String × Bool) :=
  [("immutable read", accepted immutableRead),
   ("immutable write rejected", !accepted immutableWrite),
   ("local writable use", accepted localWrite),
   ("idle writer rejected", !accepted idleWriter),
   ("live observer", accepted liveObserver),
   ("observer upgrade rejected", !accepted observerUpgrade),
   ("shared writer", accepted sharedWriter),
   ("exclusive alias rejected", !accepted exclusiveAlias),
   ("live publication rejected", !accepted livePublication),
   ("fixed replacement rejected", !accepted fixedReplacement),
   ("var immutable replacement", accepted variableImmutable),
   ("var mutable construction input", accepted variableConstruction),
   ("var construction qualification rejected", !accepted variableCannotMove),
   ("var root is not pinned", !accepted variableNotPinned),
   ("old alias survives replacement", accepted oldSharedAliasSurvives),
   ("qualified handoff", accepted validMove),
   ("ended handoff source rejected", !accepted movedSource),
   ("ended derived observer rejected", !accepted movedObserver),
   ("shared root cannot hand off", !accepted sharedPreventsMove),
   ("temporary borrowing", accepted validBorrow),
   ("independent borrowed write rejected", !accepted independentBorrowWrite),
   ("independent borrowed read rejected", !accepted independentBorrowRead),
   ("nested borrowing", accepted nestedBorrow),
   ("temporary sharing rejected", !accepted temporarySharing),
   ("temporary retention rejected", !accepted temporaryRetention),
   ("idle temporary writer rejected", !accepted idleBorrow),
   ("ended borrower observer rejected", !accepted endedBorrowObserver),
   ("escaping borrower observer rejected", !accepted escapingBorrowObserver),
   ("suspended root replacement rejected", !accepted suspendedReplacement),
   ("scalar slot replacement", accepted scalarReplacement),
   ("fixed scalar slot rejected", !accepted fixedScalarReplacement),
   ("scalar is not an object", !accepted scalarNotObject),
   ("immutable suppresses var member", !accepted immutableSuppressesSlot),
   ("observer suppresses var member", !accepted observerSuppressesSlot),
   ("default member grants no writer", !accepted defaultMember),
   ("disjoint members", accepted disjointMembers),
   ("alias overlap rejected", !accepted overlappingPair),
   ("nested member path", accepted nestedMember),
   ("unknown member rejected", !accepted missingMember),
   ("correlated permute", accepted permute),
   ("possible overlap rejected", !accepted uncertainOverlap),
   ("scope expiry", !accepted scopeEnded),
   ("retention ends qualification", !accepted retainedPreventsMove),
   ("retention survives scope", accepted scopedRetention),
   ("use on one retained branch", accepted possibleUse),
   ("unclosed scope rejected", !accepted unclosed),
   ("rootless path rejected", !accepted rootless),
   ("scope bookkeeping cannot be injected", !accepted injectedScopeEnd),
   ("generated confined footprint", confinedResult localWrite 0),
   ("outside authority blocks confinement", !confinedResult localWrite 1),
   ("publication blocks confinement", !confinedResult scopedRetention 0),
   ("original schema rejects forged path modes", forgedMemberRejected),
   ("declaration identities are globally unique", !accepted duplicatedDeclaration),
   ("orphan schema path rejected", !accepted orphanField),
   ("duplicate schema field rejected", !accepted duplicateField),
   ("scalar cannot receive ref", !accepted scalarObserver),
   ("scope escape is inferred", accepted scopeSharedEscape),
   ("inferred escape prevents handoff", !accepted scopeEscapePreventsMove),
   ("ended paths permit subsequent handoff", accepted chainedHandoff),
   ("later shared assignment justifies var shared reception", accepted laterSharedReception),
   ("writing alone does not justify shared local reception", !accepted sharedWriterWithoutReception)]

theorem fixtures_all_pass : fixtures.all Prod.snd = true := by decide +kernel

theorem permute_two_worlds :
    (check permute).toOption.map (fun analysis => analysis.worlds.length) = some 2 := by decide +kernel

theorem accepted_has_real_execution :
    (sourceExecute localWrite initialWorld.raw).length = 1 ∧ accepted localWrite = true := by decide +kernel

end RilAccess.Integrated.Examples
