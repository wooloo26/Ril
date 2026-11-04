import Std

namespace RilAccess

inductive Access where
  | immutable | ref | mut | shared
  deriving Repr, DecidableEq

structure MemberMode where
  replaceable : Bool
  access : Access
  deriving Repr, DecidableEq

def Access.writes : Access → Bool
  | .mut | .shared => true
  | _ => false

inductive SourceKind where
  | parameter | module | capture | allocation | foreign
  deriving Repr, DecidableEq

/-- A finite declaration/site name, not a dynamic allocation identity. -/
structure Source where
  kind : SourceKind
  declaration : Nat
  deriving Repr, DecidableEq

/-- Activations and allocation identities are retained in concrete metadata. -/
structure Origin where
  source : Source
  activation : Nat
  object : Nat
  task : Nat
  scope : Nat
  deriving Repr, DecidableEq

structure Handle where
  origin : Origin
  access : Access
  authority : Nat
  deriving Repr, DecidableEq

structure Authority where
  active : Bool
  temporary : Bool
  construction : Bool
  deriving Repr, DecidableEq

def CanWrite (h : Handle) (a : Authority) : Prop :=
  h.access.writes = true ∧ a.active = true

/-- Path attenuation cannot manufacture writable authority. -/
def attenuate (outer member : Access) : Access :=
  match outer with
  | .immutable => .immutable
  | .ref => if member = .immutable then .immutable else .ref
  | .mut | .shared => member

theorem attenuate_write (hw : (attenuate outer member).writes = true) :
    outer.writes = true ∧ member.writes = true := by
  cases outer <;> cases member <;> simp_all [attenuate, Access.writes]

def endAuthority (a : Authority) : Authority := { a with active := false }

theorem ended_no_write : ¬ CanWrite h (endAuthority a) := by
  simp [CanWrite, endAuthority]

/-- Handoff preserves the object, and consumes one authority shared by derived handles. -/
def handoff (h : Handle) (freshAuthority : Nat) : Handle :=
  { h with authority := freshAuthority }

structure TransferResult where
  sourceAuthority : Authority
  target : Handle
  targetAuthority : Authority
  deriving Repr, DecidableEq

def transferConstruction (h : Handle) (a : Authority) (fresh : Nat) : Option TransferResult :=
  if a.active && a.construction && decide (fresh ≠ h.authority) then
    some ⟨endAuthority a, handoff h fresh, { a with active := true }⟩
  else none

theorem transfer_consumes_and_preserves
    (ht : transferConstruction h a fresh = some result) :
    result.target.origin = h.origin ∧ ¬ CanWrite h result.sourceAuthority ∧
      result.target.authority ≠ h.authority := by
  unfold transferConstruction at ht
  split at ht
  · rename_i hvalid
    cases ht
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hvalid
    exact ⟨rfl, ended_no_write, hvalid.2⟩
  · contradiction

def Separated (a b : List Nat) : Prop := ∀ x ∈ a, x ∉ b

end RilAccess
