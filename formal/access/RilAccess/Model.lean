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

/-- Path attenuation cannot manufacture writable authority. -/
def attenuate (outer member : Access) : Access :=
  match outer with
  | .immutable => .immutable
  | .ref => if member = .immutable then .immutable else .ref
  | .mut | .shared => member

theorem attenuate_write (hw : (attenuate outer member).writes = true) :
    outer.writes = true ∧ member.writes = true := by
  cases outer <;> cases member <;> simp_all [attenuate, Access.writes]

def Separated (a b : List Nat) : Prop := ∀ x ∈ a, x ∉ b

end RilAccess
