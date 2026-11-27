import Std

namespace RilAccess

inductive Access where
  | immutable | ref | mut | shared
  deriving Repr, DecidableEq

inductive ParameterMode where
  | immutable | observe | mutable | retained | construction
  deriving Repr, DecidableEq

def ParameterMode.access : ParameterMode → Access
  | .immutable => .immutable
  | .observe => .ref
  | .mutable | .construction => .mut
  | .retained => .shared

/-- Conflicts refer to actual regions. Modes determine which pairs need a
    separation check independently of the region representation. -/
def ParameterMode.conflicts (left right : ParameterMode) : Bool :=
  left == .mutable || right == .mutable || left == .retained && right == .retained ||
    left == .construction || right == .construction

structure MemberMode where
  replaceable : Bool
  access : Access
  deriving Repr, DecidableEq

def Access.writes : Access → Bool
  | .mut | .shared => true
  | _ => false

inductive SourceKind where
  | parameter | module | capture | allocation
  deriving Repr, DecidableEq

/-- A finite declaration/site name, not a dynamic allocation identity. -/
structure Source where
  kind : SourceKind
  declaration : Nat
  deriving Repr, DecidableEq

/-- Activations and allocation identities are retained in concrete metadata. -/
structure SourceInstance where
  source : Source
  activation : Nat
  object : Nat
  scope : Nat
  deriving Repr, DecidableEq

/-- Explanation of a state event. Labels carry no authority. -/
inductive Mechanism where
  | binding | aggregate | projection | call | higherOrder | returnValue | closure
  | via | infer | module | opaque | handler | cleanup | resource
  | clone | derive | handoff
  deriving Repr, DecidableEq

inductive EventKind where
  | read | write | retain | capture | rootReturn | containedReturn | transfer
  deriving Repr, DecidableEq

structure Event where
  kind : EventKind
  srcInst : SourceInstance
  mechanism : Mechanism
  deriving Repr, DecidableEq

structure HeapLink (Object : Type) where
  parent : Object
  field : Nat
  child : Object
  deriving Repr, DecidableEq

def HeapLink.map (f : α → β) (edge : HeapLink α) : HeapLink β :=
  ⟨f edge.parent, edge.field, f edge.child⟩

abbrev HeapEdge := HeapLink SourceInstance

/-- Path attenuation cannot manufacture writable authority. -/
def attenuate (outer member : Access) : Access :=
  match outer with
  | .immutable => .immutable
  | .ref => if member = .immutable then .immutable else .ref
  | .mut | .shared => member

theorem attenuate_write (hw : (attenuate outer member).writes = true) :
    outer.writes = true ∧ member.writes = true := by
  cases outer <;> cases member <;> simp_all [attenuate, Access.writes]

def SourceKind.admitsPureRil : SourceKind → Bool
  | .parameter | .module | .capture => true
  | .allocation => false

/-- Verified deeply immutable `.ril` or static origins; allocation sources never qualify. -/
def isPureInstance (pureSources : List Source) (o : SourceInstance) : Bool :=
  o.source.kind.admitsPureRil && decide (o.source ∈ pureSources)

def Separated (a b : List Nat) : Prop := ∀ x ∈ a, x ∉ b

end RilAccess
