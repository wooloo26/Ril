import RilAccess.Draft.Boundary

/-! The boundary uses resolved type shapes and evaluated operands. The caller
supplies the actual type classification and heap, including complete authority
metadata. Tags name storage schemas, including selected sum variants. -/
namespace RilAccess.Draft

inductive RootShape where
  | unit
  | record (tag : Nat)
  | nonemptyTuple (tag : Nat)
  | collection (tag : Nat)
  | sum (tag : Nat)
  | ineligible

def RootShape.objectTag : RootShape → Option Nat
  | .record tag | .nonemptyTuple tag | .collection tag | .sum tag => some tag
  | .unit | .ineligible => none

def RootShape.isTuple : RootShape → Bool
  | .unit | .nonemptyTuple _ => true
  | _ => false

def unitValue (unitTag : Nat) : Value := .scalar unitTag 0

inductive UnitVariant where
  | tag (schema : Nat)
  | payload (schema : Nat)

inductive ConstructorForm where
  | bare | emptyCall | unitArgument

inductive ConstructorError where
  | nullaryVariantCall | callableValue
  deriving Repr, DecidableEq

/-- Lower a resolved tag or unit-literal construction. Bare payload constructors
denote callable values and are outside this sum allocation boundary. -/
def lowerUnitVariant (unitTag : Nat) (origin : Origin) (variant : UnitVariant)
    (form : ConstructorForm) : Except ConstructorError Cell :=
  match variant, form with
  | .tag schema, .bare => .ok ⟨origin, .fixed schema [], []⟩
  | .tag _, _ => .error .nullaryVariantCall
  | .payload _, .bare => .error .callableValue
  | .payload schema, .emptyCall | .payload schema, .unitArgument =>
    .ok ⟨origin, .fixed schema [⟨.scalar unitTag, ⟨false, .immutable⟩⟩], [unitValue unitTag]⟩

theorem unit_call_equivalent (unitTag : Nat) (origin : Origin) (schema : Nat) :
    lowerUnitVariant unitTag origin (.payload schema) .emptyCall =
      lowerUnitVariant unitTag origin (.payload schema) .unitArgument := rfl

inductive DeriveInputError where
  | invalidDeriveInput -- E0536
  deriving Repr, DecidableEq

/-- Select the root from the evaluated operand. Core preparation checks the
immutable reception and graph of that root. -/
def prepareRoot (shape : RootShape) (value : Value) (input : Input) :
    Except DeriveInputError World :=
  match shape.objectTag, value with
  | some tag, .reference root =>
    if valueFits (lookup input.pool) (.object tag) value then
      match prepare { input with root } with
      | some start => .ok start
      | none => .error .invalidDeriveInput
    else .error .invalidDeriveInput
  | _, _ => .error .invalidDeriveInput

theorem unit_root_rejected (value : Value) (input : Input) :
    prepareRoot .unit value input = .error .invalidDeriveInput := by
  cases value <;> rfl

theorem prepared_root_sound (h : prepareRoot shape value input = .ok start) :
    ∃ tag root cell, shape.objectTag = some tag ∧ value = .reference root ∧
      lookup input.pool root = some cell ∧ cell.storage.tag = tag ∧
      prepare { input with root } = some start := by
  cases ht : shape.objectTag with
  | none => cases value <;> simp [prepareRoot, ht] at h
  | some tag =>
    cases value with
    | scalar => simp [prepareRoot, ht] at h
    | reference root =>
      cases hl : lookup input.pool root with
      | none => simp [prepareRoot, ht, valueFits, hl] at h
      | some cell =>
        by_cases hs : cell.storage.tag = tag
        · cases hp : prepare { input with root } with
          | none => simp [prepareRoot, ht, valueFits, hl, hs, hp] at h
          | some world =>
            have same : world = start := by simpa [prepareRoot, ht, valueFits, hl, hs, hp] using h
            exact ⟨tag, root, cell, rfl, rfl, hl, hs, same ▸ hp⟩
        · simp [prepareRoot, ht, valueFits, hl, hs] at h

end RilAccess.Draft
