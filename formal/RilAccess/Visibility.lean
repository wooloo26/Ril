import RilAccess.Model

/-! Package visibility lattice (`private` < `pub(pkg)` < `pub`), representation
opacity (`opaque` vs `pub opaque(pkg)`), exported signature leak detection (`E0910`),
opacity well-formedness (`E0911`), and extensible sum (`..`) exhaustiveness across
package and `.d.ril` boundaries (`E0303`, `E0304`, `E0908`). -/
namespace RilAccess.VisibilityModel

inductive Visibility where
  | priv
  | pubPkg
  | pubExport
  deriving Repr, DecidableEq

def Visibility.rank : Visibility → Nat
  | .priv => 0
  | .pubPkg => 1
  | .pubExport => 2

def Visibility.le (a b : Visibility) : Bool :=
  decide (a.rank ≤ b.rank)

inductive ObserverContext where
  | sameScope
  | samePkg
  | externalPkg
  deriving Repr, DecidableEq

def visibleFrom (vis : Visibility) (ctx : ObserverContext) : Bool :=
  match vis, ctx with
  | _, .sameScope => true
  | .priv, _ => false
  | .pubPkg, .samePkg => true
  | .pubPkg, .externalPkg => false
  | .pubExport, _ => true

inductive Opacity where
  | transparent
  | opaqueScope
  | opaquePkg
  deriving Repr, DecidableEq

/-- E0911: `opaque(pkg)` requires explicit `pub` (`pubExport`) visibility. -/
def validOpacity (vis : Visibility) (op : Opacity) : Bool :=
  match op with
  | .transparent | .opaqueScope => true
  | .opaquePkg => decide (vis = .pubExport)

def representationTransparent (vis : Visibility) (op : Opacity) (ctx : ObserverContext) : Bool :=
  visibleFrom vis ctx &&
  match op with
  | .transparent => true
  | .opaqueScope => decide (ctx = .sameScope)
  | .opaquePkg => decide (ctx = .sameScope) || decide (ctx = .samePkg)

/-- A library file with no `pub` items is package-sealed (`pubExport` capped at `pubPkg`). -/
def effectiveVisibility (moduleHasPub : Bool) (declVis : Visibility) : Visibility :=
  match declVis with
  | .priv => .priv
  | .pubPkg => .pubPkg
  | .pubExport => if moduleHasPub then .pubExport else .pubPkg

/-- E0910: Every type referenced by a declaration's signature must have effective
visibility at least as wide as the declaration's own effective visibility. -/
def signatureWellFormed (moduleHasPub : Bool) (declVis : Visibility) (referencedTypes : List Visibility) : Bool :=
  let eff := effectiveVisibility moduleHasPub declVis
  referencedTypes.all fun tVis => Visibility.le eff (effectiveVisibility moduleHasPub tVis)

inductive SumOrigin where
  | rilPkg
  | foreignDecl
  deriving Repr, DecidableEq

structure SumDef where
  origin : SumOrigin
  vis : Visibility
  op : Opacity
  extensible : Bool
  variants : List Nat
  deriving Repr, DecidableEq

def canMatchVariants (s : SumDef) (ctx : ObserverContext) : Bool :=
  validOpacity s.vis s.op && representationTransparent s.vis s.op ctx

def requiresWildcard (s : SumDef) (ctx : ObserverContext) : Bool :=
  s.extensible && (decide (s.origin = .foreignDecl) || decide (ctx = .externalPkg))

/-- Exhaustiveness and non-redundancy check for sum pattern matching:
- Open sums (`requiresWildcard = true`) require a wildcard arm even if all currently
  declared variants are listed.
- Closed sums (`requiresWildcard = false`) require either every declared variant
  without a redundant wildcard, or a proper subset with a wildcard arm. -/
def exhaustiveMatch (s : SumDef) (ctx : ObserverContext) (covered : List Nat) (hasWildcard : Bool) : Bool :=
  canMatchVariants s ctx &&
  let allDeclaredCovered := s.variants.all (fun v => decide (v ∈ covered))
  if requiresWildcard s ctx then
    hasWildcard
  else if hasWildcard then
    !allDeclaredCovered
  else
    allDeclaredCovered

theorem visibility_le_refl (v : Visibility) : Visibility.le v v = true := by
  cases v <;> decide

theorem visibility_le_trans {a b c : Visibility}
    (hab : Visibility.le a b = true) (hbc : Visibility.le b c = true) :
    Visibility.le a c = true := by
  simp only [Visibility.le, decide_eq_true_eq] at hab hbc ⊢
  omega

theorem opaquePkg_requires_pubExport {vis : Visibility} :
    validOpacity vis .opaquePkg = true ↔ vis = .pubExport := by
  cases vis <;> simp [validOpacity]

theorem opaquePkg_boundary :
    visibleFrom .pubExport .externalPkg = true ∧
    representationTransparent .pubExport .opaquePkg .samePkg = true ∧
    representationTransparent .pubExport .opaquePkg .externalPkg = false := by
  decide

theorem pubPkg_hidden_externally :
    visibleFrom .pubPkg .samePkg = true ∧
    visibleFrom .pubPkg .externalPkg = false := by
  decide

theorem signature_rejects_pubPkg_leak {refs : List Visibility}
    (hmem : Visibility.pubPkg ∈ refs) :
    signatureWellFormed true .pubExport refs = false := by
  cases hs : signatureWellFormed true .pubExport refs with
  | false => rfl
  | true =>
    have hall := List.all_eq_true.mp hs .pubPkg hmem
    simp [effectiveVisibility, Visibility.le, Visibility.rank] at hall

theorem ril_extensible_closed_inside_pkg {s : SumDef} {ctx : ObserverContext} {covered : List Nat}
    (horig : s.origin = .rilPkg) (hext : s.extensible = true)
    (hctx : ctx = .sameScope ∨ ctx = .samePkg)
    (hcan : canMatchVariants s ctx = true)
    (hall : ∀ v ∈ s.variants, v ∈ covered) :
    exhaustiveMatch s ctx covered false = true ∧
      exhaustiveMatch s ctx covered true = false := by
  have hreq : requiresWildcard s ctx = false := by
    rcases hctx with rfl | rfl <;> simp [requiresWildcard, horig, hext]
  have hallBool : (s.variants.all fun v => decide (v ∈ covered)) = true :=
    List.all_eq_true.mpr (fun v hv => decide_eq_true (hall v hv))
  simp [exhaustiveMatch, hcan, hreq, hallBool]

theorem ril_extensible_open_outside_pkg {s : SumDef} {covered : List Nat}
    (horig : s.origin = .rilPkg) (hext : s.extensible = true)
    (hcan : canMatchVariants s .externalPkg = true) :
    exhaustiveMatch s .externalPkg covered false = false ∧
      exhaustiveMatch s .externalPkg covered true = true := by
  have hreq : requiresWildcard s .externalPkg = true := by
    simp [requiresWildcard, horig, hext]
  simp [exhaustiveMatch, hcan, hreq]

theorem foreign_extensible_open_everywhere {s : SumDef} {ctx : ObserverContext} {covered : List Nat}
    (horig : s.origin = .foreignDecl) (hext : s.extensible = true) :
    exhaustiveMatch s ctx covered false = false := by
  have hreq : requiresWildcard s ctx = true := by
    simp [requiresWildcard, horig, hext]
  simp [exhaustiveMatch, hreq]

theorem opaquePkg_sum_blocks_external_match {s : SumDef} {covered : List Nat} {hasWildcard : Bool}
    (hop : s.op = .opaquePkg) :
    exhaustiveMatch s .externalPkg covered hasWildcard = false := by
  simp [exhaustiveMatch, canMatchVariants, representationTransparent, hop]

end RilAccess.VisibilityModel
