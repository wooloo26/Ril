import RilAccess.Model

/-! Package visibility lattice (`private` < `pub(pkg)` < `pub`), contextual package
import anchors (`pkg`, `ril`, external dependencies), module representation opacity
(`transparent` vs `opaque`), top-level module purity (`E0906`), exported signature
and `use` cleanup contract leak detection (`E0910`), and extensible sum (`..`)
exhaustiveness across package and `.d.ril` boundaries (`E0303`, `E0304`, `E0308`). -/
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

inductive PackageAnchor where
  | pkg
  | ril
  | externalDep
  deriving Repr, DecidableEq

def importContext : PackageAnchor → ObserverContext
  | .pkg => .samePkg
  | .ril => .externalPkg
  | .externalDep => .externalPkg

def validDependencyMountName (name : String) : Bool :=
  name != "pkg" && name != "ril"

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
  deriving Repr, DecidableEq

def representationTransparent (vis : Visibility) (op : Opacity) (ctx : ObserverContext) : Bool :=
  visibleFrom vis ctx &&
  match op with
  | .transparent => true
  | .opaqueScope => decide (ctx = .sameScope)

/-- A library file with no `pub` items is package-sealed (`pubExport` capped at `pubPkg`). -/
def effectiveVisibility (moduleHasPub : Bool) (declVis : Visibility) : Visibility :=
  match declVis with
  | .priv => .priv
  | .pubPkg => .pubPkg
  | .pubExport => if moduleHasPub then .pubExport else .pubPkg

def Visibility.min (a b : Visibility) : Visibility :=
  if Visibility.le a b then a else b

/-- Effective visibility along an enclosing inline `sub` path caps the declaration's reachability. -/
def pathVisibility (moduleHasPub : Bool) (enclosingSubs : List Visibility) (declVis : Visibility) : Visibility :=
  enclosingSubs.foldl Visibility.min (effectiveVisibility moduleHasPub declVis)

/-- E0910: Every type or `use` cleanup handler referenced by a declaration's public
interface must have effective visibility at least as wide as the declaration. -/
def signatureWellFormed (moduleHasPub : Bool) (declVis : Visibility) (referencedVis : List Visibility) : Bool :=
  let eff := effectiveVisibility moduleHasPub declVis
  referencedVis.all fun itemVis => Visibility.le eff (effectiveVisibility moduleHasPub itemVis)

inductive TopLevelBindingKind where
  | pureConst
  | metaConst
  | mutableOrLiveState
  deriving Repr, DecidableEq

/-- E0906: Module top-level permits only pure deeply immutable `let` and `meta let`
constants; `var`, `let mut`, `let ^mut`, `let ref`, and scoped `use` bindings are prohibited. -/
def validTopLevelBinding : TopLevelBindingKind → Bool
  | .pureConst | .metaConst => true
  | .mutableOrLiveState => false

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
  representationTransparent s.vis s.op ctx

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

theorem opaqueScope_boundary :
    visibleFrom .pubExport .samePkg = true ∧
    visibleFrom .pubExport .externalPkg = true ∧
    representationTransparent .pubExport .opaqueScope .sameScope = true ∧
    representationTransparent .pubExport .opaqueScope .samePkg = false ∧
    representationTransparent .pubExport .opaqueScope .externalPkg = false := by
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

theorem topLevel_rejects_mutable_and_live_state :
    validTopLevelBinding .pureConst = true ∧
    validTopLevelBinding .metaConst = true ∧
    validTopLevelBinding .mutableOrLiveState = false := by
  decide

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

theorem opaqueScope_sum_blocks_outside_scope_match {s : SumDef} {ctx : ObserverContext}
    {covered : List Nat} {hasWildcard : Bool}
    (hop : s.op = .opaqueScope) (hout : ctx ≠ .sameScope) :
    exhaustiveMatch s ctx covered hasWildcard = false := by
  cases ctx <;> simp_all [exhaustiveMatch, canMatchVariants, representationTransparent]

theorem pkg_anchor_isolates_package_visibility :
    visibleFrom .pubPkg (importContext .pkg) = true ∧
    visibleFrom .pubPkg (importContext .ril) = false ∧
    visibleFrom .pubPkg (importContext .externalDep) = false ∧
    validDependencyMountName "pkg" = false ∧
    validDependencyMountName "ril" = false := by
  decide

theorem foldl_min_le_init (xs : List Visibility) (init : Visibility) :
    (xs.foldl Visibility.min init).rank ≤ init.rank := by
  induction xs generalizing init with
  | nil => exact Nat.le_refl _
  | cons hd tl ih =>
    have hstep := ih (Visibility.min init hd)
    have hmin : (Visibility.min init hd).rank ≤ init.rank := by
      cases init <;> cases hd <;> decide
    exact Nat.le_trans hstep hmin

theorem foldl_min_le_mem {xs : List Visibility} {init v : Visibility} (hv : v ∈ xs) :
    (xs.foldl Visibility.min init).rank ≤ v.rank := by
  induction xs generalizing init with
  | nil => nomatch hv
  | cons hd tl ih =>
    rcases List.mem_cons.mp hv with rfl | htl
    · have hstep := foldl_min_le_init tl (Visibility.min init v)
      have hmin : (Visibility.min init v).rank ≤ v.rank := by
        cases init <;> cases v <;> decide
      exact Nat.le_trans hstep hmin
    · exact ih htl

theorem enclosing_sub_caps_pathVisibility {moduleHasPub : Bool}
    {enclosingSubs : List Visibility} {declVis subVis : Visibility}
    (hmem : subVis ∈ enclosingSubs) :
    Visibility.le (pathVisibility moduleHasPub enclosingSubs declVis) subVis = true := by
  unfold Visibility.le pathVisibility
  exact decide_eq_true (foldl_min_le_mem hmem)

end RilAccess.VisibilityModel
