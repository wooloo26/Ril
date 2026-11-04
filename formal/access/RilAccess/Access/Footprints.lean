import RilAccess.Access.Progress

namespace RilAccess.Integrated

inductive RootKind where
  | binding | retained | loan
  deriving Repr, DecidableEq

structure AuthorityRoot where
  pointer : Pointer
  scope : Nat
  kind : RootKind
  deriving Repr, DecidableEq

def bindingRoots (w : World) : List AuthorityRoot :=
  w.permissions.flatMap fun permission =>
    if permission.alive then
      (rawLookup w.raw permission.register).toList.map fun pointer =>
        ⟨pointer, permission.scope, .binding⟩
    else []

/-- Retained observations are erased-runtime evidence of external roots. Using
the log here also prevents a missing metadata token from hiding a publication. -/
def retainedRoots (w : World) : List AuthorityRoot :=
  w.raw.observations.flatMap fun event =>
    if event.kind = .retain then [⟨event.pointer, 0, .retained⟩] else []

def loanRoots (w : World) : List AuthorityRoot :=
  w.loans.map fun loan =>
    ⟨loan.region, ((lookupToken w loan.token).map Token.scope).getD 0, .loan⟩

def authorityRoots (w : World) : List AuthorityRoot :=
  bindingRoots w ++ retainedRoots w ++ loanRoots w

/-- Conservative confinement in this closed, tree-shaped reference model. -/
def confinedTo (w : World) (scope : Nat) (region : Pointer) : Bool :=
  (authorityRoots w).all fun root => !overlaps root.pointer region ||
    (decide (scope ≤ root.scope) && decide (root.kind ≠ .retained))

theorem every_live_binding_in_footprint (hp : permission ∈ w.permissions)
    (ha : permission.alive = true) (hr : rawLookup w.raw permission.register = some pointer) :
    AuthorityRoot.mk pointer permission.scope .binding ∈ authorityRoots w := by
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  exact ⟨permission, hp, by simp [ha, hr]⟩

theorem every_publication_in_footprint (he : event ∈ w.raw.observations)
    (hk : event.kind = .retain) :
    AuthorityRoot.mk event.pointer 0 .retained ∈ authorityRoots w := by
  apply List.mem_append_left
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  exact ⟨event, he, by simp [hk]⟩

theorem every_loan_in_footprint (hl : loan ∈ w.loans) :
    AuthorityRoot.mk loan.region ((lookupToken w loan.token).map Token.scope |>.getD 0) .loan ∈
      authorityRoots w := by
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨loan, hl, rfl⟩

theorem confinement_covers_every_root (h : confinedTo w scope region = true)
    (hr : root ∈ authorityRoots w) (hoverlap : overlaps root.pointer region = true) :
    scope ≤ root.scope ∧ root.kind ≠ .retained := by
  have hall := List.all_eq_true.mp h root hr
  simpa [hoverlap] using hall

theorem retained_root_prevents_discharge (h : confinedTo w scope region = true)
    (he : event ∈ w.raw.observations) (hk : event.kind = .retain)
    (hoverlap : overlaps event.pointer region = true) : False := by
  have hn := confinement_covers_every_root h (every_publication_in_footprint he hk) hoverlap
  exact hn.2 rfl

theorem outside_binding_prevents_discharge (h : confinedTo w scope region = true)
    (hp : permission ∈ w.permissions) (ha : permission.alive = true)
    (hr : rawLookup w.raw permission.register = some pointer)
    (hoverlap : overlaps pointer region = true) (houtside : permission.scope < scope) : False := by
  have hn := confinement_covers_every_root h (every_live_binding_in_footprint hp ha hr) hoverlap
  have hs : scope ≤ permission.scope := hn.1
  omega

end RilAccess.Integrated
