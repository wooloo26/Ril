import RilAccess.Access.Progress

namespace RilAccess.Integrated

inductive RootKind where
  | binding | retained | hold
  deriving Repr, DecidableEq

structure AuthorityRoot where
  pointer : Pointer
  scope : Nat
  kind : RootKind
  deriving Repr, DecidableEq

def bindingRoots (w : World) : List AuthorityRoot :=
  w.bindings.flatMap fun binding =>
    if binding.alive then
      (rawLookup w.raw binding.register).toList.map fun pointer =>
        ⟨pointer, binding.scope, .binding⟩
    else []

/-- Retained observations are erased-runtime records of outside roots. Using
the log here also prevents a missing metadata token from hiding a publication. -/
def retainedRoots (w : World) : List AuthorityRoot :=
  w.raw.observations.flatMap fun event =>
    if event.kind = .retain then [⟨event.pointer, 0, .retained⟩] else []

def holdRoots (w : World) : List AuthorityRoot :=
  w.holds.map fun hold =>
    ⟨hold.region, ((lookupToken w hold.token).map Token.scope).getD 0, .hold⟩

def authorityRoots (w : World) : List AuthorityRoot :=
  bindingRoots w ++ retainedRoots w ++ holdRoots w

/-- Conservative confinement in this closed, tree-shaped reference model. -/
def confinedTo (w : World) (scope : Nat) (region : Pointer) : Bool :=
  (authorityRoots w).all fun root => !overlaps root.pointer region ||
    (decide (scope ≤ root.scope) && decide (root.kind ≠ .retained))

theorem every_live_binding_in_footprint (hp : binding ∈ w.bindings)
    (ha : binding.alive = true) (hr : rawLookup w.raw binding.register = some pointer) :
    AuthorityRoot.mk pointer binding.scope .binding ∈ authorityRoots w := by
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  exact ⟨binding, hp, by simp [ha, hr]⟩

theorem every_publication_in_footprint (he : event ∈ w.raw.observations)
    (hk : event.kind = .retain) :
    AuthorityRoot.mk event.pointer 0 .retained ∈ authorityRoots w := by
  apply List.mem_append_left
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  exact ⟨event, he, by simp [hk]⟩

theorem every_hold_in_footprint (hl : hold ∈ w.holds) :
    AuthorityRoot.mk hold.region ((lookupToken w hold.token).map Token.scope |>.getD 0) .hold ∈
      authorityRoots w := by
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨hold, hl, rfl⟩

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
    (hp : binding ∈ w.bindings) (ha : binding.alive = true)
    (hr : rawLookup w.raw binding.register = some pointer)
    (hoverlap : overlaps pointer region = true) (houtside : binding.scope < scope) : False := by
  have hn := confinement_covers_every_root h (every_live_binding_in_footprint hp ha hr) hoverlap
  have hs : scope ≤ binding.scope := hn.1
  omega

end RilAccess.Integrated
