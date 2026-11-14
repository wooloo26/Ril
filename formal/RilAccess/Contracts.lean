import RilAccess.Provenance.Semantics

namespace RilAccess

/-- These executable boundary judgments consume facts, never manufacture them. -/
def pathAccess (root : Access) (members : List Access) : Access :=
  members.foldl attenuate root

theorem path_write_requires_root (hw : (pathAccess root members).writes = true) :
    root.writes = true := by
  induction members generalizing root with
  | nil => exact hw
  | cons member rest ih =>
    exact (attenuate_write (ih hw)).1

theorem path_write_requires_members (hw : (pathAccess root members).writes = true) :
    ∀ m ∈ members, m.writes = true := by
  induction members generalizing root with
  | nil => simp
  | cons member rest ih =>
    have hfirst := attenuate_write (path_write_requires_root hw)
    intro m hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hfirst.2
    · exact ih hw m hm

structure Footprint where
  roots : List Origin
  environments : List Origin
  escaping : List Origin
  deriving Repr, DecidableEq

def owned (activation task scope : Nat) (o : Origin) : Bool :=
  decide (o.source.kind = .allocation) && decide (o.activation = activation) &&
    decide (o.task = task) && decide (o.scope = scope)

def confined (activation task scope : Nat) (f : Footprint) : Bool :=
  (f.roots ++ f.environments).all (owned activation task scope) && f.escaping.isEmpty

def localEvent : EventKind → Bool
  | .read | .write => true
  | _ => false

def discharge (activation task scope : Nat) (f : Footprint) (events : List Event) : List Event :=
  events.filter fun e =>
    !(localEvent e.kind && owned activation task scope e.origin && confined activation task scope f)

theorem discharge_only_confined (he : e ∈ events)
    (hn : e ∉ discharge activation task scope f events) :
    localEvent e.kind = true ∧ owned activation task scope e.origin = true ∧
      confined activation task scope f = true := by
  simp only [discharge, List.mem_filter, Bool.not_eq_true', Bool.and_eq_false_iff,
    not_and, he, true_implies] at hn
  simp_all

theorem retained_event_survives (he : e ∈ events) (hk : localEvent e.kind = false) :
    e ∈ discharge activation task scope f events := by
  simp [discharge, he, hk]

theorem confined_roots (h : confined activation task scope f = true)
    (ho : o ∈ f.roots ++ f.environments) : owned activation task scope o = true := by
  have hall : (f.roots ++ f.environments).all (owned activation task scope) = true :=
    (by simpa only [confined, Bool.and_eq_true] using h :
      (f.roots ++ f.environments).all (owned activation task scope) = true ∧
        f.escaping.isEmpty = true).1
  exact List.all_eq_true.mp hall o ho

theorem escaping_prevents_discharge (he : f.escaping ≠ []) :
    confined activation task scope f = false := by
  cases h : f.escaping <;> simp_all [confined]

def FootprintCovers (abstract concrete : Footprint) : Prop :=
  (∀ o ∈ concrete.roots, o ∈ abstract.roots) ∧
  (∀ o ∈ concrete.environments, o ∈ abstract.environments) ∧
  (∀ o ∈ concrete.escaping, o ∈ abstract.escaping)

theorem confinement_from_overapproximation (cover : FootprintCovers abstract concrete)
    (h : confined activation task scope abstract = true) :
    confined activation task scope concrete = true := by
  have ha := h
  simp only [confined, Bool.and_eq_true, List.isEmpty_iff] at ha
  simp only [confined, Bool.and_eq_true, List.isEmpty_iff]
  refine ⟨?_, ?_⟩
  · apply List.all_eq_true.mpr
    intro o ho
    apply confined_roots h
    rcases List.mem_append.mp ho with hr | he
    · exact List.mem_append_left _ (cover.1 o hr)
    · exact List.mem_append_right _ (cover.2.1 o he)
  · cases he : concrete.escaping with
    | nil => rfl
    | cons o rest =>
      have hm := cover.2.2 o (by simp [he])
      simp [ha.2] at hm

theorem static_discharge_safe (cover : FootprintCovers abstract concrete)
    (he : e ∈ events) (hn : e ∉ discharge activation task scope abstract events) :
    e ∉ discharge activation task scope concrete events := by
  obtain ⟨hk, ho, hf⟩ := discharge_only_confined he hn
  simp [discharge, hk, ho, confinement_from_overapproximation cover hf]

structure Summary where
  rootReturn : List Origin
  contained : List Origin
  writes : List Origin
  retained : List Origin
  createdEnvironments : List Origin
  namedReads : List Origin
  effects : List Nat
  deriving Repr, DecidableEq

def Summary.combine (a b : Summary) : Summary :=
  ⟨a.rootReturn ++ b.rootReturn, a.contained ++ b.contained, a.writes ++ b.writes,
    a.retained ++ b.retained, a.createdEnvironments ++ b.createdEnvironments,
    a.namedReads ++ b.namedReads, a.effects ++ b.effects⟩

/-- Effect handling does not erase any state/provenance component. -/
def Summary.handle (s : Summary) (effect : Nat) : Summary :=
  { s with effects := s.effects.filter (fun e => e != effect) }

def Summary.isPure (pureSources : List Source) (s : Summary) : Bool :=
  s.effects.isEmpty &&
  s.rootReturn.isEmpty &&
  s.contained.isEmpty &&
  s.writes.isEmpty &&
  s.retained.isEmpty &&
  s.namedReads.all (isPureOrigin pureSources) &&
  s.createdEnvironments.all (isPureOrigin pureSources)

/-- CallableType upper-bound contract matching after pure-origin reduction (`actual ⊑ expected`). -/
def Summary.subsumes (pureSources : List Source) (expected actual : Summary) : Bool :=
  actual.effects.all (fun e => decide (e ∈ expected.effects)) &&
  actual.rootReturn.all (fun o => decide (o ∈ expected.rootReturn)) &&
  actual.contained.all (fun o => decide (o ∈ expected.contained)) &&
  actual.retained.all (fun o => decide (o ∈ expected.retained)) &&
  actual.writes.all (fun o => decide (o ∈ expected.writes ∨ o ∈ expected.retained)) &&
  actual.namedReads.all (fun o =>
    isPureOrigin pureSources o ||
    decide (o ∈ expected.namedReads ∨ o ∈ expected.writes ∨ o ∈ expected.retained)) &&
  actual.createdEnvironments.all (fun o =>
    isPureOrigin pureSources o || decide (o ∈ expected.createdEnvironments))

structure SummarySubsumes (pureSources : List Source) (expected actual : Summary) : Prop where
  effects : ∀ e ∈ actual.effects, e ∈ expected.effects
  rootReturn : ∀ o ∈ actual.rootReturn, o ∈ expected.rootReturn
  contained : ∀ o ∈ actual.contained, o ∈ expected.contained
  retained : ∀ o ∈ actual.retained, o ∈ expected.retained
  writes : ∀ o ∈ actual.writes, o ∈ expected.writes ∨ o ∈ expected.retained
  namedReads : ∀ o ∈ actual.namedReads,
    isPureOrigin pureSources o = true ∨ o ∈ expected.namedReads ∨ o ∈ expected.writes ∨ o ∈ expected.retained
  createdEnvironments : ∀ o ∈ actual.createdEnvironments,
    isPureOrigin pureSources o = true ∨ o ∈ expected.createdEnvironments

theorem summary_subsumes_iff {pureSources : List Source} {expected actual : Summary} :
    expected.subsumes pureSources actual = true ↔ SummarySubsumes pureSources expected actual := by
  constructor
  · intro h
    simp only [Summary.subsumes, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
      decide_eq_true_eq] at h
    exact ⟨h.1.1.1.1.1.1, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩
  · intro h
    simp only [Summary.subsumes, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
      decide_eq_true_eq]
    exact ⟨⟨⟨⟨⟨⟨h.effects, h.rootReturn⟩, h.contained⟩, h.retained⟩, h.writes⟩, h.namedReads⟩,
      h.createdEnvironments⟩

theorem summary_subsumes_refl (pureSources : List Source) (s : Summary) :
    s.subsumes pureSources s = true := by
  rw [summary_subsumes_iff]
  exact ⟨fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h,
    fun _ h => Or.inl h, fun _ h => Or.inr (Or.inl h), fun _ h => Or.inr h⟩

theorem summary_subsumes_trans {pureSources : List Source} {a b c : Summary}
    (hab : b.subsumes pureSources a = true) (hbc : c.subsumes pureSources b = true) :
    c.subsumes pureSources a = true := by
  have hab' := summary_subsumes_iff.mp hab
  have hbc' := summary_subsumes_iff.mp hbc
  rw [summary_subsumes_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he; exact hbc'.effects e (hab'.effects e he)
  · intro o ho; exact hbc'.rootReturn o (hab'.rootReturn o ho)
  · intro o ho; exact hbc'.contained o (hab'.contained o ho)
  · intro o ho; exact hbc'.retained o (hab'.retained o ho)
  · intro o ho
    rcases hab'.writes o ho with hw | hr
    · exact hbc'.writes o hw
    · exact Or.inr (hbc'.retained o hr)
  · intro o ho
    rcases hab'.namedReads o ho with hp | hn | hw | hr
    · exact Or.inl hp
    · exact hbc'.namedReads o hn
    · rcases hbc'.writes o hw with hw' | hr'
      · exact Or.inr (Or.inr (Or.inl hw'))
      · exact Or.inr (Or.inr (Or.inr hr'))
    · exact Or.inr (Or.inr (Or.inr (hbc'.retained o hr)))
  · intro o ho
    rcases hab'.createdEnvironments o ho with hp | hc
    · exact Or.inl hp
    · exact hbc'.createdEnvironments o hc

theorem pure_summary_subsumed_by_any {pureSources : List Source} {actual : Summary}
    (hp : actual.isPure pureSources = true) (expected : Summary) :
    expected.subsumes pureSources actual = true := by
  simp only [Summary.isPure, Bool.and_eq_true, List.isEmpty_iff, List.all_eq_true] at hp
  rcases hp with ⟨⟨⟨⟨⟨⟨heff, hroot⟩, hcont⟩, hwr⟩, hret⟩, hreads⟩, henv⟩
  rw [summary_subsumes_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ h; simp [heff] at h
  · intro _ h; simp [hroot] at h
  · intro _ h; simp [hcont] at h
  · intro _ h; simp [hret] at h
  · intro _ h; simp [hwr] at h
  · intro o h; exact Or.inl (hreads o h)
  · intro o h; exact Or.inl (henv o h)

theorem foreign_read_not_erased_by_pure {pureSources : List Source} {expected actual : Summary} {o : Origin}
    (hf : o.source.kind = .foreign) (hr : o ∈ actual.namedReads)
    (hsub : expected.subsumes pureSources actual = true) :
    o ∈ expected.namedReads ∨ o ∈ expected.writes ∨ o ∈ expected.retained := by
  have h := (summary_subsumes_iff.mp hsub).namedReads o hr
  rcases h with hp | hrest
  · rw [foreign_origin_never_pure hf] at hp; contradiction
  · exact hrest

theorem retained_not_subsumed_by_write_only {pureSources : List Source} {expected actual : Summary} {o : Origin}
    (hr : o ∈ actual.retained) (hsub : expected.subsumes pureSources actual = true) :
    o ∈ expected.retained :=
  (summary_subsumes_iff.mp hsub).retained o hr

structure Crossing where
  dataAccess : List Access
  latentSources : List Origin
  scopedAuthority : Bool
  detachedResource : Bool
  explicitResourceContract : Bool
  deriving Repr, DecidableEq

def taskCrossing (c : Crossing) : Bool :=
  !c.scopedAuthority && c.latentSources.isEmpty &&
    c.dataAccess.all (fun m => decide (m = .immutable)) &&
    (!c.detachedResource || c.explicitResourceContract)

theorem task_no_live_data (h : taskCrossing c = true) (hm : m ∈ c.dataAccess) :
    m = .immutable := by
  simp only [taskCrossing, Bool.and_eq_true] at h
  exact of_decide_eq_true (List.all_eq_true.mp h.1.2 m hm)

def allocationBound : List Nat → Nat
  | [] => 0
  | x :: xs => max (x + 1) (allocationBound xs)

theorem below_allocation_bound (h : x ∈ objects) : x < allocationBound objects := by
  induction objects with
  | nil => simp at h
  | cons y ys ih =>
    have left := Nat.le_max_left (y + 1) (allocationBound ys)
    have right := Nat.le_max_right (y + 1) (allocationBound ys)
    rcases List.mem_cons.mp h with rfl | hm
    · simp only [allocationBound]
      omega
    · have hi := ih hm
      simp only [allocationBound]
      omega

def freshObject (old : List Nat) (object : Nat) : Nat := allocationBound old + object

theorem fresh_object_injective : Function.Injective (freshObject old) := by
  intro a b h
  unfold freshObject at h
  omega

/-- Alternatives retain joint output assignments instead of independent unions. -/
def correlatedSeparated (alternatives : List (List Nat × List Nat)) : Bool :=
  alternatives.all fun (a, b) => a.all fun x => decide (x ∉ b)

theorem correlated_separation_sound (h : correlatedSeparated alternatives = true)
    (ha : pair ∈ alternatives) : Separated pair.1 pair.2 := by
  have hp := List.all_eq_true.mp h pair ha
  intro x hx
  exact of_decide_eq_true (List.all_eq_true.mp hp x hx)

theorem join_preserves_common_relation (hleft : correlatedSeparated left = true)
    (hright : correlatedSeparated right = true) :
    correlatedSeparated (left ++ right) = true := by
  simp only [correlatedSeparated, List.all_append, Bool.and_eq_true]
  exact ⟨hleft, hright⟩

def disjointUnknownSelections (left right : List Nat) : Bool :=
  left.all fun x => decide (x ∉ right)

theorem disjoint_check_sound (h : disjointUnknownSelections left right = true) :
    Separated left right := by
  intro x hx
  exact of_decide_eq_true (List.all_eq_true.mp h x hx)

inductive CrossingMode where
  | immutableData
  | isolatedConstruction
  | movableEndpoint
  deriving Repr, DecidableEq

structure GraphCrossing where
  mode : CrossingMode
  dataAccess : List Access
  latentSources : List Origin
  graphOrigins : List Origin
  transferredObjects : List Nat
  writableObjects : List Nat
  callerLiveObjects : List Nat
  callerWritableObjects : List Nat
  hasExternalAlias : Bool
  scopedAuthority : Bool
  sourceConsumed : Bool
  targetScope : Nat
  explicitResourceContract : Bool
  deriving Repr, DecidableEq

def originLegalAcrossTask (explicitContract : Bool) (targetScope : Nat) (o : Origin) : Bool :=
  (decide (o.source.kind ≠ SourceKind.foreign) || explicitContract) &&
    decide (o.scope ≤ targetScope)

def graphCrossingCommon (c : GraphCrossing) : Bool :=
  !c.scopedAuthority &&
  c.latentSources.isEmpty &&
  !c.hasExternalAlias &&
  c.graphOrigins.all (originLegalAcrossTask c.explicitResourceContract c.targetScope) &&
  disjointUnknownSelections c.transferredObjects c.callerWritableObjects &&
  disjointUnknownSelections c.writableObjects c.callerLiveObjects

def graphCrossingModeValid (c : GraphCrossing) : Bool :=
  match c.mode with
  | .immutableData =>
      c.writableObjects.isEmpty &&
      c.dataAccess.all (fun m => decide (m = Access.immutable))
  | .isolatedConstruction =>
      c.sourceConsumed &&
      c.dataAccess.all (fun m => decide (m ≠ Access.ref))
  | .movableEndpoint =>
      c.sourceConsumed &&
      c.explicitResourceContract &&
      c.dataAccess.all (fun m => decide (m ≠ Access.ref ∧ m ≠ Access.shared))

def taskGraphCrossing (c : GraphCrossing) : Bool :=
  graphCrossingCommon c && graphCrossingModeValid c

theorem taskGraphCrossing_no_live_ref {c : GraphCrossing} {m : Access}
    (h : taskGraphCrossing c = true) (hm : m ∈ c.dataAccess) :
    m ≠ Access.ref := by
  simp only [taskGraphCrossing, Bool.and_eq_true] at h
  have hmode := h.2
  unfold graphCrossingModeValid at hmode
  cases hc : c.mode <;> simp only [hc, Bool.and_eq_true] at hmode
  · have himm : m = Access.immutable := of_decide_eq_true (List.all_eq_true.mp hmode.2 m hm)
    rw [himm]
    decide
  · exact of_decide_eq_true (List.all_eq_true.mp hmode.2 m hm)
  · exact (of_decide_eq_true (List.all_eq_true.mp hmode.2 m hm)).1

theorem taskGraphCrossing_writable_disjoint_caller_live {c : GraphCrossing}
    (h : taskGraphCrossing c = true) :
    Separated c.writableObjects c.callerLiveObjects := by
  simp only [taskGraphCrossing, graphCrossingCommon, Bool.and_eq_true] at h
  exact disjoint_check_sound h.1.2

theorem taskGraphCrossing_transferred_disjoint_caller_writable {c : GraphCrossing}
    (h : taskGraphCrossing c = true) :
    Separated c.transferredObjects c.callerWritableObjects := by
  simp only [taskGraphCrossing, graphCrossingCommon, Bool.and_eq_true] at h
  exact disjoint_check_sound h.1.1.2

theorem taskGraphCrossing_origin_sound {c : GraphCrossing} {o : Origin}
    (h : taskGraphCrossing c = true) (ho : o ∈ c.graphOrigins) :
    (o.source.kind ≠ SourceKind.foreign ∨ c.explicitResourceContract = true) ∧
      o.scope ≤ c.targetScope := by
  simp only [taskGraphCrossing, graphCrossingCommon, Bool.and_eq_true] at h
  have horig := List.all_eq_true.mp h.1.1.1.2 o ho
  simp only [originLegalAcrossTask, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at horig
  exact horig

structure ForeignContract where
  sources : List Source
  deriving Repr, DecidableEq

def ForeignConforms (contract : ForeignContract) (trace : List Event) : Prop :=
  ∀ e ∈ trace, e.origin.source ∈ contract.sources

theorem foreign_sources_covered (conforms : ForeignConforms contract trace)
    (he : e ∈ trace) : e.origin.source ∈ contract.sources := conforms e he

end RilAccess
