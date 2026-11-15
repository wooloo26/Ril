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

def owned (activation scope : Nat) (o : Origin) : Bool :=
  decide (o.source.kind = .allocation) && decide (o.activation = activation) &&
    decide (o.scope = scope)

def confined (activation scope : Nat) (f : Footprint) : Bool :=
  (f.roots ++ f.environments).all (owned activation scope) && f.escaping.isEmpty

def localEvent : EventKind → Bool
  | .read | .write => true
  | _ => false

def discharge (activation scope : Nat) (f : Footprint) (events : List Event) : List Event :=
  events.filter fun e =>
    !(localEvent e.kind && owned activation scope e.origin && confined activation scope f)

theorem discharge_only_confined (he : e ∈ events)
    (hn : e ∉ discharge activation scope f events) :
    localEvent e.kind = true ∧ owned activation scope e.origin = true ∧
      confined activation scope f = true := by
  simp only [discharge, List.mem_filter, Bool.not_eq_true', Bool.and_eq_false_iff,
    not_and, he, true_implies] at hn
  simp_all

theorem retained_event_survives (he : e ∈ events) (hk : localEvent e.kind = false) :
    e ∈ discharge activation scope f events := by
  simp [discharge, he, hk]

theorem confined_roots (h : confined activation scope f = true)
    (ho : o ∈ f.roots ++ f.environments) : owned activation scope o = true := by
  have hall : (f.roots ++ f.environments).all (owned activation scope) = true :=
    (by simpa only [confined, Bool.and_eq_true] using h :
      (f.roots ++ f.environments).all (owned activation scope) = true ∧
        f.escaping.isEmpty = true).1
  exact List.all_eq_true.mp hall o ho

theorem escaping_prevents_discharge (he : f.escaping ≠ []) :
    confined activation scope f = false := by
  cases h : f.escaping <;> simp_all [confined]

def FootprintCovers (abstract concrete : Footprint) : Prop :=
  (∀ o ∈ concrete.roots, o ∈ abstract.roots) ∧
  (∀ o ∈ concrete.environments, o ∈ abstract.environments) ∧
  (∀ o ∈ concrete.escaping, o ∈ abstract.escaping)

theorem confinement_from_overapproximation (cover : FootprintCovers abstract concrete)
    (h : confined activation scope abstract = true) :
    confined activation scope concrete = true := by
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
    (he : e ∈ events) (hn : e ∉ discharge activation scope abstract events) :
    e ∉ discharge activation scope concrete events := by
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

/-- Rows compare as sets: order and repeated provenance explanations are irrelevant. -/
def sameMembers [DecidableEq α] (left right : List α) : Bool :=
  left.all (fun item => decide (item ∈ right)) &&
    right.all (fun item => decide (item ∈ left))

theorem sameMembers_iff [DecidableEq α] {left right : List α} :
    sameMembers left right = true ↔ ∀ item, item ∈ left ↔ item ∈ right := by
  simp only [sameMembers, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨forward, backward⟩ item
    exact ⟨forward item, backward item⟩
  · intro h
    exact ⟨fun item hi => (h item).mp hi, fun item hi => (h item).mpr hi⟩

/-- Pure module constants require no named state clause. Pure local reads and
environment creation still require their definition-site `&up` / `&capture`. -/
def isPureModuleConstant (pureSources : List Source) (origin : Origin) : Bool :=
  decide (origin.source.kind = .module) && isPureOrigin pureSources origin

def Summary.requiredNamedReads (pureSources : List Source) (summary : Summary) : List Origin :=
  summary.namedReads.filter (fun origin => !isPureModuleConstant pureSources origin)

/-- Named definitions spell exact exercised obligations (`E0510`, `E0529`,
`E0612`). Callable upper-bound matching and pure-capture reduction are separate. -/
def Summary.exactContract (pureSources : List Source) (declared actual : Summary) : Bool :=
  sameMembers declared.effects actual.effects &&
  sameMembers declared.rootReturn actual.rootReturn &&
  sameMembers declared.contained actual.contained &&
  sameMembers declared.writes actual.writes &&
  sameMembers declared.retained actual.retained &&
  sameMembers declared.createdEnvironments actual.createdEnvironments &&
  sameMembers (declared.requiredNamedReads pureSources) (actual.requiredNamedReads pureSources)

structure SummaryExactContract (pureSources : List Source) (declared actual : Summary) : Prop where
  effects : ∀ effect, effect ∈ declared.effects ↔ effect ∈ actual.effects
  rootReturn : ∀ origin, origin ∈ declared.rootReturn ↔ origin ∈ actual.rootReturn
  contained : ∀ origin, origin ∈ declared.contained ↔ origin ∈ actual.contained
  writes : ∀ origin, origin ∈ declared.writes ↔ origin ∈ actual.writes
  retained : ∀ origin, origin ∈ declared.retained ↔ origin ∈ actual.retained
  createdEnvironments : ∀ origin,
    origin ∈ declared.createdEnvironments ↔ origin ∈ actual.createdEnvironments
  namedReads : ∀ origin,
    origin ∈ declared.requiredNamedReads pureSources ↔ origin ∈ actual.requiredNamedReads pureSources

theorem summary_exactContract_iff {pureSources : List Source} {declared actual : Summary} :
    Summary.exactContract pureSources declared actual = true ↔
      SummaryExactContract pureSources declared actual := by
  simp only [Summary.exactContract, Bool.and_eq_true, sameMembers_iff]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨effects, roots⟩, contained⟩, writes⟩, retained⟩, environments⟩, reads⟩
    exact ⟨effects, roots, contained, writes, retained, environments, reads⟩
  · intro h
    exact ⟨⟨⟨⟨⟨⟨h.effects, h.rootReturn⟩, h.contained⟩, h.writes⟩, h.retained⟩,
      h.createdEnvironments⟩, h.namedReads⟩

theorem exactContract_rejects_excess_write {pureSources : List Source}
    {declared actual : Summary} {o : Origin}
    (hdecl : o ∈ declared.writes)
    (hnoWrite : o ∉ actual.writes) :
    Summary.exactContract pureSources declared actual = false := by
  cases hex : Summary.exactContract pureSources declared actual with
  | false => rfl
  | true =>
    exact False.elim (hnoWrite (((summary_exactContract_iff.mp hex).writes o).mp hdecl))

theorem exactContract_rejects_excess_retained {pureSources : List Source}
    {declared actual : Summary} {o : Origin}
    (hdecl : o ∈ declared.retained) (hnoRetain : o ∉ actual.retained) :
    Summary.exactContract pureSources declared actual = false := by
  cases hex : Summary.exactContract pureSources declared actual with
  | false => rfl
  | true =>
    exact False.elim (hnoRetain (((summary_exactContract_iff.mp hex).retained o).mp hdecl))

theorem exactContract_rejects_missing_environment {pureSources : List Source}
    {declared actual : Summary} {o : Origin}
    (hactual : o ∈ actual.createdEnvironments) (hmissing : o ∉ declared.createdEnvironments) :
    Summary.exactContract pureSources declared actual = false := by
  cases hex : Summary.exactContract pureSources declared actual with
  | false => rfl
  | true =>
    exact False.elim (hmissing
      (((summary_exactContract_iff.mp hex).createdEnvironments o).mpr hactual))

theorem exactContract_rejects_missing_local_read {pureSources : List Source}
    {declared actual : Summary} {o : Origin}
    (hlocal : o.source.kind ≠ .module) (hactual : o ∈ actual.namedReads)
    (hmissing : o ∉ declared.namedReads) :
    Summary.exactContract pureSources declared actual = false := by
  cases hex : Summary.exactContract pureSources declared actual with
  | false => rfl
  | true =>
    have required : o ∈ actual.requiredNamedReads pureSources := by
      simp [Summary.requiredNamedReads, isPureModuleConstant, hlocal, hactual]
    have declaredRead := ((summary_exactContract_iff.mp hex).namedReads o).mpr required
    exact False.elim (hmissing (List.mem_filter.mp declaredRead).1)

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

structure ForeignContract where
  sources : List Source
  deriving Repr, DecidableEq

def ForeignConforms (contract : ForeignContract) (trace : List Event) : Prop :=
  ∀ e ∈ trace, e.origin.source ∈ contract.sources

theorem foreign_sources_covered (conforms : ForeignConforms contract trace)
    (he : e ∈ trace) : e.origin.source ∈ contract.sources := conforms e he

end RilAccess
