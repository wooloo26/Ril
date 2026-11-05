import RilAccess.Call.Entry

/-! The provenance CFG generates consistent identities. Its mechanism/context
labels are not proofs of dynamic activation freshness or source-level calls. -/
namespace RilAccess.ProvenanceIdentity

def Known (state : Configuration) (origin : Origin) : Prop :=
  (∃ register, origin ∈ state.roots register) ∨
  (∃ edge ∈ state.heap, origin = edge.parent ∨ origin = edge.child) ∨
  (∃ event ∈ state.events, origin = event.origin)

structure WorldInvariant (state : Configuration) : Prop where
  bounded : ∀ origin, Known state origin → origin.object < state.nextObject
  canonical : ∀ left right, Known state left → Known state right → left.object = right.object → left = right

theorem known_setRoot (h : Known (setRoot state register value) origin) :
    Known state origin ∨ origin = value := by
  rcases h with ⟨selected, ho⟩ | heap | events
  · by_cases he : selected = register
    · subst selected; simp [setRoot] at ho; exact Or.inr ho
    · exact Or.inl (Or.inl ⟨selected, by simpa [setRoot, he] using ho⟩)
  · exact Or.inl (Or.inr (Or.inl heap))
  · exact Or.inl (Or.inr (Or.inr events))

theorem reachable_known (hk : Known state root) (hp : Reach state.heap root target) : Known state target := by
  induction hp with
  | refl => exact hk
  | cons he _ ih => exact ih (Or.inr (Or.inl ⟨_, he, Or.inr rfl⟩))

theorem execution_origins (hx : Execute action before after) :
    (after.nextObject = before.nextObject ∧ ∀ origin, Known after origin → Known before origin) ∨
    (∃ source, after.nextObject = before.nextObject + 1 ∧
      ∀ origin, Known after origin → Known before origin ∨ origin = freshOrigin before source) := by
  cases hx with
  | seed =>
    exact Or.inr ⟨_, rfl, fun _ ho => known_setRoot ho⟩
  | copy ho =>
    refine Or.inl ⟨rfl, fun origin hk => ?_⟩
    rcases known_setRoot hk with old | rfl
    · exact old
    · exact Or.inl ⟨_, ho⟩
  | store hparent hchild =>
    refine Or.inl ⟨rfl, fun origin hk => ?_⟩
    rcases hk with root | ⟨edge, he, endpoint⟩ | events
    · exact Or.inl root
    · rcases List.mem_cons.mp he with rfl | he
      · rcases endpoint with rfl | rfl
        · exact Or.inl ⟨_, hparent⟩
        · exact Or.inl ⟨_, hchild⟩
      · exact Or.inr (Or.inl ⟨edge, (List.mem_filter.mp he).1, endpoint⟩)
    · exact Or.inr (Or.inr events)
  | project hp he _ _ =>
    refine Or.inl ⟨rfl, fun origin hk => ?_⟩
    rcases known_setRoot hk with old | rfl
    · exact old
    · exact Or.inr (Or.inl ⟨_, he, Or.inr rfl⟩)
  | emitRoot ho =>
    refine Or.inl ⟨rfl, fun origin hk => ?_⟩
    rcases hk with root | heap | ⟨event, he, rfl⟩
    · exact Or.inl root
    · exact Or.inr (Or.inl heap)
    · rcases List.mem_cons.mp he with rfl | he
      · exact Or.inl ⟨_, ho⟩
      · exact Or.inr (Or.inr ⟨event, he, rfl⟩)
  | emitDeep ho hp =>
    refine Or.inl ⟨rfl, fun origin hk => ?_⟩
    rcases hk with root | heap | ⟨event, he, rfl⟩
    · exact Or.inl root
    · exact Or.inr (Or.inl heap)
    · rcases List.mem_cons.mp he with rfl | he
      · exact reachable_known (Or.inl ⟨_, ho⟩) hp
      · exact Or.inr (Or.inr ⟨event, he, rfl⟩)
  | @enter mechanism identity state =>
    cases mechanism <;> exact Or.inl ⟨rfl, fun _ h => h⟩
  | @leave mechanism state =>
    cases mechanism <;> exact Or.inl ⟨rfl, fun _ h => h⟩
  | skip => exact Or.inl ⟨rfl, fun _ h => h⟩

theorem execution_preserves (hw : WorldInvariant before) (hx : Execute action before after) :
    WorldInvariant after := by
  rcases execution_origins hx with ⟨counter, existing⟩ | ⟨source, counter, introduced⟩
  · exact ⟨fun o ho => by rw [counter]; exact hw.bounded o (existing o ho),
      fun a b ha hb he => hw.canonical a b (existing a ha) (existing b hb) he⟩
  · constructor
    · intro origin ho
      rcases introduced origin ho with old | rfl
      · have hb := hw.bounded origin old; omega
      · simp [freshOrigin, counter]
    · intro left right hl hr he
      rcases introduced left hl with oldLeft | rfl <;>
        rcases introduced right hr with oldRight | rfl
      · exact hw.canonical _ _ oldLeft oldRight he
      · have hb := hw.bounded left oldLeft; simp only [freshOrigin] at he; omega
      · have hb := hw.bounded right oldRight; simp only [freshOrigin] at he; omega
      · rfl

theorem trace_invariant (ht : Trace program (initial program.entry) state) : WorldInvariant state := by
  have initialInvariant : WorldInvariant (initial program.entry) := by
    constructor <;> intros <;> simp [Known, initial] at *
  induction ht with
  | refl => exact initialInvariant
  | @tail middle next eventPrefix hs ih =>
    cases hs with
    | next _ _ hx _ =>
      have hd := execution_preserves ih hx
      exact ⟨hd.bounded, hd.canonical⟩

theorem metadata_coherent (hw : WorldInvariant state)
    (represented : ∀ root ∈ roots, Known state root) :
    Identity.coherent (Identity.labels state.heap roots) = true := by
  have known : ∀ origin ∈ Identity.labels state.heap roots, Known state origin := by
    intro origin ho
    rcases List.mem_append.mp (List.mem_eraseDups.mp ho) with root | edges
    · exact represented _ root
    · obtain ⟨edge, he, endpoint⟩ := List.mem_flatMap.mp edges
      simp only [List.mem_cons, List.not_mem_nil, or_false] at endpoint
      rcases endpoint with rfl | rfl
      · exact Or.inr (Or.inl ⟨edge, he, Or.inl rfl⟩)
      · exact Or.inr (Or.inl ⟨edge, he, Or.inr rfl⟩)
  apply List.all_eq_true.mpr
  intro left hl
  apply List.all_eq_true.mpr
  intro right hr
  apply decide_eq_true
  by_cases hi : left.object = right.object
  · exact Or.inr (congrArg Identity.owner (hw.canonical _ _ (known _ hl) (known _ hr) hi))
  · exact Or.inl hi

theorem cfg_entry_can_freeze (ht : Trace program (initial program.entry) state)
    (represented : ∀ root ∈ arguments.flatMap Prod.snd, Known state root) :
    ∃ frozen, CoreEntry.capturePrepared state.heap arguments = .ok frozen := by
  have consistent := metadata_coherent (trace_invariant ht) represented
  unfold CoreEntry.capturePrepared
  rw [dif_pos consistent]
  exact ⟨_, rfl⟩

end RilAccess.ProvenanceIdentity
