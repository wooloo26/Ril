import RilAccess.Provenance.Analysis

namespace RilAccess

structure HeapEdge where
  parent : Origin
  field : Nat
  child : Origin
  deriving Repr, DecidableEq

structure Event where
  kind : EventKind
  origin : Origin
  mechanism : Mechanism
  deriving Repr, DecidableEq

structure Configuration where
  pc : Option Nat
  roots : Nat → List Origin
  heap : List HeapEdge
  events : List Event
  nextObject : Nat
  activation : Nat
  task : Nat
  scope : Nat
  calls : List Nat
  handlers : List Nat
  cleanups : List Nat

def initial (entry : Nat) : Configuration :=
  ⟨some entry, fun _ => [], [], [], 0, 0, 0, 0, [], [], []⟩

def setRoot (c : Configuration) (r : Nat) (o : Origin) : Configuration :=
  { c with roots := fun n => if n = r then [o] else c.roots n }

def enterContext (c : Configuration) (m : Mechanism) (id : Nat) : Configuration :=
  match m with
  | .call | .higherOrder | .closure =>
      { c with calls := c.activation :: c.calls, activation := id }
  | .handler => { c with handlers := id :: c.handlers }
  | .cleanup | .resource => { c with cleanups := id :: c.cleanups }
  | .task => { c with task := id }
  | _ => c

def leaveContext (c : Configuration) (m : Mechanism) : Configuration :=
  match m with
  | .call | .higherOrder | .closure =>
      { c with calls := c.calls.drop 1, activation := c.calls.headD c.activation }
  | .handler => { c with handlers := c.handlers.drop 1 }
  | .cleanup | .resource => { c with cleanups := c.cleanups.drop 1 }
  | _ => c

inductive Reach (heap : List HeapEdge) : Origin → Origin → Prop where
  | refl : Reach heap x x
  | cons : e ∈ heap → Reach heap e.child y → Reach heap e.parent y

/-- Independent concrete transitions. Static inferred facts are never premises. -/
def freshOrigin (c : Configuration) (s : Source) : Origin :=
  ⟨s, c.activation, c.nextObject, c.task, c.scope⟩

inductive Execute : Action → Configuration → Configuration → Prop where
  | seed :
      Execute (.seed r s) c
        { setRoot c r (freshOrigin c s) with nextObject := c.nextObject + 1 }
  | copy : o ∈ c.roots src → Execute (.copy src to m) c (setRoot c to o)
  | store : parent ∈ c.roots a → child ∈ c.roots b →
      Execute (.store a field b) c { c with heap := (⟨parent, field, child⟩ ::
        c.heap.filter (fun e => !(e.parent == parent && e.field == field))) }
  | project : parent ∈ c.roots a → e ∈ c.heap → e.parent = parent → e.field = field →
      Execute (.project a field b) c (setRoot c b e.child)
  | emitRoot : o ∈ c.roots r →
      Execute (.emit k r false m) c { c with events := ⟨k, o, m⟩ :: c.events }
  | emitDeep : root ∈ c.roots r → Reach c.heap root o →
      Execute (.emit k r true m) c { c with events := ⟨k, o, m⟩ :: c.events }
  | enter : Execute (.enter m identity) c (enterContext c m identity)
  | leave : Execute (.leave m) c (leaveContext c m)
  | skip : Execute .skip c c

inductive Step (p : ResolvedProgram) : Configuration → Configuration → Prop where
  | next : i ∈ p.code → c.pc = some i.pc → Execute i.action c d →
      target ∈ i.next → Step p c { d with pc := target }

inductive Trace (p : ResolvedProgram) : Configuration → Configuration → Prop where
  | refl : Trace p c c
  | tail : Trace p a b → Step p b c → Trace p a c

def Matched (p : ResolvedProgram) (facts : List Fact) (c : Configuration) : Prop :=
  (∀ pc, c.pc = some pc → Fact.active pc ∈ facts) ∧
  (∀ r o, o ∈ c.roots r → o.source ∈ p.sources ∧ .root r o.source ∈ facts) ∧
  (∀ e ∈ c.heap, e.parent.source ∈ p.sources ∧ e.child.source ∈ p.sources ∧
    Fact.edge e.parent.source e.child.source ∈ facts) ∧
  (∀ e ∈ c.events, Fact.event e.kind e.origin.source ∈ facts)

variable {p : ResolvedProgram} {facts : List Fact} {c d : Configuration}
  {heap : List HeapEdge} {x y o : Origin} {i : Instruction} {a : Analysis} {e : Event}

theorem initial_matched (hc : Closed p.rules facts) : Matched p facts (initial p.entry) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro pc hp
    have he : pc = p.entry := by simpa [initial] using hp.symm
    subst pc
    apply hc ⟨[], .active p.entry⟩ (by simp [ResolvedProgram.rules])
    simp
  · simp [initial]
  · simp [initial]
  · simp [initial]

theorem reach_covered (hc : Closed p.rules facts)
    (he : ∀ e ∈ heap, e.parent.source ∈ p.sources ∧ e.child.source ∈ p.sources ∧
      Fact.edge e.parent.source e.child.source ∈ facts)
    (hx : x.source ∈ p.sources) (hr : Reach heap x y) :
    y.source ∈ p.sources ∧ Fact.descendant x.source y.source ∈ facts := by
  induction hr with
  | refl =>
    exact ⟨hx, hc ⟨[], .descendant _ _⟩ (graph_rule_mem (graph_refl_mem hx)) (by simp)⟩
  | @cons e y hem _ ih =>
    obtain ⟨hp, hchild, hedge⟩ := he e hem
    obtain ⟨hy, htail⟩ := ih hchild
    have hfirst : Fact.descendant e.parent.source e.child.source ∈ facts := by
      apply hc ⟨[.edge e.parent.source e.child.source], .descendant _ _⟩
        (graph_rule_mem (graph_edge_mem hp hchild))
      · simpa using hedge
    refine ⟨hy, hc ⟨[.descendant e.parent.source e.child.source,
      .descendant e.child.source y.source], .descendant e.parent.source y.source⟩
      (graph_rule_mem (graph_trans_mem hp hchild hy)) ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    intro f hf
    rcases hf with rfl | rfl <;> assumption

theorem setRoot_matched (hm : Matched p facts c)
    (ho : o.source ∈ p.sources ∧ Fact.root r o.source ∈ facts) :
    Matched p facts (setRoot c r o) := by
  refine ⟨hm.1, ?_, hm.2.2.1, hm.2.2.2⟩
  intro n x hx
  by_cases hn : n = r
  · subst n
    simp [setRoot] at hx
    subst x
    exact ho
  · exact hm.2.1 n x (by simpa [setRoot, hn] using hx)

theorem execute_preserves (hc : Closed p.rules facts) (hi : i ∈ p.code)
    (ha : Fact.active i.pc ∈ facts) (hm : Matched p facts c)
    (hx : Execute i.action c d) : Matched p facts d := by
  generalize heq : i.action = action at hx
  have rule (r) (hr : r ∈ actionRules p.sources i.pc action)
      (hp : ∀ f ∈ r.premises, f ∈ facts) : r.conclusion ∈ facts :=
    hc r (action_rule_mem hi (by simpa [heq] using hr)) hp
  cases hx with
  | @seed register source c =>
    have hs := seed_source_mem hi heq
    have hf := rule ⟨[.active i.pc], .root register source⟩
      (by simp [actionRules]) (by simpa using ha)
    exact setRoot_matched hm ⟨hs, hf⟩
  | @copy o src to m c ho =>
    obtain ⟨hs, hf⟩ := hm.2.1 src o ho
    apply setRoot_matched hm
    refine ⟨hs, rule ⟨[.active i.pc, .root src o.source], .root to o.source⟩
      (by exact List.mem_map.mpr ⟨o.source, hs, rfl⟩) ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    intro f hf'
    rcases hf' with rfl | rfl <;> assumption
  | @store parent child a field b c hparent hchild =>
    obtain ⟨hs, hp⟩ := hm.2.1 a parent hparent
    obtain ⟨ht, hch⟩ := hm.2.1 b child hchild
    refine ⟨hm.1, hm.2.1, ?_, hm.2.2.2⟩
    intro e hem
    rcases List.mem_cons.mp hem with rfl | hem
    · refine ⟨hs, ht, rule ⟨[.active i.pc, .root a parent.source, .root b child.source],
        .edge parent.source child.source⟩ (by
          exact List.mem_flatMap.mpr ⟨parent.source, hs,
            List.mem_map.mpr ⟨child.source, ht, rfl⟩⟩) ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      intro f hf
      rcases hf with rfl | rfl | rfl <;> assumption
    · exact hm.2.2.1 e (List.mem_filter.mp hem).1
  | @project parent e field a b c hp hem hep _ =>
    obtain ⟨hs, hf⟩ := hm.2.1 a parent hp
    obtain ⟨_, ht, hedge⟩ := hm.2.2.1 e hem
    rw [hep] at hedge
    apply setRoot_matched hm
    refine ⟨ht, rule ⟨[.active i.pc, .root a parent.source,
      .edge parent.source e.child.source], .root b e.child.source⟩
      (by exact List.mem_flatMap.mpr ⟨parent.source, hs,
        List.mem_map.mpr ⟨e.child.source, ht, rfl⟩⟩) ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    intro f hf'
    rcases hf' with rfl | rfl | rfl <;> assumption
  | @emitRoot o k r m c ho =>
    obtain ⟨hs, hf⟩ := hm.2.1 r o ho
    refine ⟨hm.1, hm.2.1, hm.2.2.1, ?_⟩
    intro e hem
    rcases List.mem_cons.mp hem with rfl | hem
    · apply rule ⟨[.active i.pc, .root r o.source], .event k o.source⟩
        (by exact List.mem_map.mpr ⟨o.source, hs, rfl⟩)
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      intro f hf'
      rcases hf' with rfl | rfl <;> assumption
    · exact hm.2.2.2 e hem
  | @emitDeep root o k r m c hroot hreach =>
    obtain ⟨hs, hf⟩ := hm.2.1 r root hroot
    obtain ⟨ht, hdesc⟩ := reach_covered hc hm.2.2.1 hs hreach
    refine ⟨hm.1, hm.2.1, hm.2.2.1, ?_⟩
    intro e hem
    rcases List.mem_cons.mp hem with rfl | hem
    · apply rule ⟨[.active i.pc, .root r root.source,
        .descendant root.source o.source], .event k o.source⟩
        (by exact List.mem_flatMap.mpr ⟨root.source, hs,
          List.mem_map.mpr ⟨o.source, ht, rfl⟩⟩)
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      intro f hf'
      rcases hf' with rfl | rfl | rfl <;> assumption
    · exact hm.2.2.2 e hem
  | enter =>
    unfold enterContext
    split <;> exact hm
  | leave =>
    unfold leaveContext
    split <;> exact hm
  | skip => exact hm

theorem step_preserves (hc : Closed p.rules facts) (hm : Matched p facts c)
    (hs : Step p c d) : Matched p facts d := by
  cases hs with
  | @next i c d target hi hpc hex hn =>
    have ha := hm.1 i.pc hpc
    have hd := execute_preserves hc hi ha hm hex
    refine ⟨?_, hd.2⟩
    intro pc heq
    have ht : target = some pc := heq
    have hr : Rule.mk [.active i.pc] (.active pc) ∈ p.rules := by
      apply instruction_rule_mem hi
      apply List.mem_append_right
      apply List.mem_flatMap.mpr
      exact ⟨target, hn, by simp [ht]⟩
    exact hc _ hr (by simpa using ha)

theorem trace_preserves (hc : Closed p.rules facts) (hm : Matched p facts c)
    (ht : Trace p c d) : Matched p facts d := by
  induction ht with
  | refl => exact hm
  | tail _ step ih => exact step_preserves hc ih step

/-- Covers every event in every finite prefix, including exceptional exits. -/
theorem provenance_coverage (ha : analyze p = .ok a)
    (ht : Trace p (initial p.entry) c) (he : e ∈ c.events) :
    Fact.event e.kind e.origin.source ∈ a.facts :=
  (trace_preserves (analyze_least ha).1 (initial_matched (analyze_least ha).1) ht).2.2.2 e he

theorem program_point_coverage (ha : analyze p = .ok a)
    (ht : Trace p (initial p.entry) c) (hpc : c.pc = some pc)
    (ho : o ∈ c.roots register) : Fact.root register o.source ∈ a.at pc := by
  have hm := trace_preserves (analyze_least ha).1 (initial_matched (analyze_least ha).1) ht
  simp only [Analysis.at, if_pos (hm.1 pc hpc)]
  exact (hm.2.1 register o ho).2

theorem forbidden_event_unreachable (ha : analyze p = .ok a)
    (hcheck : Check.absent (.event k s) ∈ p.checks)
    (ht : Trace p (initial p.entry) c) (he : e ∈ c.events)
    (hk : e.kind = k) (hs : e.origin.source = s) : False := by
  have hn := analyze_checks ha hcheck
  have hf := provenance_coverage ha ht he
  simp only [checkHolds, decide_eq_true_eq] at hn
  exact hn (by simpa [hk, hs] using hf)

end RilAccess
