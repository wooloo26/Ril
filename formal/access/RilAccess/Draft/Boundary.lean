import RilAccess.Draft.Proofs

namespace RilAccess.Draft

variable {input : Input} {world next start finish : World} {command : Command}
  {program : List Command} {event : Event} {observation : ExternalObservation}

theorem step_logs (h : step command world = some next) :
    (∀ event ∈ world.events, event ∈ next.events) ∧ (∀ effect ∈ world.effects, effect ∈ next.effects) := by
  obtain ⟨events, he, _⟩ := (step_facts h).eventDelta
  obtain ⟨effects, hf⟩ := (step_facts h).effectDelta
  exact ⟨fun _ hx => he ▸ List.mem_append_right _ hx, fun _ hx => hf ▸ List.mem_append_right _ hx⟩

theorem trace_logs (ht : Trace program start finish) :
    (∀ event ∈ start.events, event ∈ finish.events) ∧ (∀ effect ∈ start.effects, effect ∈ finish.effects) := by
  induction ht with
  | refl => exact ⟨fun _ he => he, fun _ he => he⟩
  | tail _ _ hs ih =>
    exact ⟨fun e he => (step_logs hs).1 e (ih.1 e he), fun e he => (step_logs hs).2 e (ih.2 e he)⟩

theorem external_state_survives (hs : step (.external observation) world = some next)
    (ht : Trace program next finish) (he : event ∈ observation.events) : event ∈ finish.outward := by
  obtain ⟨facts, hn⟩ := checked_external hs
  have present : event ∈ finish.events :=
    (trace_logs ht).1 event (by rw [hn]; exact List.mem_append_left _ he)
  have hi : finish.input = world.input := (trace_frame ht).1.trans (by rw [hn]; rfl)
  unfold World.outward
  split
  · apply List.mem_filter.mpr
    refine ⟨present, ?_⟩
    simp only [hi, (facts.events event he).2, Bool.and_false, Bool.false_and, Bool.not_false]
  · exact present

theorem abort_preserves_state (h : step (.finish .abort) world = some next) :
    next.output = none ∧ next.active = false ∧ next.events = world.events ∧
      next.effects = world.effects ∧ next.memory = world.memory := by
  have he := (checked_step h).2
  simp only [execute, Option.some.injEq] at he
  cases he
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

structure PublishedFacts (world : World) (published : Published) : Prop where
  immutable : published.access = .immutable
  closed : world.active = false
  present : ∃ cell, world.memory published.object = some cell
  root : published.object = world.input.root ∨ published.object = counterpart world.input world.input.root

def OutputSafe (world : World) : Prop := ∀ published, world.output = some published → PublishedFacts world published

theorem step_output_safe (h : step command world = some next) (hw : OutputSafe world) : OutputSafe next := by
  have priorNone : world.output = none := by
    cases ho : world.output with
    | none => rfl
    | some published =>
      have closed := (hw published ho).closed
      simp [checked_active h] at closed
  cases command with
  | rewrite object values =>
    obtain ⟨_, _, _, _, _, _, rfl⟩ := checked_rewrite h
    intro published hp; simp [rewritten, priorNone] at hp
  | allocate storage values =>
    obtain ⟨_, _, _, _, _, rfl⟩ := checked_allocate h
    intro published hp; simp [allocated, priorNone] at hp
  | external observation =>
    obtain ⟨_, rfl⟩ := checked_external h
    intro published hp; simp [observed, priorNone] at hp
  | effect effect =>
    have he := (checked_step h).2
    simp only [execute, Option.some.injEq] at he
    cases he
    intro published hp; simp [priorNone] at hp
  | finish reason =>
    have he := (checked_step h).2
    have ha := (checked_step h).1
    simp only [execute, Option.some.injEq] at he
    cases he
    cases reason with
    | abort => intro published hp; simp [finished] at hp
    | normal =>
      intro published hp
      simp only [finished, Option.some.injEq] at hp
      cases hp
      refine ⟨rfl, rfl, ?_, ?_⟩
      · simp only [admissible, Bool.and_eq_true] at ha
        cases hm : world.memory (if world.dirty then counterpart world.input world.input.root else world.input.root) with
        | none => simp [hm] at ha
        | some cell => exact ⟨cell, hm⟩
      · cases world.dirty <;> simp [finished]

theorem trace_output_safe (hp : prepare input = some start) (ht : Trace program start finish) : OutputSafe finish := by
  have initialSafe : OutputSafe start := by
    obtain ⟨_, rfl⟩ := prepared hp
    intro published hp; contradiction
  induction ht with
  | refl => exact initialSafe
  | tail _ _ hs ih => exact step_output_safe hs ih

theorem publication_ends_privilege (hp : prepare input = some start)
    (ht : Trace program start finish) (ho : finish.output = some published) :
    published.access = .immutable ∧ finish.active = false ∧
      (∀ command, step command finish = none) ∧ ∃ cell, finish.memory published.object = some cell := by
  have facts := trace_output_safe hp ht published ho
  exact ⟨facts.immutable, facts.closed, fun _ => closed_no_step facts.closed, facts.present⟩

theorem private_draft_region (hp : prepare input = some start) (ht : Trace program start finish)
    (ho : object ∈ finish.draftObjects) : finish.input.bound ≤ object :=
  private_bounds (trace_invariant hp ht).locals ho

/-- Complete footprints include contained/captured/retained references, not just
the event's top-level object. Unknown footprints never establish conformance. -/
theorem conforming_external_cannot_escape (hp : prepare input = some start)
    (ht : Trace program start finish) (hs : step (.external observation) finish = some next)
    (conforms : ExternalConforms observation actualEvents actualEffects actualFootprint)
    (ho : origin ∈ actualFootprint.roots ++ actualFootprint.environments ++ actualFootprint.escaping) :
    origin.object ∉ finish.draftObjects := by
  obtain ⟨footprint, known, safe⟩ := (checked_external hs).1.footprint
  have covers : FootprintCovers footprint actualFootprint := by
    simpa only [ExternalConforms, known] using conforms.2.2
  have included : origin ∈ footprint.roots ++ footprint.environments ++ footprint.escaping := by
    rcases List.mem_append.mp ho with prior | escaped
    · rcases List.mem_append.mp prior with root | env
      · exact List.mem_append_left _ (List.mem_append_left _ (covers.1 _ root))
      · exact List.mem_append_left _ (List.mem_append_right _ (covers.2.1 _ env))
    · exact List.mem_append_right _ (covers.2.2 _ escaped)
  have below := below_allocation_bound (safe origin included).1
  intro inRegion
  have above := private_draft_region hp ht inRegion
  unfold Input.bound at above
  omega

theorem publication_root (hp : prepare input = some start) (ht : Trace program start finish)
    (ho : finish.output = some published) :
    published.object = input.root ∨ published.object = counterpart input input.root := by
  have same : finish.input = input := (trace_frame ht).1.trans (congrArg World.input (prepared hp).2)
  simpa only [same] using (trace_output_safe hp ht published ho).root

theorem published_schema_preserved (hp : prepare input = some start)
    (ht : Trace program start finish) (hr : lookup input.pool input.root = some source)
    (ho : finish.output = some published) :
    ∃ cell, finish.memory published.object = some cell ∧ cell.storage = source.storage := by
  rcases publication_root hp ht ho with original | copied
  · have hm : start.memory input.root = some source := by
      rw [(prepared hp).2]; exact original_lookup (prepared hp).1 hr
    obtain ⟨cell, hc, _, schema⟩ := trace_identity ht hm
    exact ⟨cell, original.symm ▸ hc, schema⟩
  · obtain ⟨cell, hc, _, schema⟩ := source_counterpart_persists hp ht hr
    exact ⟨cell, copied.symm ▸ hc, schema⟩

def SourcesCovered (heap : Heap) (sources : List Source) : Prop :=
  ∀ object cell, heap object = some cell → cell.origin.source ∈ sources

theorem initial_sources : SourcesCovered (initialHeap input) input.sources := by
  intro object cell hc
  unfold initialHeap at hc
  split at hc
  · exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨cell, (lookup_present hc).1, rfl⟩)
  · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hc; exact List.mem_cons_self

theorem step_sources (h : step command world = some next)
    (hp : world.input.context.source ∈ sources) (hw : SourcesCovered world.memory sources) :
    SourcesCovered next.memory sources := by
  cases (step_facts h).heap with
  | stable memory => simpa [memory] using hw
  | @rewrite address previous values hm _ _ _ memory =>
    intro object cell hc
    by_cases he : object = address
    · subst object
      have eq : { previous with contents := values } = cell := by simpa [memory, put] using hc
      cases eq
      exact hw address previous hm
    · exact hw object cell (by simpa [memory, put, he] using hc)
  | @allocate layout values _ _ _ _ _ memory =>
    intro object cell hc
    by_cases he : object = world.nextObject
    · subst object
      have eq : Cell.mk (world.input.context.origin world.nextObject) layout values = cell := by simpa [memory, put] using hc
      cases eq; exact hp
    · exact hw object cell (by simpa [memory, put, he] using hc)

theorem trace_sources (hp : prepare input = some start) (ht : Trace program start finish) :
    SourcesCovered finish.memory input.sources := by
  have hi : start.input = input := congrArg World.input (prepared hp).2
  have initialSources : SourcesCovered start.memory input.sources := by rw [(prepared hp).2]; exact initial_sources
  induction ht with
  | refl => exact initialSources
  | tail earlier _ hs ih =>
    apply step_sources hs ?_ ih
    rw [(trace_frame earlier).1, hi]; exact List.mem_cons_self

theorem published_sources_covered (hp : prepare input = some start)
    (ht : Trace program start finish) (ho : finish.output = some published) :
    ∃ cell, finish.memory published.object = some cell ∧ cell.origin.source ∈ input.sources := by
  obtain ⟨cell, hc⟩ := (trace_output_safe hp ht published ho).present
  exact ⟨cell, hc, trace_sources hp ht _ _ hc⟩

theorem command_fact_covered (hc : command ∈ program)
    (hf : fact ∈ (commandRules input command).map Rule.conclusion) : fact ∈ analyze input program := by
  obtain ⟨rule, hr, rfl⟩ := List.mem_map.mp hf
  have empty : rule.premises = [] := by
    cases command with
    | external observation => obtain ⟨_, _, rfl⟩ := List.mem_map.mp hr; rfl
    | rewrite _ _ => simp only [commandRules, List.mem_singleton] at hr; cases hr; rfl
    | allocate _ _ => simp only [commandRules, List.mem_singleton] at hr; cases hr; rfl
    | effect _ => simp [commandRules] at hr
    | finish _ => simp [commandRules] at hr
  exact solve_closed rule (List.mem_flatMap.mpr ⟨command, hc, hr⟩) (by simp [empty])

theorem recipe_source_coverage (hp : prepare input = some start) (ht : Trace program start finish)
    (he : event ∈ finish.events) : Fact.event event.kind event.origin.source ∈ analyze input program := by
  have hi : start.input = input := congrArg World.input (prepared hp).2
  induction ht with
  | refl => rw [(prepared hp).2] at he; contradiction
  | tail earlier hc hs ih =>
    obtain ⟨added, delta, rules⟩ := (step_facts hs).eventDelta
    rw [delta] at he
    rcases List.mem_append.mp he with fresh | prior
    · have rule := rules event fresh
      rw [(trace_frame earlier).1, hi] at rule
      exact command_fact_covered hc rule
    · exact ih prior

theorem run_checked_simulates (h : runChecked program start = some finish) : runUnchecked program start = some finish := by
  induction program generalizing start with
  | nil => exact h
  | cons command rest ih =>
    cases hs : step command start with
    | none => simp [runChecked, hs] at h
    | some middle =>
      have remaining : runChecked rest middle = some finish := by simpa [runChecked, hs] using h
      simpa [runUnchecked, (checked_step hs).2] using ih remaining

theorem Trace.trans (first : Trace program a b) (second : Trace program b c) : Trace program a c := by
  induction second with
  | refl => exact first
  | tail _ hc hs ih => exact .tail ih hc hs

theorem run_checked_trace (h : runChecked commands start = some finish)
    (included : ∀ command ∈ commands, command ∈ program) : Trace program start finish := by
  induction commands generalizing start with
  | nil => simp [runChecked] at h; cases h; exact .refl
  | cons command rest ih =>
    cases hs : step command start with
    | none => simp [runChecked, hs] at h
    | some middle =>
      have remaining : runChecked rest middle = some finish := by simpa [runChecked, hs] using h
      exact (Trace.tail Trace.refl (included _ (by simp)) hs).trans
        (ih remaining (fun command hm => included _ (List.mem_cons_of_mem _ hm)))

theorem checked_recipe (h : check input program = some analysis) :
    ∃ start, prepare input = some start ∧ runChecked program start = some analysis.result ∧
      runUnchecked program start = some analysis.result ∧ Trace program start analysis.result ∧
      analysis.result.active = false ∧ analysis.facts = analyze input program := by
  cases hp : prepare input with
  | none => simp [check, hp] at h
  | some start =>
    cases hr : runChecked program start with
    | none => simp [check, hp, hr] at h
    | some finish =>
      simp only [check, hp, GraphAuthority.option_bind_some, hr] at h
      change (if finish.active then none else _) = some analysis at h
      split at h
      · contradiction
      · rename_i closed
        have hc : finish.active = false := by simpa using closed
        cases h
        exact ⟨start, rfl, hr, run_checked_simulates hr, run_checked_trace hr (fun _ hm => hm), hc, rfl⟩


/-- A prefix of the independent, unchecked sequential execution. -/
inductive Prefix : List Command → World → World → Prop where
  | here {program : List Command} {state : World} : Prefix program state state
  | next {command : Command} {rest : List Command} {before after middle : World} :
      execute command before = some after → Prefix rest after middle → Prefix (command :: rest) before middle

theorem checked_prefix_trace (complete : runChecked commands start = some finish)
    (hp : Prefix commands start middle)
    (included : ∀ command ∈ commands, command ∈ program) : Trace program start middle := by
  induction hp generalizing finish with
  | here => exact .refl
  | @next command rest before after middle executed earlier ih =>
    cases hs : step command before with
    | none => simp [runChecked, hs] at complete
    | some checked =>
      have eq : checked = after := Option.some.inj ((checked_step hs).2.symm.trans executed)
      cases eq
      have tailComplete : runChecked rest after = some finish := by simpa [runChecked, hs] using complete
      exact (Trace.tail Trace.refl (included _ (by simp)) hs).trans
        (ih tailComplete (fun command hc => included _ (List.mem_cons_of_mem _ hc)))

/-- Principal finite-recipe result: every actual unchecked prefix inherits the
invariant and source coverage, rather than merely agreeing at the final state. -/
theorem checked_recipe_prefixes (h : check input program = some analysis) :
    ∃ start, prepare input = some start ∧
      ∀ middle, Prefix program start middle →
        WorldInvariant input middle ∧ SourcesCovered middle.memory input.sources ∧
          ∀ event ∈ middle.events, Fact.event event.kind event.origin.source ∈ analysis.facts := by
  obtain ⟨start, hp, completed, _, _, _, hf⟩ := checked_recipe h
  refine ⟨start, hp, fun middle prefixTrace => ?_⟩
  have ht := checked_prefix_trace completed prefixTrace (fun _ hc => hc)
  exact ⟨trace_invariant hp ht, trace_sources hp ht, fun event he => hf ▸ recipe_source_coverage hp ht he⟩

end RilAccess.Draft
