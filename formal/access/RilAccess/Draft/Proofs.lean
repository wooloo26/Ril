import RilAccess.Draft.Core

namespace RilAccess.Draft

variable {input : Input} {pool : List Cell} {object old : Nat} {cell : Cell}
  {world next start finish : World} {command : Command} {contents : List Value}
  {storage : Storage} {program : List Command}

structure InputFacts (input : Input) : Prop where
  objects : (input.pool.map (fun cell => cell.origin.object)).Nodup
  cells : ∀ cell ∈ input.pool, cell.origin.object ∈ input.reserved ∧
    owned input.context.activation input.context.task input.context.scope cell.origin = false ∧
    contentsFit (lookup input.pool) cell.storage cell.contents = true
  root : (lookup input.pool input.root).isSome = true
  authority : GraphAuthority.immutableConsistent input.authorityGraph = true
  reserved : input.authoritiesReserved = true
  schemas : input.schemasValid = true
  receptions : input.receptionsValid = true

theorem input_facts (h : input.valid = true) : InputFacts input := by
  simp only [Input.valid, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨h.1.1.1.1, ?_, h.1.1.2, h.1.2, h.2.1, h.2.2.1, h.2.2.2⟩
  intro cell hc
  simpa only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, and_assoc] using
    List.all_eq_true.mp h.1.1.1.2 cell hc

theorem prepared (h : prepare input = some world) :
    input.valid = true ∧ world =
      { input := input, memory := initialHeap input, nextObject := input.bound + input.bound } := by
  unfold prepare at h
  split at h
  · rename_i hv; cases h; exact ⟨hv, rfl⟩
  · contradiction

theorem valid_cell (h : input.valid = true) (hc : cell ∈ input.pool) :
    cell.origin.object ∈ input.reserved ∧ contentsFit (lookup input.pool) cell.storage cell.contents = true :=
  ⟨((input_facts h).cells _ hc).1, ((input_facts h).cells _ hc).2.2⟩

theorem lookup_present (h : lookup pool object = some cell) :
    cell ∈ pool ∧ cell.origin.object = object :=
  ⟨List.mem_of_find?_eq_some h, of_decide_eq_true
    (List.find?_some (p := fun candidate : Cell => decide (candidate.origin.object = object)) h)⟩

theorem initial_counterpart (h : lookup input.pool object = some cell) :
    initialHeap input (counterpart input object) = some (copyCell input cell) := by
  unfold initialHeap
  rw [if_neg (show ¬counterpart input object < input.bound by unfold counterpart; omega)]
  simp [counterpart, h]

inductive Path (heap : Heap) : Nat → List Nat → Nat → Prop where
  | here {object : Nat} : Path heap object [] object
  | next {object child target index : Nat} {cell : Cell} {rest : List Nat} :
      heap object = some cell → cell.contents[index]? = some (.reference child) →
      Path heap child rest target → Path heap object (index :: rest) target

theorem copy_preserves_paths (hp : Path (lookup input.pool) object fields target) :
    Path (initialHeap input) (counterpart input object) fields (counterpart input target) := by
  induction hp with
  | here => exact .here
  | next hm hv _ ih =>
    apply Path.next (initial_counterpart hm) ?_ ih
    simp [copyCell, List.getElem?_map, hv, renameValue]

theorem counterpart_fresh (ho : old ∈ input.reserved) : counterpart input object ≠ old := by
  have hb := below_allocation_bound ho
  unfold counterpart Input.bound
  omega

theorem counterpart_injective : Function.Injective (counterpart input) := by
  intro a b he; unfold counterpart at he; omega

structure ObservationFacts (input : Input) (observation : ExternalObservation) : Prop where
  footprint : ∃ footprint, observation.footprint = .known footprint ∧
    ∀ origin ∈ footprint.roots ++ footprint.environments ++ footprint.escaping,
      origin.object ∈ input.reserved ∧ owned input.context.activation input.context.task input.context.scope origin = false
  events : ∀ event ∈ observation.events, event.origin.object ∈ input.reserved ∧
    owned input.context.activation input.context.task input.context.scope event.origin = false

theorem observation_facts (h : observationAllowed input observation = true) :
    ObservationFacts input observation := by
  cases hf : observation.footprint with
  | unresolved obligations => simp [observationAllowed, hf] at h
  | known footprint =>
    simp only [observationAllowed, hf, Bool.and_eq_true] at h
    constructor
    · refine ⟨footprint, hf, fun origin ho => ?_⟩
      simpa only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] using
        List.all_eq_true.mp h.1.2 origin ho
    · intro event he
      have checks := List.all_eq_true.mp h.1.1 event he
      simp only [eventAllowed, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at checks
      exact ⟨checks.1.1.1, checks.1.2⟩

inductive HeapChange (before after : World) : Prop where
  | stable : after.memory = before.memory → HeapChange before after
  | rewrite {address : Nat} {previous : Cell} {values : List Value} :
      before.memory address = some previous → before.input.bound ≤ address →
      contentsFit before.memory previous.storage values = true →
      values.all (confinedValue before) = true →
      after.memory = put before.memory address { previous with contents := values } → HeapChange before after
  | allocate {layout : Storage} {values : List Value} :
      before.input.bound ≤ before.nextObject → before.memory before.nextObject = none →
      layout ∈ before.input.schemas → contentsFit after.memory layout values = true →
      values.all (confinedValue (allocated before layout values)) = true →
      after.memory = put before.memory before.nextObject ⟨before.input.context.origin before.nextObject, layout, values⟩ →
      HeapChange before after

/-- Local operational evidence decoded once. No global safety predicate is an
input to the executable checker. Trace invariants are proved from these deltas. -/
structure StepFacts (before : World) (command : Command) (after : World) : Prop where
  executed : execute command before = some after
  active : before.active = true
  input : after.input = before.input
  heap : HeapChange before after
  locals : after.locals = before.locals ∨
    (after.locals = before.nextObject :: before.locals ∧ before.input.bound ≤ before.nextObject)
  eventDelta : ∃ added, after.events = added ++ before.events ∧
    ∀ event ∈ added, Fact.event event.kind event.origin.source ∈ (commandRules before.input command).map Rule.conclusion
  effectDelta : ∃ added, after.effects = added ++ before.effects
  knownPreserved : before.observations.all ExternalObservation.known = true →
    after.observations.all ExternalObservation.known = true

theorem checked_step (h : step command world = some next) :
    admissible command world = true ∧ execute command world = some next := by
  unfold step at h
  split at h
  · exact ⟨by assumption, h⟩
  · contradiction

theorem checked_active (h : step command world = some next) : world.active = true := by
  have ha := (checked_step h).1
  simp only [admissible, Bool.and_eq_true] at ha
  exact ha.1

theorem closed_no_step (ha : world.active = false) : step command world = none := by simp [step, admissible, ha]

theorem checked_rewrite (h : step (.rewrite object contents) world = some next) :
    ∃ cell, world.memory object = some cell ∧ world.input.bound ≤ object ∧
      cell.origin = world.input.context.origin object ∧
      contentsFit world.memory cell.storage contents = true ∧
      contents.all (confinedValue world) = true ∧ next = rewritten world object cell contents := by
  obtain ⟨ha, he⟩ := checked_step h
  simp only [admissible, Bool.and_eq_true] at ha
  obtain ⟨cell, hm, hc⟩ := Option.any_eq_true _ _ |>.mp ha.2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  exact ⟨cell, hm, hc.1.1.1.2, hc.1.1.2, hc.1.2, hc.2, by simpa [execute, hm] using he.symm⟩

theorem checked_allocate (h : step (.allocate storage contents) world = some next) :
    world.input.bound ≤ world.nextObject ∧ world.memory world.nextObject = none ∧
      storage ∈ world.input.schemas ∧ contentsFit next.memory storage contents = true ∧
      contents.all (confinedValue (allocated world storage contents)) = true ∧ next = allocated world storage contents := by
  obtain ⟨ha, he⟩ := checked_step h
  simp only [admissible, Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none] at ha
  have hn : next = allocated world storage contents := by simpa [execute] using he.symm
  exact ⟨ha.2.2.1.1.1, ha.2.2.1.1.2, ha.2.1, by simpa [hn] using ha.2.2.1.2, ha.2.2.2, hn⟩

theorem checked_external (h : step (.external observation) world = some next) :
    ObservationFacts world.input observation ∧ next = observed world observation := by
  obtain ⟨ha, he⟩ := checked_step h
  simp only [admissible, Bool.and_eq_true] at ha
  exact ⟨observation_facts ha.2, by simpa [execute] using he.symm⟩

theorem step_facts (h : step command world = some next) : StepFacts world command next := by
  have executed := (checked_step h).2
  have active := checked_active h
  cases command with
  | rewrite object values =>
    obtain ⟨cell, hm, hb, ho, typed, refs, rfl⟩ := checked_rewrite h
    refine ⟨executed, active, rfl, .rewrite hm hb typed refs rfl, Or.inl rfl,
      ⟨[⟨.write, cell.origin, .derive⟩], rfl, ?_⟩, ⟨[], rfl⟩, fun x => x⟩
    intro event he
    have eq : event = ⟨.write, cell.origin, .derive⟩ := by simpa using he
    subst event
    simp [commandRules, ho, Context.origin]
  | allocate storage values =>
    obtain ⟨hb, hn, schema, typed, refs, rfl⟩ := checked_allocate h
    refine ⟨executed, active, rfl, .allocate hb hn schema typed refs rfl, Or.inr ⟨rfl, hb⟩,
      ⟨[⟨.write, world.input.context.origin world.nextObject, .derive⟩], rfl, ?_⟩,
      ⟨[], rfl⟩, fun x => x⟩
    intro event he
    have eq : event = ⟨.write, world.input.context.origin world.nextObject, .derive⟩ := by simpa using he
    subst event
    simp [commandRules, Context.origin]
  | external observation =>
    obtain ⟨facts, rfl⟩ := checked_external h
    have known : observation.known = true := by obtain ⟨fp, hf, _⟩ := facts.footprint; simp [ExternalObservation.known, hf]
    refine ⟨executed, active, rfl, .stable rfl, Or.inl rfl, ⟨observation.events, rfl, ?_⟩,
      ⟨observation.effects, rfl⟩, ?_⟩
    · intro event he
      exact List.mem_map.mpr ⟨⟨[], .event event.kind event.origin.source⟩,
        List.mem_map.mpr ⟨event, he, rfl⟩, rfl⟩
    · intro previous; simp [observed, known, previous]
  | effect effect =>
    simp only [execute, Option.some.injEq] at executed
    cases executed
    exact ⟨rfl, active, rfl, .stable rfl, Or.inl rfl, ⟨[], rfl, by simp⟩, ⟨[effect], rfl⟩, fun x => x⟩
  | finish reason =>
    simp only [execute, Option.some.injEq] at executed
    cases executed
    exact ⟨rfl, active, rfl, .stable rfl, Or.inl rfl, ⟨[], rfl, by simp⟩, ⟨[], rfl⟩, fun x => x⟩

theorem step_frame (h : step command world = some next) :
    next.input = world.input ∧ ∀ object, object < world.input.bound → next.memory object = world.memory object := by
  have facts := step_facts h
  refine ⟨facts.input, fun object ho => ?_⟩
  cases facts.heap with
  | stable he => rw [he]
  | @rewrite address previous values _ hb _ _ he =>
    rw [he]; simp [put, show object ≠ address by omega]
  | allocate hb _ _ _ _ he =>
    rw [he]; simp [put, show object ≠ world.nextObject by omega]

theorem trace_frame (ht : Trace program start finish) :
    finish.input = start.input ∧ ∀ object, object < start.input.bound → finish.memory object = start.memory object := by
  induction ht with
  | refl => exact ⟨rfl, fun _ _ => rfl⟩
  | tail _ _ hs ih =>
    obtain ⟨hi, hm⟩ := step_frame hs
    exact ⟨hi.trans ih.1, fun object ho => (hm object (by simpa [ih.1] using ho)).trans (ih.2 object ho)⟩

theorem base_snapshot_preserved (hp : prepare input = some start) (ht : Trace program start finish) (hc : cell ∈ input.pool) :
    finish.memory cell.origin.object = lookup input.pool cell.origin.object := by
  obtain ⟨hv, he⟩ := prepared hp
  have hb := below_allocation_bound (valid_cell hv hc).1
  have hm := (trace_frame ht).2
  rw [he] at hm
  rw [hm cell.origin.object hb]
  simp [initialHeap, Input.bound, hb]

theorem step_identity (h : step command world = some next) (hc : world.memory object = some cell) :
    ∃ current, next.memory object = some current ∧ current.origin = cell.origin ∧ current.storage = cell.storage := by
  cases (step_facts h).heap with
  | stable he => exact ⟨cell, he ▸ hc, rfl, rfl⟩
  | @rewrite address previous values hm _ _ _ he =>
    by_cases eq : object = address
    · subst object
      have same : cell = previous := Option.some.inj (hc.symm.trans hm)
      subst cell
      exact ⟨{ previous with contents := values }, by simp [he, put], rfl, rfl⟩
    · exact ⟨cell, by simpa [he, put, eq] using hc, rfl, rfl⟩
  | allocate _ missing _ _ _ he =>
    have different : object ≠ world.nextObject := by intro eq; subst object; rw [missing] at hc; contradiction
    exact ⟨cell, by simpa [he, put, different] using hc, rfl, rfl⟩

theorem trace_identity (ht : Trace program start finish) (hc : start.memory object = some cell) :
    ∃ current, finish.memory object = some current ∧ current.origin = cell.origin ∧ current.storage = cell.storage := by
  induction ht with
  | refl => exact ⟨cell, hc, rfl, rfl⟩
  | tail _ _ hs ih =>
    obtain ⟨middle, hm, ho, ht⟩ := ih
    obtain ⟨last, hl, hlo, hlt⟩ := step_identity hs hm
    exact ⟨last, hl, hlo.trans ho, hlt.trans ht⟩

theorem source_counterpart_persists (hp : prepare input = some start) (ht : Trace program start finish)
    (hc : lookup input.pool object = some cell) :
    ∃ current, finish.memory (counterpart input object) = some current ∧
      current.origin = input.context.origin (counterpart input object) ∧ current.storage = cell.storage := by
  have hm : start.memory (counterpart input object) = some (copyCell input cell) := by
    rw [(prepared hp).2]; exact initial_counterpart hc
  obtain ⟨current, hm, ho, hs⟩ := trace_identity ht hm
  exact ⟨current, hm, by simpa [copyCell, (lookup_present hc).2] using ho, hs⟩

def TypeExtends (before after : Heap) : Prop :=
  ∀ object cell, before object = some cell →
    ∃ current, after object = some current ∧ current.storage = cell.storage

def WellTyped (heap : Heap) : Prop :=
  ∀ object cell, heap object = some cell → contentsFit heap cell.storage cell.contents = true

theorem value_fits_monotone (hg : TypeExtends before after)
    (hf : valueFits before dataType value = true) : valueFits after dataType value = true := by
  cases dataType with
  | scalar tag => cases value <;> simp_all [valueFits]
  | object tag =>
    cases value with
    | scalar _ _ => simp [valueFits] at hf
    | reference object =>
      cases hm : before object with
      | none => simp [valueFits, hm] at hf
      | some cell =>
        obtain ⟨current, hc, hs⟩ := hg object cell hm
        simpa [valueFits, hm, hc, hs] using hf

theorem contents_fit_monotone (hg : TypeExtends before after)
    (hf : contentsFit before storage values = true) : contentsFit after storage values = true := by
  cases storage with
  | fixed tag members =>
    simp only [contentsFit, Bool.and_eq_true] at hf ⊢
    refine ⟨hf.1, List.all_eq_true.mpr ?_⟩
    intro pair hp
    exact value_fits_monotone hg (List.all_eq_true.mp hf.2 pair hp)
  | «variable» tag element =>
    exact List.all_eq_true.mpr (fun value hv => value_fits_monotone hg (List.all_eq_true.mp hf value hv))

theorem original_lookup (hv : input.valid = true) (hc : lookup input.pool object = some cell) :
    initialHeap input object = some cell := by
  have hb := below_allocation_bound (valid_cell hv (lookup_present hc).1).1
  rw [(lookup_present hc).2] at hb
  simp [initialHeap, Input.bound, hb, hc]

theorem copy_value_fits (hf : valueFits (lookup input.pool) dataType value = true) :
    valueFits (initialHeap input) dataType (renameValue input value) = true := by
  cases dataType with
  | scalar tag => cases value <;> simp_all [valueFits, renameValue]
  | object tag =>
    cases value with
    | scalar _ _ => simp [valueFits] at hf
    | reference object =>
      cases hm : lookup input.pool object with
      | none => simp [valueFits, hm] at hf
      | some cell =>
        simpa [valueFits, hm, renameValue, initial_counterpart hm, copyCell] using hf

theorem copy_contents_fit (hf : contentsFit (lookup input.pool) storage values = true) :
    contentsFit (initialHeap input) storage (values.map (renameValue input)) = true := by
  cases storage with
  | fixed tag members =>
    simp only [contentsFit, Bool.and_eq_true, List.length_map] at hf ⊢
    refine ⟨hf.1, ?_⟩
    rw [List.zip_map_right, List.all_map]
    exact List.all_eq_true.mpr (fun pair hp => copy_value_fits (List.all_eq_true.mp hf.2 pair hp))
  | «variable» tag element =>
    rw [contentsFit, List.all_map]
    exact List.all_eq_true.mpr (fun value hv => copy_value_fits (List.all_eq_true.mp hf value hv))

theorem prepared_well_typed (hp : prepare input = some start) : WellTyped start.memory := by
  obtain ⟨hv, rfl⟩ := prepared hp
  intro object cell hc
  change initialHeap input object = some cell at hc
  unfold initialHeap at hc
  split at hc
  · have hf := (valid_cell hv (lookup_present hc).1).2
    have grow : TypeExtends (lookup input.pool) (initialHeap input) :=
      fun _ _ hm => ⟨_, original_lookup hv hm, rfl⟩
    exact contents_fit_monotone grow hf
  · obtain ⟨original, ho, rfl⟩ := Option.map_eq_some_iff.mp hc
    exact copy_contents_fit (valid_cell hv (lookup_present ho).1).2

theorem step_well_typed (h : step command world = some next) (hw : WellTyped world.memory) :
    WellTyped next.memory := by
  have grow : TypeExtends world.memory next.memory := by
    intro object cell hc
    obtain ⟨current, hm, _, hs⟩ := step_identity h hc
    exact ⟨current, hm, hs⟩
  cases (step_facts h).heap with
  | stable memory => simpa [memory] using hw
  | @rewrite address previous values hm _ typed _ memory =>
    intro object cell hc
    by_cases he : object = address
    · subst object
      have eq : { previous with contents := values } = cell := by simpa [memory, put] using hc
      cases eq
      exact contents_fit_monotone grow typed
    · exact contents_fit_monotone grow (hw object cell (by simpa [memory, put, he] using hc))
  | @allocate layout values _ _ _ typed _ memory =>
    intro object cell hc
    by_cases he : object = world.nextObject
    · subst object
      have eq : Cell.mk (world.input.context.origin world.nextObject) layout values = cell := by
        simpa [memory, put] using hc
      cases eq
      exact typed
    · exact contents_fit_monotone grow (hw object cell (by simpa [memory, put, he] using hc))

theorem trace_well_typed (ht : Trace program start finish) (hw : WellTyped start.memory) :
    WellTyped finish.memory := by
  induction ht with
  | refl => exact hw
  | tail _ _ hs ih => exact step_well_typed hs ih

theorem fixed_shape_preserved (hp : prepare input = some start)
    (ht : Trace program start finish)
    (hc : finish.memory object = some cell) (hs : cell.storage = .fixed tag members) :
    cell.contents.length = members.length := by
  have hw := trace_well_typed ht (prepared_well_typed hp) object cell hc
  rw [hs] at hw
  simp only [contentsFit, Bool.and_eq_true, decide_eq_true_eq] at hw
  exact hw.1.symm

theorem admitted_inputs_have_no_writer (hp : prepare input = some start)
    (hc : cell ∈ input.pool) (hw : writer ∈ GraphAuthority.analyze input.authorityGraph)
    (ho : writer.object = cell.origin.object) (hm : writer.access.writes = true) : False := by
  have valid := input_facts (prepared hp).1
  let root : GraphAuthority.Root Nat :=
    ⟨allocationBound (input.outside.roots.map GraphAuthority.Root.view) + cell.origin.object,
      cell.origin.object, .immutable⟩
  have hr : root ∈ input.authorityGraph.roots :=
    List.mem_append_right _ (List.mem_map.mpr ⟨cell, hc, rfl⟩)
  exact GraphAuthority.immutable_has_no_writer valid.authority
    (GraphAuthority.granted_covered (.root hr)) rfl hw ho hm

theorem prepared_declared_schemas (hp : prepare input = some start) :
    (input.schemas.map Storage.tag).Nodup ∧ ∀ cell ∈ input.pool, cell.storage ∈ input.schemas := by
  have declared := (input_facts (prepared hp).1).schemas
  simp only [Input.schemasValid, Bool.and_eq_true, decide_eq_true_eq] at declared
  exact ⟨declared.1, fun cell hc => of_decide_eq_true (List.all_eq_true.mp declared.2 cell hc)⟩

theorem allocation_has_declared_schema (h : step (.allocate storage contents) world = some next) :
    storage ∈ world.input.schemas := by
  have ha := (checked_step h).1
  simp only [admissible, Bool.and_eq_true, decide_eq_true_eq] at ha
  exact ha.2.1

theorem admitted_mode_is_immutable (hp : prepare input = some start) (hc : cell ∈ input.pool) :
    ∃ admission ∈ input.admissions, admission.1 = cell.origin.object ∧ admission.2 = .immutable := by
  have receptions := (input_facts (prepared hp).1).receptions
  simp only [Input.receptionsValid, Bool.and_eq_true] at receptions
  have received := List.all_eq_true.mp receptions.2 cell hc
  simpa only [List.any_eq_true, decide_eq_true_eq] using received


theorem value_reference_known (hf : valueFits heap dataType (.reference child) = true) :
    (heap child).isSome = true := by
  cases dataType with
  | scalar tag => simp [valueFits] at hf
  | object tag =>
    cases hm : heap child with
    | none => simp [valueFits, hm] at hf
    | some cell => rfl

theorem contents_reference_known (hf : contentsFit heap layout values = true)
    (hv : Value.reference child ∈ values) : (heap child).isSome = true := by
  cases layout with
  | fixed tag members =>
    have parts : members.length = values.length ∧
        (members.zip values).all (fun (slot, value) => valueFits heap slot.dataType value) = true := by
      simpa only [contentsFit, Bool.and_eq_true, decide_eq_true_eq] using hf
    have mapped : Value.reference child ∈ (members.zip values).map Prod.snd := by
      rw [List.map_snd_zip (by omega)]
      exact hv
    obtain ⟨pair, hp, he⟩ := List.mem_map.mp mapped
    have fits := List.all_eq_true.mp parts.2 pair hp
    change valueFits heap pair.1.dataType pair.2 = true at fits
    rw [he] at fits
    exact value_reference_known fits
  | «variable» tag element => exact value_reference_known (List.all_eq_true.mp hf _ hv)

def LocalsBound (world : World) : Prop :=
  ∀ object ∈ world.locals, world.input.bound ≤ object

theorem private_bounds (hl : LocalsBound world) (ho : object ∈ world.draftObjects) : world.input.bound ≤ object := by
  rcases List.mem_append.mp ho with source | localRoot
  · obtain ⟨cell, _, rfl⟩ := List.mem_map.mp source; unfold counterpart; omega
  · exact hl object localRoot

def RegionSealed (world : World) : Prop :=
  ∀ object cell, world.memory object = some cell → ∀ child, Value.reference child ∈ cell.contents →
    (object < world.input.bound ↔ child < world.input.bound)

theorem prepared_sealed (hp : prepare input = some start) : RegionSealed start := by
  obtain ⟨valid, rfl⟩ := prepared hp
  intro object cell hm child hc
  change (object < input.bound ↔ child < input.bound)
  change initialHeap input object = some cell at hm
  unfold initialHeap at hm
  split at hm
  · rename_i low
    have typed := (valid_cell valid (lookup_present hm).1).2
    have known := contents_reference_known typed hc
    cases found : lookup input.pool child with
    | none => simp [found] at known
    | some target =>
      have hb := below_allocation_bound (valid_cell valid (lookup_present found).1).1
      rw [(lookup_present found).2] at hb
      exact ⟨fun _ => hb, fun _ => low⟩
  · rename_i high
    obtain ⟨original, lookup, rfl⟩ := Option.map_eq_some_iff.mp hm
    obtain ⟨value, _, renamed⟩ := List.mem_map.mp hc
    cases value with
    | scalar tag payload => simp [renameValue] at renamed
    | reference source =>
      have he : counterpart input source = child := by simpa [renameValue] using renamed
      have hb : input.bound ≤ child := by rw [← he]; unfold counterpart; omega
      exact ⟨fun low => False.elim (high low), fun low => by omega⟩

theorem step_locals_bound (h : step command world = some next) (hl : LocalsBound world) : LocalsBound next := by
  have facts := step_facts h
  rw [show LocalsBound next = (∀ object ∈ next.locals, world.input.bound ≤ object) by rw [LocalsBound, facts.input]]
  rcases facts.locals with same | ⟨added, bound⟩
  · simpa [same, LocalsBound] using hl
  · intro object ho
    rw [added] at ho
    rcases List.mem_cons.mp ho with rfl | ho
    · exact bound
    · exact hl object ho

theorem step_sealed (h : step command world = some next) (sealed : RegionSealed world) (hl : LocalsBound world) :
    RegionSealed next := by
  have facts := step_facts h
  intro object cell hm child hc
  rw [facts.input]
  cases facts.heap with
  | stable memory => exact sealed object cell (memory ▸ hm) child hc
  | @rewrite address previous values lookup bound _ refs memory =>
    by_cases selected : object = address
    · subst object
      have eq : { previous with contents := values } = cell := by simpa [memory, put] using hm
      cases eq
      have inRegion : child ∈ world.draftObjects := by
        simpa only [confinedValue, decide_eq_true_eq] using List.all_eq_true.mp refs _ hc
      have high := private_bounds hl inRegion
      constructor <;> intro impossible <;> omega
    · exact sealed object cell (by simpa [memory, put, selected] using hm) child hc
  | @allocate layout values bound _ _ _ refs memory =>
    by_cases selected : object = world.nextObject
    · subst object
      have eq : Cell.mk (world.input.context.origin world.nextObject) layout values = cell := by simpa [memory, put] using hm
      cases eq
      have candidateBound : LocalsBound (allocated world layout values) := by
        intro object ho
        rcases List.mem_cons.mp ho with rfl | ho
        · exact bound
        · exact hl object ho
      have inRegion : child ∈ (allocated world layout values).draftObjects := by
        simpa only [confinedValue, decide_eq_true_eq] using List.all_eq_true.mp refs _ hc
      have high := private_bounds candidateBound inRegion
      change world.input.bound ≤ child at high
      constructor <;> intro impossible <;> omega
    · exact sealed object cell (by simpa [memory, put, selected] using hm) child hc

/-- Derived inductively. This invariant is never supplied in a recipe input. -/
structure WorldInvariant (initialInput : Input) (world : World) : Prop where
  input : world.input = initialInput
  frame : ∀ object, object < initialInput.bound → world.memory object = lookup initialInput.pool object
  typed : WellTyped world.memory
  locals : LocalsBound world
  sealed : RegionSealed world
  boundaries : world.observations.all ExternalObservation.known = true

theorem prepare_invariant (hp : prepare input = some start) : WorldInvariant input start := by
  refine ⟨congrArg World.input (prepared hp).2, ?_, prepared_well_typed hp, ?_, prepared_sealed hp, ?_⟩
  · intro object low
    rw [(prepared hp).2]
    simp [initialHeap, low]
  · obtain ⟨_, rfl⟩ := prepared hp; intro object ho; contradiction
  · obtain ⟨_, rfl⟩ := prepared hp; rfl

theorem step_invariant (h : step command world = some next) (hw : WorldInvariant input world) : WorldInvariant input next := by
  have facts := step_facts h
  exact ⟨facts.input.trans hw.input,
    fun object ho => ((step_frame h).2 object (by simpa [hw.input] using ho)).trans (hw.frame object ho),
    step_well_typed h hw.typed, step_locals_bound h hw.locals, step_sealed h hw.sealed hw.locals,
    facts.knownPreserved hw.boundaries⟩

theorem trace_invariant (hp : prepare input = some start) (ht : Trace program start finish) : WorldInvariant input finish := by
  induction ht with
  | refl => exact prepare_invariant hp
  | tail _ _ hs ih => exact step_invariant hs ih

theorem path_stays_region (sealed : RegionSealed world) (hp : Path world.memory root fields target) :
    (root < world.input.bound ↔ target < world.input.bound) := by
  induction hp with
  | here => rfl
  | next hm hv _ ih => exact (sealed _ _ hm _ (List.mem_of_getElem? hv)).trans ih

theorem old_root_cannot_reach_draft (hp : prepare input = some start) (ht : Trace program start finish)
    (path : Path finish.memory root fields target) (old : root ∈ input.reserved)
    (privateTarget : target ∈ finish.draftObjects) : False := by
  have invariant := trace_invariant hp ht
  have low := below_allocation_bound old
  have sameRegion := path_stays_region invariant.sealed path
  have high := private_bounds invariant.locals privateTarget
  rw [invariant.input] at sameRegion high
  have below := sameRegion.mp low
  omega

end RilAccess.Draft
