import RilAccess.Model
import RilAccess.Solver

namespace RilAccess

/-- Mechanism labels retain the explanation/lowering site, not extra authority. -/
inductive Mechanism where
  | binding | aggregate | projection | call | higherOrder | returnValue | closure
  | via | infer | module | opaque | handler | resume | cleanup | task | resource
  | clone | derive | handoff
  deriving Repr, DecidableEq

inductive EventKind where
  | read | write | retain | capture | rootReturn | containedReturn | transfer
  deriving Repr, DecidableEq

inductive Fact where
  | active (pc : Nat)
  | root (register : Nat) (source : Source)
  | edge (parent child : Source)
  | descendant (parent child : Source)
  | event (kind : EventKind) (source : Source)
  deriving Repr, DecidableEq

inductive Action where
  | seed (destination : Nat) (source : Source)
  | copy (src to : Nat) (mechanism : Mechanism)
  | store (parent field child : Nat)
  | project (parent field destination : Nat)
  | emit (kind : EventKind) (register : Nat) (deep : Bool) (mechanism : Mechanism)
  | enter (mechanism : Mechanism) (identity : Nat)
  | leave (mechanism : Mechanism)
  | skip
  deriving Repr, DecidableEq

structure Instruction where
  pc : Nat
  action : Action
  next : List (Option Nat)
  deriving Repr, DecidableEq

/-- Checks constrain inferred facts; they do not seed the inference. -/
inductive Check where
  | present (fact : Fact)
  | absent (fact : Fact)
  | exactEvents (row : List Fact)
  deriving Repr, DecidableEq

structure ResolvedProgram where
  entry : Nat
  code : List Instruction
  checks : List Check := []
  deriving Repr, DecidableEq

def ResolvedProgram.sources (p : ResolvedProgram) : List Source :=
  p.code.flatMap fun i => match i.action with | .seed _ s => [s] | _ => []

def actionRules (sources : List Source) (pc : Nat) : Action → List (Rule Fact)
  | .seed r s => [⟨[.active pc], .root r s⟩]
  | .copy a b _ => sources.map fun s => ⟨[.active pc, .root a s], .root b s⟩
  | .store a _ b => sources.flatMap fun s => sources.map fun t =>
      ⟨[.active pc, .root a s, .root b t], .edge s t⟩
  | .project a _ b => sources.flatMap fun s => sources.map fun t =>
      ⟨[.active pc, .root a s, .edge s t], .root b t⟩
  | .emit k r false _ => sources.map fun s => ⟨[.active pc, .root r s], .event k s⟩
  | .emit k r true _ => sources.flatMap fun s => sources.map fun t =>
      ⟨[.active pc, .root r s, .descendant s t], .event k t⟩
  | _ => []

def instructionRules (sources : List Source) (i : Instruction) : List (Rule Fact) :=
  actionRules sources i.pc i.action ++ i.next.flatMap fun next =>
    match next with
    | none => []
    | some n => [⟨[.active i.pc], .active n⟩]

def graphRules (sources : List Source) : List (Rule Fact) :=
  sources.flatMap fun s =>
    [⟨[], .descendant s s⟩] ++ sources.flatMap fun t =>
      [⟨[.edge s t], .descendant s t⟩] ++ sources.map fun u =>
        ⟨[.descendant s t, .descendant t u], .descendant s u⟩

def ResolvedProgram.rules (p : ResolvedProgram) : List (Rule Fact) :=
  [⟨[], .active p.entry⟩] ++ graphRules p.sources ++
    p.code.flatMap (instructionRules p.sources)

def isEvent : Fact → Bool | .event _ _ => true | _ => false

def checkHolds (facts : List Fact) : Check → Bool
  | .present f => decide (f ∈ facts)
  | .absent f => decide (f ∉ facts)
  | .exactEvents row =>
      facts.all (fun f => !isEvent f || decide (f ∈ row)) &&
        row.all (fun f => isEvent f && decide (f ∈ facts))

structure Analysis where
  facts : List Fact
  /-- Fired rules are a finite explanation graph, including recursive dependencies. -/
  explanations : List (Rule Fact)
  deriving Repr, DecidableEq

inductive Diagnostic where
  | contractMismatch (check : Check) (inferred : Analysis)
  | missingOrigin (pc register : Nat) (inferred : Analysis)
  deriving Repr, DecidableEq

def operands : Action → List Nat
  | .copy src _ _ => [src]
  | .store parent _ child => [parent, child]
  | .project parent _ _ => [parent]
  | .emit _ register _ _ => [register]
  | _ => []

/-- Check may-source availability in the global solution, not definite
initialization along every incoming path. Success does not imply progress. -/
def missingOperands (p : ResolvedProgram) (facts : List Fact) : List (Nat × Nat) :=
  p.code.flatMap fun i =>
    if Fact.active i.pc ∈ facts then
      (operands i.action).filterMap fun register =>
        if p.sources.any (fun s => decide (Fact.root register s ∈ facts)) then none
        else some (i.pc, register)
    else []

def analyze (p : ResolvedProgram) : Except Diagnostic Analysis :=
  let facts := solve p.rules
  let inferred : Analysis := ⟨facts, p.rules.filter fun r =>
    r.premises.all (fun x => decide (x ∈ facts))⟩
  match (missingOperands p facts).head? with
  | some (pc, register) => .error (.missingOrigin pc register inferred)
  | none =>
    match p.checks.find? (fun c => !checkHolds facts c) with
    | some c => .error (.contractMismatch c inferred)
    | none => .ok inferred

/-- Per-point queries intentionally share the flow-insensitive region solution. -/
def Analysis.at (a : Analysis) (pc : Nat) : List Fact :=
  if Fact.active pc ∈ a.facts then a.facts else []

def Analysis.outwardCandidates (a : Analysis) : List Fact := a.facts.filter isEvent

variable {p : ResolvedProgram} {a : Analysis} {c : Check} {i : Instruction}
  {r : Rule Fact} {s : Source}

theorem analyze_facts (ha : analyze p = .ok a) : a.facts = solve p.rules := by
  unfold analyze at ha
  dsimp only at ha
  split at ha
  · contradiction
  · split at ha
    · contradiction
    · cases ha
      rfl

theorem analyze_checks (ha : analyze p = .ok a) (hc : c ∈ p.checks) :
    checkHolds a.facts c = true := by
  have hf := analyze_facts ha
  unfold analyze at ha
  dsimp only at ha
  split at ha
  · contradiction
  · split at ha
    · contradiction
    · rename_i hn
      have h := List.find?_eq_none.mp hn c hc
      simp_all

theorem analyze_least (ha : analyze p = .ok a) :
    Closed p.rules a.facts ∧ Grounded p.rules a.facts := by
  rw [analyze_facts ha]
  exact ⟨solve_closed, solve_grounded⟩

theorem analyze_no_missing (ha : analyze p = .ok a) : missingOperands p a.facts = [] := by
  rw [analyze_facts ha]
  unfold analyze at ha
  dsimp only at ha
  split at ha
  · contradiction
  · rename_i hm
    exact List.head?_eq_none_iff.mp hm

theorem analyze_operand_known (ha : analyze p = .ok a) (hi : i ∈ p.code)
    (hactive : Fact.active i.pc ∈ a.facts) (hr : register ∈ operands i.action) :
    ∃ s ∈ p.sources, Fact.root register s ∈ a.facts := by
  apply Classical.byContradiction
  intro hn
  have hnone : p.sources.any (fun s => decide (Fact.root register s ∈ a.facts)) = false := by
    apply List.any_eq_false.mpr
    intro s hs
    have no : Fact.root register s ∉ a.facts := fun hf => hn ⟨s, hs, hf⟩
    simp [no]
  have bad : (i.pc, register) ∈ missingOperands p a.facts := by
    apply List.mem_flatMap.mpr
    refine ⟨i, hi, ?_⟩
    simp only [if_pos hactive]
    apply List.mem_filterMap.mpr
    exact ⟨register, hr, by simp [hnone]⟩
  simp [analyze_no_missing ha] at bad

theorem instruction_rule_mem (hi : i ∈ p.code)
    (hr : r ∈ instructionRules p.sources i) : r ∈ p.rules := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  exact ⟨i, hi, hr⟩

theorem action_rule_mem (hi : i ∈ p.code)
    (hr : r ∈ actionRules p.sources i.pc i.action) : r ∈ p.rules :=
  instruction_rule_mem hi (List.mem_append_left _ hr)

theorem seed_source_mem (hi : i ∈ p.code) (hs : i.action = .seed register s) : s ∈ p.sources := by
  apply List.mem_flatMap.mpr
  exact ⟨i, hi, by simp [hs]⟩

theorem graph_rule_mem (hr : r ∈ graphRules p.sources) : r ∈ p.rules := by
  apply List.mem_append_left
  exact List.mem_append_right _ hr

theorem graph_refl_mem (hs : s ∈ sources) :
    Rule.mk [] (.descendant s s) ∈ graphRules sources := by
  apply List.mem_flatMap.mpr
  exact ⟨s, hs, List.mem_append_left _ (by simp)⟩

theorem graph_edge_mem (hs : s ∈ sources) (ht : t ∈ sources) :
    Rule.mk [.edge s t] (.descendant s t) ∈ graphRules sources := by
  apply List.mem_flatMap.mpr
  refine ⟨s, hs, List.mem_append_right _ ?_⟩
  apply List.mem_flatMap.mpr
  exact ⟨t, ht, List.mem_append_left _ (by simp)⟩

theorem graph_trans_mem (hs : s ∈ sources) (ht : t ∈ sources) (hu : u ∈ sources) :
    Rule.mk [.descendant s t, .descendant t u] (.descendant s u) ∈ graphRules sources := by
  apply List.mem_flatMap.mpr
  refine ⟨s, hs, List.mem_append_right _ ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨t, ht, List.mem_append_right _ ?_⟩
  exact List.mem_map.mpr ⟨u, hu, rfl⟩

end RilAccess
