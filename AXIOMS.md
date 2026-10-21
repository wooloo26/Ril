# Ril Semantic Kernel Axioms (`ril-compiler`)

This document defines the architectural axioms for refactoring and completing `crates/ril-compiler/src/sema/`. It is written for developers working on the Ril compiler.

`doc/SPEC.md` and `doc/STD.md` define the normative language rules. `DEVELOPMENT.md` defines repository workflows and current implementation gaps. **This document defines the internal mathematical and structural invariants of the semantic kernel** so that implementation complexity scales as $O(N)$ (additive by domain) rather than $O(N^2)$ (multiplicative across feature combinations).

---

## 1. Root Cause Diagnosis: Why Ad-Hoc Patching Fails

Ril's language specification (`doc/SPEC.md`) is axiomatic and zero-slack: every capability, `Source` provenance, fixed dimension, loan, effect, resource duty, `Result` obligation, and termination contract is sound by construction.

However, the legacy implementation in `crates/ril-compiler/src/sema/` grew by patching feature-pair interactions one by one, producing three structural bottlenecks:

1. **God-Object State & Combinatorial Side-Tables**
   - `Checker` (`crates/ril-compiler/src/sema/checker.rs`) holds ~195 mutable fields across 80+ submodules.
   - `SemanticFacts` (`crates/ril-compiler/src/sema.rs`) exports ~100 separate fact collections.
   - Whenever feature $A$ (e.g., `Source` provenance or record bounds) interacts with construct $B$ (e.g., default arguments, channel sends, `with`/`resume` handlers, or closure captures), a bespoke side-ledger (`call_input_source_composites.rs`, `storage_input_source.rs`, `channel_repetition_validation.rs`, etc.) was added instead of routing both through a single algebraic boundary operator.
2. **Span-Keyed Identity Collisions**
   - Many working tables in `Checker` still index facts by raw source coordinates `(u32, u32, u32)` or `Span` (`sites`, `contextual_types`, `variant_projections`, `implicit_unwraps`, `type_contract_environments`, `result_sites`, `read_epochs`).
   - A single syntax span can be evaluated multiple times across:
     - Default parameter synthesis at distinct call sites,
     - Generic and static specialization (`meta` / `type<T>`),
     - Higher-order callback replay and loop fixed-point passes,
     - Multi-shot or post-`resume` algebraic effect handler activations.
   - Keying semantic state by `Span` overwrites earlier occurrences or forces fragile retroactive epoch rewriting (`allocation_epoch` history patching).
3. **Split Type & Provenance Truth**
   - Type and provenance representation is split across three layers:
     1. Erased runtime shape `sema::model::Ty` (which drops `Source`, fixed array extents, and contextual row environments),
     2. Legacy AST/string-keyed `SourceTypeWitness { syntax: TypeExpr, key: String }`,
     3. The canonical graph arena `sema::source_types::SourceTypeIndex` (`SourceTypeId`).
   - Reconstructing complete `Source` schemas from erased `Ty` or string keys at each validation site loses lexical binder identity (`ScopedSourceIdentityId`) and causes false positives/negatives across nested containers, tuples, closures, and `Result`/optional payloads.

---

## 2. The Three Kernel Axioms

Every change to `crates/ril-compiler/src/sema/` must converge toward the following three axioms.

```text
                  +-----------------------------------------+
                  |  Canonical HIR (HirProgram, BlockIndex) |
                  |  + Immutable SourceTypeIndex            |
                  +--------------------+--------------------+
                                       |
         Axiom I: (HirNodeId, ActivationEpochId) Occurrence Identity
                                       v
                  +-----------------------------------------+
                  |   Monotone Abstract Machine (Domains)   |
                  |  All 10 boundaries -> receive_boundary  |
                  |  All control merges -> join_branches    |
                  |  All epoch steps    -> transport_epoch  |
                  +--------------------+--------------------+
                                       |
         Axiom II & III: Proof-Carrying Derivation Ledger
                                       v
                  +-----------------------------------------+
                  |  Independent Certificate Validator      |
                  |  validate::solved_facts -> VerifiedProgram
                  +-----------------------------------------+
```

---

### Axiom I: Occurrence Identity Over Source Spans

> **Rule 1.1 (Spans Are Diagnostic Only):** `Span` and `(u32, u32, u32)` locate source text for diagnostic rendering and source-location queries. They must **never** be used as primary keys in semantic state tables, obligation ledgers, or validation joins.

> **Rule 1.2 (Two-Level Identity):** Every semantic entity is uniquely identified by the product of its **Static Syntax Identity** and its **Dynamic Evaluation Occurrence**:
> $$\text{OccurrenceId} = (\text{HirNodeId}, \text{ActivationEpochId})$$

1. **Static Syntax Identity (`HirNodeId`):**
   - Owned by `hir::nodes::HirProgram` (`ExprId`, `StmtId`, `PatternId`, `TypeExprId`, `GenericParamId`, `BlockAnchor` in `ril-compiler-core::ids`).
   - Lowered/desugared constructs must carry explicit `hir::NodeOrigin::Generated { generation, anchor, kind }` or `NodeOrigin::Transformed`, never synthetic colliding spans.
   - Structural block tails and statement memberships are queried from `hir::blocks::BlockIndex`, never by comparing byte offsets or inspecting raw AST slice suffixes.
   - Unified calls and pipelines (`|>` / `!>`) are queried through `hir::application::HirApplication` (`EvaluationRole::Callee`, `EvaluationRole::Piped`, `EvaluationRole::Written(i)`), never by fabricating fake `ast::ExprKind::Call` nodes.

2. **Dynamic Evaluation & Epoch Identity (`ActivationEpochId` / `EvaluationOccurrenceId`):**
   - A single `ExprId` or `StmtId` evaluated in distinct activations (e.g., default parameter evaluation per call site, closure invocation per call context, handler arm pre-`resume` vs. post-`resume` epoch, loop iteration pass) receives a distinct, monotonically allocated occurrence record in the evaluation ledger (`sema::evaluation_identity`).
   - **Historical Immutability:** An `ExpressionFact` or `AccessFact` is recorded at its birth `allocation_epoch`. When a value is read or retained in a later epoch (such as across a heap allocation, suspension, or `resume`), the checker must apply an explicit, pure `transport(value, from_epoch, to_epoch)` transition rather than mutating historical records in place.

---

### Axiom II: Unified Abstract Value & Single Boundary Reception

> **Rule 2.1 (Single Value Representation):** Every evaluated expression at an occurrence yields a single algebraic value descriptor $\mathcal{V}$. Do not track a value's runtime type in one table, its `Source` coordinates in a second table, its record-bound environment in a third, and its `Result`/optional tags in a fourth.

#### The Canonical Abstract Value Tuple

Every abstract value / storage slot in the semantic kernel is defined by:

$$\mathcal{V} = \bigl(\tau_{\text{source}},\; \mathcal{E}_{\text{frozen}},\; \Pi_{\text{origins}},\; \mathcal{P}_{\text{perm}},\; \mathcal{R}_{\text{recency}},\; \mathcal{O}_{\text{duties}}\bigr)$$

| Component | Canonical Type / Store | Role |
| :--- | :--- | :--- |
| $\tau_{\text{source}}$ | `SourceTypeId` in `SourceTypeIndex` | Complete structural & provenance schema: retains `Source` coordinates, fixed array dimensions `[N]T`, parameter modes, generic binders, and callable signatures. `model::Ty` is strictly a derived projection of `SourceTypeId`. |
| $\mathcal{E}_{\text{frozen}}$ | `FrozenEnvId` | Lexical contract environment captured at declaration/creation: binds generic parameters, qualified row bounds, static `meta` values, and `ScopedSourceIdentityId` roots. |
| $\Pi_{\text{origins}}$ | `BTreeSet<OriginId>` + projection path | Abstract heap roots, formal loan anchors, and composite member/element coordinates reachable through this value. |
| $\mathcal{P}_{\text{perm}}$ | `AccessMode` (`Own`, `Mut`, `Read`, `Immut`, `View`) | Current capability ceiling. Monotone under projection and assignment: `Read`, `View`, and `Immut` restrictions can **never** recover write authority. |
| $\mathcal{R}_{\text{recency}}$ | `EpochId` + `ProtectedAnswerId` | Birth allocation epoch and handler/resumption epoch provenance for non-tail reference and temporary escape checking. |
| $\mathcal{O}_{\text{duties}}$ | `DutyState` (`OptionalTagId`, `ResultSite`, `ResourceHandle`) | Uninspected `Result` obligations, optional tag refinements, linear resource cleanup duties, and channel state tokens. |

#### The Single Reception Morphism (`receive_boundary`)

> **Rule 2.2 (Universal Boundary Transfer):** Ril has **10 value-receiving boundaries**. Every single boundary must execute the **same canonical transfer function** (`receive_boundary`) over $(\mathcal{V}_{\text{actual}}, \tau_{\text{formal\_view}}, \mathcal{E}_{\text{target}}, \text{BoundaryKind})$.

The 10 value-receiving boundaries are:

1. **Local Binding:** `let`, `var`, and destructuring `PatternId` bindings.
2. **Explicit Application Input:** Call and pipeline operands (`HirApplication` roles `Piped` and `Written(i)`).
3. **Default Parameter Instantiation:** Default argument expressions evaluated in the callee's frozen declaration environment at the caller's activation epoch.
4. **Composite Construction:** Record fields, tuple slots, enum variant payloads, fixed-size array elements `[N]T`, and dynamic container admissions (`Vec`, `Map`, `Set`).
5. **Storage Write / Mutation:** Reassignment (`x = v`) and interior/indexed mutation (`a[i] = v`, `r.f = v`). Writes check all possible target origins and install **only** the destination's declared view—a current mutable value never redefines its declaration's fixed view.
6. **Environment Capture:** Function, closure (`ClosureSiteId`), iterator generator, and `with` handler environment captures.
7. **Channel Transport:** Channel `send`, `recv`, `try_recv`, and `for msg in rx` iteration yields.
8. **Effect & Resumption Transport:** Effect operation arguments, `resume(answer)` inputs, and protected computation receipts (`ProtectedAnswerId`).
9. **Control-Flow Join & Block Tail:** `if`/`else`, `match` arms, `with` handler arms, and lexical block completions (`BlockIndex` tail vs. non-tail statement drops).
10. **Callable Return & Publication:** `return expr`, function/lambda body tails, and module/static constant publications (`ConstRef`).

#### Invariants of `receive_boundary`

When `receive_boundary` admits $\mathcal{V}_{\text{actual}}$ into target schema $(\tau_{\text{target}}, \mathcal{E}_{\text{target}})$:

1. **Recursive Structural Walk (Bounded by `work`):** It traverses $\tau_{\text{actual}}$ and $\tau_{\text{target}}$ in `SourceTypeIndex` simultaneously across records, tuples, arrays, optionals, `Result`, closures, and generic bounds—charging explicit `work` budget before every node expansion.
2. **Provenance & Dimension Preservation:**
   - Declared fixed dimensions (`[N]T`, including inner dimensions of empty outer arrays `[0][3]int`) are checked against $\tau_{\text{actual}}$ in `SourceTypeIndex`, never inferred from runtime backing slice length.
   - Required `Source` coordinates and qualified record-bound member sources are verified or propagated uniformly whether the value arrives directly, inside a tuple/record/array/Result, via a default argument, or across a channel/`resume`.
3. **Capability & Loan Transition:**
   - Installs the target's frozen view without amplifying permissions.
   - Records formal loans, suspension of parent borrows on reborrow, and recent-to-older epoch transport in one atomic step.
4. **Duty Transfer:**
   - Transfers or discharges `Result` inspection duties, `OptionalTagId` refinements, and linear resource handles.

> **Corollary:** Never write a specialized `validate_channel_closure_result_source` or `check_default_arg_record_bound_composite`. If a `Source` or bound check fails across a channel or default argument, fix the missing `receive_boundary` call or projection rule in `SourceTypeIndex` so **all 10 boundaries** gain the capability simultaneously.

---

### Axiom III: Monotone Fixed-Point Domains & Proof-Carrying Validation

> **Rule 3.1 (Domain Decomposition):** Decompose `Checker` and `SemanticFacts` into five orthogonal domains with owned state and explicit finite-lattice interfaces.

| Domain | Owned Responsibility | Lattice / Fixed-Point Mechanism |
| :--- | :--- | :--- |
| **1. `TypeSourceDomain`** | `SourceTypeIndex`, `FrozenEnvId`, generic substitutions, structural projections, `receive_boundary` compatibility, `NumericSelectionId` resolution. | Immutable DAG arena (`SourceTypeId`) + unification/constraint work queue with explicit `Unknown` poison lattice. |
| **2. `HeapCapabilityDomain`** | `OriginId`, `AccessMode`, `LoanId`, closure exclusivity (`ClosureSiteId`), `EpochId` recency, deep-clone isolation vs. view aliasing. | Finite abstract heap graph $(\text{Origins} \times \text{Fields})$ with monotone permission meet and epoch-transport edges. |
| **3. `ApplicationEffectDomain`** | `HirApplication` evaluation order, `EvaluationOccurrenceId` ledger, algebraic effect row propagation, `HandlerSiteId` and `ResumptionEpoch` transitions. | Call-graph SCC worklist (`sema::summary::close_invocation_dependencies`) + handler activation state lattice. |
| **4. `ObligationDutyDomain`** | `Result` handling lattice, `OptionalTagId` boolean guard receipts, linear resource lifecycles, channel state/guard BDD observer. | Branch-sensitive path lattice: joins (`join_branches`) take the conservative intersection of proven facts and union of pending duties. |
| **5. `TerminationBudgetDomain`** | Structural recursion proofs, lexicographic decrease measures, loop bounds, and compile-time `work` / static event budgets. | Call-graph Tarjan SCC analysis + measure matrix solver; strict pre-charge budget accounting. |

> **Rule 3.2 (Producer vs. Independent Certificate Checker):**
> `validate::solved_facts` (which gates construction of the private `VerifiedProgram` token required by Core lowering) must act as an **independent certificate verifier**, not a second copy of the type checker.

1. **No Self-Certifying Producer Flags:** A boolean flag set by `Checker` (e.g., `checked_record_bounds = true`) is **not** a proof.
2. **Unified Certificate Checking:** Instead of 25 separate `validate_*` passes each re-walking ASTs and guessing how calls or bindings happened, the checker emits a compact **Boundary & Occurrence Ledger** indexed by `(HirNodeId, ActivationEpochId)`.
3. **Total Occurrence Coverage:** The validator walks `HirProgram` (`BlockIndex`, `HirApplication`) and the `EvaluationOccurrenceId` ledger once, verifying that:
   - Every static HIR node is covered by at least one well-formed static typing record,
   - Every reachable dynamic evaluation occurrence (including defaults, generated pattern values, synthetic callbacks, and post-`resume` steps) has a valid `receive_boundary` certificate against its original `HirNodeId` and `ActivationEpochId`,
   - Deleting or skipping any producer table causes validation to reject with an explicit missing-evidence error (`E9999` / internal verification failure) rather than silently passing.

---

## 3. Strict Engineering Rules for Developers

When implementing features or fixing regressions in `crates/ril-compiler/`:

### DO NOT (Forbidden Patterns)
1. **Do not add new `Span`-keyed or `(u32, u32, u32)`-keyed maps** to `Checker` or `SemanticFacts`. Use `ExprId`, `StmtId`, `PatternId`, `TypeExprId`, `BlockAnchor`, or `(HirNodeId, EvaluationOccurrenceId)`.
2. **Do not add feature-specific side ledgers** when a test fails at the intersection of two features. Ask:
   - *Which of the 10 boundaries transmitted this value?*
   - *Which component of $\mathcal{V} = (\tau_{\text{source}}, \mathcal{E}_{\text{frozen}}, \Pi_{\text{origins}}, \mathcal{P}_{\text{perm}}, \mathcal{R}_{\text{recency}}, \mathcal{O}_{\text{duties}})$ was dropped or reconstructed from erased `Ty`?*
   Fix the representation in $\mathcal{V}$ or `receive_boundary` directly.
3. **Do not parse or string-match `SourceTypeWitness.key`** to inspect types, dimensions, or `Source` sets. All structural queries must go through `SourceTypeIndex` (`crates/ril-compiler/src/sema/source_types/`).
4. **Do not fabricate synthetic `ast::Expr` nodes with cloned spans** during semantic checking. Use `HirApplication` for call/pipeline views and `hir::NodeOrigin::Generated` for compiler-synthesized roots.
5. **Do not silently default to "safe" when a proof is missing or a budget is exhausted.** In Ril, unknown overlap, unresolved generic/source identity, or exhausted `work` budget is always a conservative rejection or obligation failure, never a pass.

### DO (Required Patterns)
1. **Charge `work` budgets before allocation or traversal.** Every recursive walk over `HirProgram`, `SourceTypeIndex`, or abstract heap graphs must decrement a bounded `work: &mut usize` counter before enqueueing or cloning nodes.
2. **Keep `BTreeMap` / `BTreeSet` deterministic ordering.** Compiler state, diagnostics, and IR lowering must be 100% deterministic across runs and platforms (`pointer32` and `pointer64`). Never use host `usize` for target layout calculations.
3. **Preserve `AnalysisSnapshot` resilience for semantic introspection.** Failed or incomplete programs must still produce an uncertified `AnalysisSnapshot` with partial symbol/type/capability facts and `CauseId` chains, while only zero-error + validated programs can mint `VerifiedProgram`.
4. **Delete superseded legacy code immediately after migrating a consumer.** Once a validation pass or checker routine moves to `HirProgram` / `SourceTypeIndex` / `receive_boundary`, delete the old span-based fallback in the same slice so dead state cannot drift.

---

## 4. Kernel Completion Roadmap

Follow this sequence to complete the kernel while shrinking `sema/`. The active tests and corpus define the remaining failures; historical checkpoint counts do not define acceptance.

### Phase 1: Complete `receive_boundary` Coverage Across All 10 Boundaries
- Route all remaining ad-hoc source/bound checks (`record_bound_validation/call_input_source*.rs`, `storage_sources.rs`, `explicit_named.rs`, `channel_source_index.rs`) through the unified `(HirNodeId, EvaluationOccurrenceId)` observation index and `SourceTypeIndex`.
- Ensure generated I/O callbacks, iterator state closures, channel `send`/`recv` payloads, and `with`/`resume` answer bindings (`ProtectedAnswerId`) emit standard boundary reception records in their actual activation epoch.

### Phase 2: Unify Non-Tail Reference & Resumption Epoch Transport
- Use `hir::blocks::BlockIndex` and `ProtectedAnswerId` to separate:
  1. Block tail expressions (which transfer to the enclosing block's receiver),
  2. Non-tail statement expressions (which drop at the statement boundary while retaining any escaped loan/recency observations),
  3. Protected `with` computation answers vs. handler arm continuations (`resume`).
- Apply explicit `transport(value, from_epoch, to_epoch)` across suspension and resumption boundaries so post-`resume` reads/writes validate against the actual resumption epoch.

### Phase 3: Retire `SourceTypeWitness` String Keys & Span Working Tables
- Replace remaining uses of `SourceTypeWitness { syntax, key }` in `Checker` and `SemanticFacts` with `(SourceTypeId, FrozenEnvId)`.
- Migrate `Checker::sites`, `contextual_types`, `variant_projections`, `implicit_unwraps`, `result_sites`, and `read_epochs` from `(u32, u32, u32)` keys to `ExprId` / `(ExprId, EvaluationOccurrenceId)`.

### Phase 4: Collapse `Checker` into the Five Domain Stores
- Extract owned domain structs (`TypeSourceDomain`, `HeapCapabilityDomain`, `ApplicationEffectDomain`, `ObligationDutyDomain`, `TerminationBudgetDomain`) from `Checker`.
- Reduce `Checker` to a thin coordinator that walks `HirProgram` and dispatches to the five domains and `validate::solved_facts`.
