# The Ril Language Specification

**Version:** 0.1.0  
**Status:** Canonical Reference Specification  
**Format:** Code-First Normative Document  

---


## Document Conventions

This document defines Ril grammar, typing, access modes, state and provenance tracking, effects, abstract-machine behavior, and diagnostics.

Contexts, judgments, paths, and object graphs are semantic notation.

Requirements in prose, grammar productions, rule tables, and annotated verification cases are normative within their stated contexts. Rationale and illustrative diagnostic text explain those requirements without adding rejection conditions.

The words **must** and **must not** express requirements and prohibitions; **may** permits an alternative; **should** gives advisory guidance whose observance is not required for conformance. Capitalization does not change their force. Declarative rules also impose requirements. Each rule applies under its stated premises and exceptions.

The following distinctions apply throughout the specification; their defining sections supply the detailed rules:

| Terms | Distinction |
| :--- | :--- |
| Binding mode / access mode | A binding mode controls slot replacement; an access mode bounds access through a path to reachable data or a callable environment |
| Pinned binding / physical address | Pinning fixes which object a binding denotes; it does not promise a fixed physical address |
| Read-only / deeply immutable | A read-only path grants no writes through that path; a live origin may still be writable through another path. Deep immutability excludes surviving writers and live dependencies |
| Shared object / shared writable authority | A shared object has identity and can be aliased; this alone grants no shared write authority |
| Construction / isolation | Construction qualification tracks eligible initial reception and handoff. Root privacy and separation of writable graph regions require independent proofs |
| Record type / record value | Both use `.{...}`; a `TypeReference` may prefix a runtime expression, pattern, or test (`User.{...}`). Sum and effect declaration bodies keep `{...}` |
| Value argument / type argument | A value argument goes only to a declared value-sorted parameter; a value is never converted to a type. `typeof e` is the explicit form |
| Purity / finiteness / normal completion | Purity excludes outward operational effects and state/provenance obligations, while implicit `Diverge`, `Panic`, and `Fatal` may remain. Optional `halt` additionally excludes `Diverge`. A `never` expression has no normal continuation; it can transfer control, panic, terminate fatally, or execute forever |

- **Normative Rules and Invariants**: Conforming implementations must enforce all specified grammar, static-checking, and execution rules, including rules not presented as titled invariants.
- **Grammar Productions**: Syntactic grammar is formally specified in Extended Backus-Naur Form (EBNF).
- **Normative Code Annotations**: Code examples define normative verification cases in the stated fixture context:
  - `-- OK`: A fragment or program that is syntactically and semantically valid in its stated fixture context.
  - `-- Error [EXXXX]`: A fragment or program that must be statically rejected with the indicated diagnostic code in its stated fixture context.
  - `-- Panics`: An expression or program that initiates panic unwinding when evaluated under the stated fixture conditions; this is an execution outcome, not a static rejection.
- **Diagnostic Text**: Error codes and their triggering conditions are normative. Example message text, source highlighting, notes, and suggested repairs are illustrative.
- **Examples**: Blocks are independent fixtures unless marked as complete source files.
  - Local statements run in an enclosing callable; displayed declarations belong to its enclosing declaration scope. Free names are typed fixture inputs or supplied declarations.
  - Fixtures handle their local expressions' operational effects; implicit `Diverge`, `Panic`, and `Fatal` may remain. Except for examples testing missing named-function annotations, abbreviated named callable declarations in independent fixtures denote their compiler-completed signatures under [mandatory contract completion](#mandatory-contract-inference-and-completion). `-- OK` checks that completed form; complete source files spell the prescribed named annotations, with the specified `via`/`infer` exemptions and automatic implicit effect inference. Anonymous functions retain full inferred contracts with optional source annotations.
  - Negative statements are checked individually with valid setup. Unfinished expression holes (`...`) reject complete program builds (`E0360`).
  - Static-evaluation fixtures use the selected abstract target and a sufficient evaluation budget unless a budget-exhaustion case is explicitly specified.
- **Semantic Cross-References**: Internal specifications and rule cross-references link directly to their defining sections via Markdown anchors.
---

## Table of Contents

- [The Ril Language Specification](#the-ril-language-specification)
  - [Document Conventions](#document-conventions)
  - [Table of Contents](#table-of-contents)
  - [Notation, Abstract Machine, and Conformance](#notation-abstract-machine-and-conformance)
    - [Grammar Notation](#grammar-notation)
    - [Program Conformance](#program-conformance)
    - [Diagnostic Classification](#diagnostic-classification)
    - [Abstract Machine and Memory Semantics](#abstract-machine-and-memory-semantics)
    - [Failure Model and Error Categories](#failure-model-and-error-categories)
    - [Run-Time Failure Conditions](#run-time-failure-conditions)
  - [Source Text and Lexical Elements](#source-text-and-lexical-elements)
    - [Character Set and Encoding](#character-set-and-encoding)
    - [Comments](#comments)
    - [Whitespace and Layout Rules](#whitespace-and-layout-rules)
    - [Syntactic Diagnostic Conditions](#syntactic-diagnostic-conditions)
    - [Identifiers and Casing Invariants](#identifiers-and-casing-invariants)
    - [Keywords](#keywords)
    - [Numeric Literals](#numeric-literals)
    - [Text and Byte Literals](#text-and-byte-literals)
    - [Boolean and Unit Literals](#boolean-and-unit-literals)
  - [Types and Memory Model](#types-and-memory-model)
    - [Value Types](#value-types)
    - [Shared Object Types](#shared-object-types)
    - [Record Types and Row Polymorphism](#record-types-and-row-polymorphism)
    - [Array, Map, and Tuple Types](#array-map-and-tuple-types)
      - [Collection Extents and Index Types](#collection-extents-and-index-types)
    - [Sum Types and GADTs](#sum-types-and-gadts)
      - [Constructor-Tuple Equivalence Invariant](#constructor-tuple-equivalence-invariant)
    - [Nominal Type Wrappers](#nominal-type-wrappers)
    - [Deep Immutability](#deep-immutability)
    - [Type Identity and Subtyping](#type-identity-and-subtyping)
    - [Complete Provenance and Required Annotations](#complete-provenance-and-required-annotations)
    - [Access Mode Inference with via and infer](#access-mode-inference-with-via-and-infer)
      - [Member Modes and Implicit Schema Parameters](#member-modes-and-implicit-schema-parameters)
      - [Inference Domains and Contract Completion](#inference-domains-and-contract-completion)
      - [Preserving Reception and Forwarding](#preserving-reception-and-forwarding)
      - [Lexical Mode Templates and Closures](#lexical-mode-templates-and-closures)
      - [Inferred Interfaces and Callable Families](#inferred-interfaces-and-callable-families)
    - [Functional Updates via Derive](#functional-updates-via-derive)
      - [Normative Rules for Functional Updates](#normative-rules-for-functional-updates)
    - [Generic Parameters, Defaults, and Value Sorts](#generic-parameters-defaults-and-value-sorts)
    - [Type Definition Boundaries](#type-definition-boundaries)
  - [Static Semantics and Type Kernel](#static-semantics-and-type-kernel)
    - [Static Contexts and Judgment Forms](#static-contexts-and-judgment-forms)
    - [Type Formation and Binding](#type-formation-and-binding)
    - [Definitional Equality and Recursive Types](#definitional-equality-and-recursive-types)
    - [Subtyping, Reception, and Contract Compatibility](#subtyping-reception-and-contract-compatibility)
    - [Bidirectional Expression Checking](#bidirectional-expression-checking)
    - [Structural Joins and Normal Continuations](#structural-joins-and-normal-continuations)
    - [Generic Evidence and Definition Checking](#generic-evidence-and-definition-checking)
    - [Pattern Evidence and GADT Branches](#pattern-evidence-and-gadt-branches)
    - [Anonymous Generalization and Fixed Storage](#anonymous-generalization-and-fixed-storage)
    - [Authority, Calls, and Contract Operations](#authority-calls-and-contract-operations)
    - [Recursive Summaries and Grounded Inference](#recursive-summaries-and-grounded-inference)
    - [Phase Checking and Static Evaluation](#phase-checking-and-static-evaluation)
    - [Semantic Interfaces and Diagnostic Boundaries](#semantic-interfaces-and-diagnostic-boundaries)
    - [Core Rule Coverage](#core-rule-coverage)
  - [Declarations and Bindings](#declarations-and-bindings)
    - [Binding Modes and Storage Matrix](#binding-modes-and-storage-matrix)
      - [Reachable Authority Use](#reachable-authority-use)
    - [Construction-Qualified Locals and Mode-Preserving Reception](#construction-qualified-locals-and-mode-preserving-reception)
    - [Shared Writable Authority](#shared-writable-authority)
    - [Immutable Bindings](#immutable-bindings)
    - [Pinned Mutable Handles](#pinned-mutable-handles)
      - [Normative Rules for Pinned Handles](#normative-rules-for-pinned-handles)
    - [Reassignable Mutable Variables](#reassignable-mutable-variables)
      - [Normative Rules for Reassignable Variables](#normative-rules-for-reassignable-variables)
    - [Scoped Resource Bindings](#scoped-resource-bindings)
      - [Normative Rules for Scoped Bindings](#normative-rules-for-scoped-bindings)
    - [Read-Only Reference Bindings](#read-only-reference-bindings)
      - [Normative Rules for Read-Only References](#normative-rules-for-read-only-references)
    - [Type Declarations and Opaque Types](#type-declarations-and-opaque-types)
      - [Declaration Metadata Attributes](#declaration-metadata-attributes)
    - [External Interface Declarations](#external-interface-declarations)
      - [Normative Rules for External Interface Modules](#normative-rules-for-external-interface-modules)
  - [Expressions and Operators](#expressions-and-operators)
    - [Expression Grammar](#expression-grammar)
      - [Expression Holes](#expression-holes)
    - [Operator Precedence and Associativity](#operator-precedence-and-associativity)
    - [Arithmetic Operators](#arithmetic-operators)
    - [Explicit Numeric Conversions](#explicit-numeric-conversions)
    - [Bitwise and Shift Operators](#bitwise-and-shift-operators)
    - [Relational and Equality Operators](#relational-and-equality-operators)
      - [Value Tests with is](#value-tests-with-is)
    - [Logical Operators](#logical-operators)
    - [Range and Sequence Indexing Expressions](#range-and-sequence-indexing-expressions)
    - [Text and Byte Operations](#text-and-byte-operations)
    - [Pipeline Operators](#pipeline-operators)
    - [Error and Fallback Operators](#error-and-fallback-operators)
    - [Record Construction and Spread Update](#record-construction-and-spread-update)
    - [Assignments and Compound Assignments](#assignments-and-compound-assignments)
  - [Control Flow and Pattern Matching](#control-flow-and-pattern-matching)
    - [Block Expressions, Tail Values, and Hoisted Declarations](#block-expressions-tail-values-and-hoisted-declarations)
      - [Block Expressions and Scope Invariants](#block-expressions-and-scope-invariants)
    - [Conditional Expressions](#conditional-expressions)
    - [Loop Expressions](#loop-expressions)
    - [Control Transfers](#control-transfers)
    - [Guarded Bindings and Non-Vacuous Invariant](#guarded-bindings-and-non-vacuous-invariant)
    - [Pattern Matching](#pattern-matching)
    - [Pattern Syntax, Or-Patterns, and Exhaustiveness](#pattern-syntax-or-patterns-and-exhaustiveness)
    - [Pattern Reception and Decomposition](#pattern-reception-and-decomposition)
    - [Flow-Sensitive Type Narrowing](#flow-sensitive-type-narrowing)
      - [Flow-Sensitive Type Narrowing Rules and Invariants](#flow-sensitive-type-narrowing-rules-and-invariants)
  - [Functions, Closures, and Callables](#functions-closures-and-callables)
    - [Named Function Declarations and Contrast Matrix](#named-function-declarations-and-contrast-matrix)
      - [Dual-Tier Where Invariants](#dual-tier-where-invariants)
      - [Signature Value Contracts](#signature-value-contracts)
    - [Callable Contracts](#callable-contracts)
      - [Mandatory Contract Inference and Completion](#mandatory-contract-inference-and-completion)
      - [Closed and Open Callable Rows](#closed-and-open-callable-rows)
      - [Callable Contract Matching](#callable-contract-matching)
      - [Higher-Order Calls](#higher-order-calls)
    - [Return Construction, Access Modes, and Sources](#return-construction-access-modes-and-sources)
    - [Termination and halt Contracts](#termination-and-halt-contracts)
    - [Parameter Modes, Caller Obligations, and Defaults](#parameter-modes-caller-obligations-and-defaults)
      - [Fresh Construction Parameters](#fresh-construction-parameters)
      - [Homogeneous Storage Authority](#homogeneous-storage-authority)
      - [Verified Storage Handoffs](#verified-storage-handoffs)
      - [Default Parameters and Named Arguments](#default-parameters-and-named-arguments)
    - [Anonymous Functions, Trailing Closures, and Projection Accessors](#anonymous-functions-trailing-closures-and-projection-accessors)
    - [Closures, Factory Signatures, and Lexical Environments](#closures-factory-signatures-and-lexical-environments)
  - [State and Provenance Tracking](#state-and-provenance-tracking)
    - [Local Mutation Purity and Local State Discharge](#local-mutation-purity-and-local-state-discharge)
    - [Parameter Mutation](#parameter-mutation)
    - [Retained Mutable Sharing](#retained-mutable-sharing)
    - [External State Tracking](#external-state-tracking)
    - [State Groups and Captured Layers](#state-groups-and-captured-layers)
    - [Named Function State Contract References](#named-function-state-contract-references)
    - [Closure Environments and Handle Modes](#closure-environments-and-handle-modes)
    - [Law of Exclusivity and Cross-Argument Disjointness](#law-of-exclusivity-and-cross-argument-disjointness)
    - [Monotonic Mode Degradation and Anti-Laundering Matrix](#monotonic-mode-degradation-and-anti-laundering-matrix)
  - [Algebraic Effects and Concurrency](#algebraic-effects-and-concurrency)
    - [Effect Declarations and Operation Signatures](#effect-declarations-and-operation-signatures)
    - [Effect Handlers](#effect-handlers)
    - [Parameterized Handler Applications](#parameterized-handler-applications)
    - [Affine Resumption and Delimited Early Abort](#affine-resumption-and-delimited-early-abort)
    - [Built-in System Effects](#built-in-system-effects)
      - [Normative Rules for Built-in System Effects](#normative-rules-for-built-in-system-effects)
    - [Finite Evaluation with Diverge](#finite-evaluation-with-diverge)
      - [Coverage and Finite Outcomes](#coverage-and-finite-outcomes)
      - [Allowance and Charging](#allowance-and-charging)
    - [Panic Absorption with absorb\_panic](#panic-absorption-with-absorb_panic)
    - [Structured Concurrency and Panic Containment](#structured-concurrency-and-panic-containment)
      - [Task Handles, Movable Guard, and Combinators](#task-handles-movable-guard-and-combinators)
      - [Structured Cancellation and Fault Precedence](#structured-cancellation-and-fault-precedence)
    - [Deterministic Data Parallelism and Divide-and-Conquer Primitives](#deterministic-data-parallelism-and-divide-and-conquer-primitives)
      - [Zero-Copy Read-Only Parallel Inputs](#zero-copy-read-only-parallel-inputs)
      - [In-Place Mutable Parallelism](#in-place-mutable-parallelism)
      - [Parallel Faults, Fatal Visibility, and Budgets](#parallel-faults-fatal-visibility-and-budgets)
    - [Structured Concurrency Channels](#structured-concurrency-channels)
  - [Compile-Time Computation and Finiteness](#compile-time-computation-and-finiteness)
    - [Static Type Values and Type Quotation](#static-type-values-and-type-quotation)
    - [Pure Type Functions and Result Restrictions](#pure-type-functions-and-result-restrictions)
      - [Type-Evaluation Exhaustion Diagnostics](#type-evaluation-exhaustion-diagnostics)
    - [Disjoint Call Families, Evaluation Budgets, and Branch Pruning](#disjoint-call-families-evaluation-budgets-and-branch-pruning)
    - [Static Introspection](#static-introspection)
      - [Coordinate and Variant Introspection (coords, variants)](#coordinate-and-variant-introspection-coords-variants)
      - [Static Coordinate Parameters and Computed Value Projection](#static-coordinate-parameters-and-computed-value-projection)
      - [Universal Constituent Projection](#universal-constituent-projection)
      - [Member Mode Introspection and Retention](#member-mode-introspection-and-retention)
      - [Mapped Record and Tuple Types](#mapped-record-and-tuple-types)
      - [Metadata and Documentation Introspection](#metadata-and-documentation-introspection)
    - [Structural Type Pattern Matching](#structural-type-pattern-matching)
    - [Static Parameter Sorts and Adaptation Rules](#static-parameter-sorts-and-adaptation-rules)
    - [Compile-Time Evaluation and Layout Queries](#compile-time-evaluation-and-layout-queries)
  - [Modules, Program Execution, and Prelude](#modules-program-execution-and-prelude)
    - [Modules and Compilation Units](#modules-and-compilation-units)
    - [Module Imports and Visibility](#module-imports-and-visibility)
      - [Normative Module Import Rules](#normative-module-import-rules)
    - [Top-Level Initialization and Purity](#top-level-initialization-and-purity)
    - [Test Conventions and Execution Protocol](#test-conventions-and-execution-protocol)
    - [Program Entry Point](#program-entry-point)
    - [Prelude Scope](#prelude-scope)
      - [Built-in Foundational Operations](#built-in-foundational-operations)
      - [Normative Rules for Built-in Operations](#normative-rules-for-built-in-operations)
    - [Mandatory Inspection of Fallible Results](#mandatory-inspection-of-fallible-results)
  - [Diagnostic Error Codes Summary](#diagnostic-error-codes-summary)
    - [Source Text, Identifiers, and Syntax](#source-text-identifiers-and-syntax)
    - [Names, Initialization, and Field Identity](#names-initialization-and-field-identity)
    - [Types, Expressions, Generics, and Patterns](#types-expressions-generics-and-patterns)
    - [Parameters, Argument Modes, and Defaults](#parameters-argument-modes-and-defaults)
    - [Bindings, State, Access Modes, and Resource Contracts](#bindings-state-access-modes-and-resource-contracts)
    - [Effects, Resumption, Concurrency, and Escape](#effects-resumption-concurrency-and-escape)
    - [Declaration Contexts, Control Flow, and Fallible Values](#declaration-contexts-control-flow-and-fallible-values)
    - [Static Computation and Finiteness](#static-computation-and-finiteness)
    - [Module Forms, Entry Points, and External Contracts](#module-forms-entry-points-and-external-contracts)

## Notation, Abstract Machine, and Conformance

### Grammar Notation

Grammar productions use EBNF. Lexical character classes use regular-expression notation; other square brackets mean optional syntax. Character categories follow their literal sections and exclude unescaped closing delimiters. `Newline` and `EOF` mean line end and source end.

```ebnf
Production  ::= Expression
Choice      ::= A | B
Sequence    ::= A B
Optional    ::= [ A ]
Repetition  ::= { A }
Terminal    ::= "literal" | 'literal'
Grouping    ::= ( A B )
```

Code examples throughout this specification use inline test annotations:

```ril
let x = 42                             -- OK: valid declaration
let y: str = 42                        -- Error [E0301]: expected type 'str', found 'int'
let arr = [1, 2]
-- let out = arr[5]                    -- Panics: index 5 is outside length 2
```

### Program Conformance

A conforming Ril implementation must:
- Accept programs that satisfy the specified syntax and conservative static judgments, subject to the specified static-evaluation budget.
- Statically reject programs that violate those rules, using the diagnostic codes assigned to the violated conditions.
- Preserve the specified abstract-machine behavior, memory model, and determinism guarantees in every execution.
- Infer complete provenance and callable contracts for every function, require the prescribed source annotations on named definitions, and expose diagnostic explanations and complete inferred contracts, including implicit `Diverge`/`Panic`/`Fatal` and anonymous functions without source annotations. Static validity follows the specified conservative judgments.

### Diagnostic Classification

```ril
let value: str = 1                    -- Error [E0301]: incompatible expression type
let unused_value = 1                  -- OK: valid unused read-only binding
-- let bad_zero = 1 / 0               -- Error [E0361]: constant zero divisor
fn ratio(d: int) -> int { 1 / d }
meta fn static_ratio(d: int) -> int { 1 / d }
-- let quotient = ratio(0)            -- Panics at run time: integer division by zero
-- meta let QUOTIENT = static_ratio(0) -- Error [E0831]: panic during static evaluation
```

An `E` diagnostic rejects a program under a specified syntactic or semantic rule. `Panic` and `Fatal` are implicit non-operational execution effects rather than user algebraic operations; recoverable errors use ordinary `Result` and `Option` data.

An expression incompatible with its required type is `E0301` when no more specific condition applies. For an isolated violation, use the diagnostic assigned by its defining rule. Specific conditions take precedence over general type or syntax diagnostics; for example, an absent record member uses `E0336`, and declaration placement uses its dedicated code. Independent violations may produce multiple diagnostics; their reporting order, secondary diagnostic count, and error recovery are unspecified. Invalid programs must be rejected.

Diagnostic explanations should identify the violated requirement and the relevant source construct. When applicable, they should distinguish expected and actual types, identify the declaration or authority responsible for a restriction, or identify an uncovered case. Suggested changes are advisory and must not claim to preserve intent when they change effects, sharing, ownership of resources, or error handling. Exact wording and presentation are not conformance requirements.

### Abstract Machine and Memory Semantics

Ril executes on an abstract machine with automatic memory management. Operands and arguments evaluate left-to-right in the order prescribed by each construct; short-circuiting and control transfers can skip later evaluation. Numeric operators produce the specified results across targets; the default integer type is arbitrary-precision `int`.

| Memory concern | Required behavior |
| :--- | :--- |
| Survival | Preserve validity for all permitted uses: aliases, environments, prepared arguments, resumptions, cleanup, and foreign retention |
| Reclamation | Automatically reclaim otherwise unreachable ordinary graphs, including cycles. Timing, order, pause bounds, and peak memory bounds are unspecified |
| Identity | Preserve surviving objects' identity, aliases, contents, and access relationships across storage movement and reclamation |
| Authority | Object survival grants no authority and extends no access lifetime; construction, scope, task, and exclusivity rules still apply |
| Source interface | No allocator controls, explicit managed-storage release, reference-count manipulation, physical-address pinning, or reclamation-triggered finalizers |
| User code and resources | Reclamation runs no Ril user code. Resource closing follows [scoped cleanup](#scoped-resource-bindings), independently of reclamation |
| Effects and budgets | Storage management adds no operational or implicit effect (`Diverge`, `Panic`, `Fatal`) and no charged event. Evaluation retains its specified charges and [failures](#run-time-failure-conditions). Source budgets bound neither memory nor pauses |

```ril
-- Strict left-to-right evaluation order across operands and arguments:
let mut trace: []int = []
let mut log = \n -> { trace |> mut Array::push(n); n }
let result = log(1) + log(2) * log(3)  -- Evaluates log(1), then log(2), then log(3)
-- trace is guaranteed to be [1, 2, 3]
```

### Failure Model and Error Categories

```ril
-- 1. Recoverable errors via Result / Option and '?' / '??':
fn parse_id(s: str) -> Result<int, str> {
    if s == "" { Err("empty input") } else { Ok(42) }
}
fn init_session() -> Result<int, str> {
    let id = parse_id("10")?           -- OK: propagated via postfix '?'
    Ok(id)
}
assert(init_session() is Ok(42) && parse_id("") is Err("empty input"))
-- let top_id = parse_id("10")?        -- Error [E0205]: '?' requires an enclosing callable frame
-- parse_id("10")                      -- Error [E0720]: unused Result

-- 2.Bounded divergence via diverge_budget (discharges implicit @Diverge):
fn spin() -> int { loop {} }
halt fn bounded() -> Result<int, BudgetError> {
    with diverge_budget(1_000)
    spin()
}
assert(bounded() is Err(BudgetError::Exhausted))

-- 3. Absorbable defects (@Panic) and unwind-safe absorption via absorb_panic:
let arr = [10, 20, 30]
assert(arr?[5] == None)                -- Safe lookup returns ?int (no @Panic)
fn read_first(xs: []int) -> int {
    xs[0]                              -- Inferred implicit @Panic
}
fn safe_first(xs: []int) -> Result<int, PanicError> {
    with absorb_panic()                -- Discharges @Panic when unwind-safe (E0608)
    read_first(xs)
}
assert(safe_first([]) is Err(PanicError::Panicked(_)))

-- 4. Unrecoverable process termination (@Fatal):
fn verify_magic(ok: bool) -> () {
    if !ok {
        fatal("corrupted state")       -- Inferred implicit @Fatal; terminates process immediately
    }
}
```

```ril
use ril/concurrent::{scope, fork, TaskFault}
let scope_outcome: Result<int, TaskFault> = {
    with scope()
    let _ = fork \-> panic("worker failure")
    Ok(42)
}
assert(scope_outcome is Err(TaskFault::Panicked(_))) -- Child panic becomes TaskFault
```

| Tier | Representation / implicit effect | Handling / containment |
| :--- | :--- | :--- |
| Recoverable domain error | `Result<T, E>`, `?T` (`Option<T>`) | `?`, `??`, `match`, `is`; unused `Result` is `E0720` |
| Bounded divergence | Implicit `@Diverge` | [`diverge_budget`](#finite-evaluation-with-diverge) $\rightarrow$ `Result<T, BudgetError>` |
| Unwinding defect | Implicit `@Panic` | Synchronous [`absorb_panic`](#panic-absorption-with-absorb_panic) (`E0608`) $\rightarrow$ `Result<T, PanicError>`; child [`fork`](#structured-concurrency-and-panic-containment) $\rightarrow$ `Result<T, TaskFault>` |
| Process termination | Implicit `@Fatal` | None; penetrates `absorb_panic`, `diverge_budget`, handlers, and `scope`, terminating the process immediately |

### Run-Time Failure Conditions

```ril
let smallest: i8 = -128i8              -- OK: representable signed literal
-- let too_large = 128i8               -- Error [E0326]: unrepresentable literal
let wrapped = 127i8 + 1i8              -- OK: -128i8 (fixed-width arithmetic wraps modulo 2^N)
let min_div = -128i8 / -1i8            -- OK: -128i8 (two's-complement wrap)
let huge = 9_223_372_036_854_775_807 * 10 -- OK: exact arbitrary-precision int
-- let const_zero = 1 / 0              -- Error [E0361]: constant zero divisor
let safe = 1 /? 0                      -- OK: None
let ieee = 1.0 / 0.0                   -- OK: positive infinity
-- meta let CHECK = assert(false)      -- Error [E0830]: static assertion failure
-- meta let FAIL = panic("bad")        -- Error [E0831]: static evaluation panic
```

| Condition when evaluated | Implicit effect | Outcome |
| :--- | :--- | :--- |
| `panic(message)` | `@Panic` | Begin LIFO panic unwinding with `message` |
| False `assert` condition | `@Panic` | Assertion panic unwinding |
| Dynamic integer `/` or `%` with zero divisor | `@Panic` | Division-by-zero panic (statically proven nonzero divisors add no `@Panic`; constant zero is `E0361`) |
| Ordinary array element index `arr[i]` outside bounds | `@Panic` | Index-bounds panic |
| Negative, reversed, or out-of-bounds sequence range `s[a..b]` | `@Panic` | Range-bounds panic under [range indexing](#range-and-sequence-indexing-expressions) |
| Allocation or growth beyond [collection extent](#collection-extents-and-index-types) | `@Panic` | Collection-size panic before committing the change |
| Foreign defect mapped at `.d.ril` boundary | `@Panic` | Panic at that boundary |
| `fatal(message)` | `@Fatal` | Write diagnostic to stderr and terminate the OS process immediately without unwinding or cleanup |
| Secondary panic inside cleanup during active panic, cancellation, or abort | `@Fatal` | `DoubleFaultFatal`; abandon remaining cleanup and terminate the OS process immediately |
| Unrecoverable host memory or stack exhaustion | None added to signatures | Immediate process termination |

In required static evaluation (`meta let`, `meta fn`, `type` functions), a false `assert` is `E0830`, and `panic`, `fatal`, or any run-time defect condition above aborts static evaluation with `E0831`.

| Abnormal control or cleanup condition | Consequence |
| :--- | :--- |
| Effect arm completes without resumption | Delimited abort; prior writes remain committed and scoped cleanup runs |
| Structured cancellation | Non-resumable unwinding at `@Fiber` cancellation points under the [scope](#structured-cancellation-and-fault-precedence) and [channel](#structured-concurrency-channels) rules |
| Cleanup panics during normal exit | Begin panic unwinding through the remaining resources |
| Cleanup panics during panic, cancellation, or effect abort | `DoubleFaultFatal`: immediate `@Fatal` process termination |

Scoped cleanup is LIFO within each unwound frame. A task boundary contains child `@Panic` faults, not a panic from its own parent frame and never `@Fatal`. Parallel evaluation exposes only faults visible in its specified reference order; a skipped branch cannot fail a successful result, and direct `fatal` is rejected in [parallel callbacks](#parallel-faults-fatal-visibility-and-budgets).

## Source Text and Lexical Elements

### Character Set and Encoding

Source text is encoded in UTF-8. Case is significant.

```text
Source bytes: FF                      -- Error [E0104]: not a UTF-8 source sequence
```

```ril
-- let value = $                     -- Error [E0105]: no token admits '$' here
let text = "$"                       -- OK: admitted string content
```

Ill-formed UTF-8 is `E0104`. A decoded character that cannot occur in any token at its source position is `E0105`. String, raw-string, and comment contents follow their lexical rules; identifier casing and spelling use `E0101`/`E0102`.

### Comments

```ebnf
DocComment   ::= ( "--|" | "--!" ) { SourceChar } ( Newline | EOF )
LineComment  ::= "--" { SourceChar } ( Newline | EOF )
BlockComment ::= "{-" { SourceChar | BlockComment } "-}"
```

```ril
--! HTTP request routing and query parsing.
-- Single-line comment to end of line
{- Block comment {- nested block comment -} continues -}

--| Search options exposed to tool callers.
pub type SearchArgs(.{
    --| Query text matched against document titles.
    query: str,
})
-- --| let local = 1                  -- Error [E0708]: doc comment requires an eligible declaration
```

Every opened block comment requires a matching `-}`; reaching the end of source with an open comment is `E0106`.

| Comment form | Attachment / scope |
| :--- | :--- |
| `--` / `{- ... -}` | Ignored whitespace trivia; `---` remains an ordinary line comment |
| `--! text` | Inner documentation at the start of a file or inline `sub` body (`E0708` elsewhere) |
| `--\| text` | Outer documentation attached to the immediately following declaration, `NominalDecl` record field, sum variant, or effect operation (`E0708` on statements or unattached trailing lines) |

Consecutive doc-comment lines of the same kind concatenate with `\n`, stripping one optional leading space (`0x20`) after `--|` or `--!`. Documentation carries no execution semantics and may be queried at compile time via [`Reflect`](#metadata-and-documentation-introspection).

### Whitespace and Layout Rules

```ril
-- Semicolon as explicit expression separator:
let a = 1; let b = 2                   -- OK: explicit semicolon separator

-- Implicit expression terminator: newlines terminate statements unless continuing:
let x = 10
let y = 20

-- Multiline expression continuation via trailing operators:
let total = 10 +
    20 +
    30                                 -- OK: trailing '+' continues expression to next line

-- Multiline expression continuation via leading pipeline operators:
let pipeline_res = [1, 2, 3]
    |> Array::map(\n -> n * 2)         -- OK: leading '|>' continues expression
    |> Array::filter(\n -> n > 2)

-- Block expressions: final expression without semicolon is the block value:
let c = {
    let base = 100
    base + y                           -- Block evaluates to 120
}
let d = {
    let base = 100;                    -- Trailing semicolon discards value
}                                      -- Block evaluates to ()
```

Spaces and tabs separate tokens. A newline ends a complete statement except below:

| Context | Newline rule |
| :--- | :--- |
| Parentheses, brackets, committed type quotes/patterns and generic lists, record/declaration fields | Whitespace; nested executable blocks keep their own boundaries |
| Trailing operator, comma, `=`, `:`, `->` | Continue the required operand or body |
| Callable declaration/type head through its effect/state annotations, return annotation, signature `where`, and required body | Remain one head across newlines; the first body brace follows the complete head |
| Required declaration body, `else`, `where` | Stay attached to the preceding construct |
| Leading `\|>`, `??` | Continue the preceding expression |
| Other leading operators or `(` | Do not reopen a completed statement |

`;` separates statements and discards their values. The final expression before `}` or `where` is the block value unless followed by `;`; a newline preserves it. Empty blocks and binding-ended blocks yield `()`.

### Syntactic Diagnostic Conditions

```ril
-- let value = )                     -- Error [E0120]: unexpected token, with no matching opener
-- let pair = (1, 2]                 -- Error [E0123]: ']' cannot close '('
-- let values = [1 2]                -- Error [E0124]: missing comma between elements
```

```ril
-- Error [E0121]: an initializer is required at end of source
let value =
```

```ril
-- Error [E0122]: the array's closing delimiter is missing at end of source
let values = [1, 2
```

| Condition | Diagnostic |
| :--- | :--- |
| Unexpected token with no more specific lexical, delimiter, or construct restriction | `E0120` |
| End of source where a required constituent is missing, with no open delimiter | `E0121` |
| Open syntactic delimiter at end of source, including a committed type quote/pattern or generic list | `E0122` |
| Closing delimiter disagrees with its corresponding opener | `E0123` |
| A required separator or other grammar token is absent between otherwise identifiable constituents | `E0124` |

Unterminated literals and comments use their lexical diagnostics rather than `E0121`/`E0122`. `E0124` does not make a token mandatory where the grammar or newline rules permit omission. Malformed interpolation uses `E0112` for its own braces, empty expression, or format syntax; an independently invalid embedded expression retains its ordinary diagnostic.

### Identifiers and Casing Invariants

```ebnf
Identifier         ::= PascalCase | ValueName | ScreamingSnakeCase
ValueName          ::= SnakeCase | UnderscoreName
PascalCase         ::= [A-Z] { [a-zA-Z0-9] }
SnakeCase          ::= [a-z] [a-z0-9]* { "_" [a-z0-9]+ }
ScreamingSnakeCase ::= [A-Z] [A-Z0-9]* { "_" [A-Z0-9]+ }
UnderscoreName     ::= "_" [a-z] [a-z0-9]* { "_" [a-z0-9]+ }
Wildcard           ::= "_"
QualifiedName    ::= { "Super" "::" } { PascalCase "::" } Identifier
```

Identifier grammatical roles obey the **Closed Casing Invariant**:

- **`PascalCase`**: Reserved for types (`type`), sum type variant constructors, nominal wrappers, algebraic effects (`eff`), generic type parameters (`T`, `ItemType`), and `sub` namespace identifiers (`Array`, `Channel`, `Geometry`, `Super`).
   - **Acronym Title-Casing Rule**: Acronyms within `PascalCase` must be title-cased as regular words (`HttpServer`, `UserId`, `JsonParser`, not `HTTPServer`, `UserID`, `JSONParser`) (`E0102`).
- **`snake_case`**: Used for run-time variables (local bindings, function parameters, reassignable variables `var`, and pinned mutable handles `let mut`), const generic parameters (`cap: int`), named functions (`fn`, `meta fn`), record fields, and module file path segments (`ril/array`, `math/geometry`).
- **`SCREAMING_SNAKE_CASE`**: Reserved for compile-time constants (`meta let`) and top-level immutable constants (`let`). Top-level mutable variables (`var`, `let mut`, `let ^mut`, and `var ^mut`) must use `snake_case`.
- **Static Keys and Field Labels**: Static coordinate parameters (`meta key |> Key<T>` or `meta key: str |> Key<T>`), const generic keys, and mapped comprehension patterns (`[coords(<T>) as (m, k)]`) use `snake_case`. Ordinary record field labels use `snake_case`, optionally with one leading underscore. A mapped record generated from sum variants exposes `PascalCase` variant labels verbatim.
- **Wildcard and Leading Underscores**: A single underscore `_` is the wildcard discard pattern, not an identifier (`E0322`). An identifier with a leading underscore, such as `_snake_case`, follows the same binding and mutable-authority use requirements as other identifiers (`E0527`).

```ril
type First { Shared }
type Second { Shared }
let first: First = First::Shared       -- OK: qualified constructor
-- let ambiguous: First = Shared      -- Error [E0206]: expected type does not resolve the abbreviation
type Maybe<T> = Option<T>
let value: Maybe<int> = Some(1)        -- OK: an alias adds no constructor candidate
```

Declarations and imports share one namespace. Same-scope duplicates are `E0203`; inner declarations may shadow outer ones, including the enclosing prelude. The intrinsic static type family `Type` and parent-scope navigator `Super` are protected against user declarations, `sub` names, type binders, and import aliases that would redefine or shadow them (`E0203`).

| Name | Resolution |
| :--- | :--- |
| Nominal type/constructor; predefined `Set<T>`/`Set::from`; `Concurrent` effect/`ril/concurrent` | Roles of one declaration; separate user declarations cannot merge |
| `S::V` | Variant member of S; no second enclosing-scope declaration |
| Unqualified constructor name | Ordinary lexical binding first; otherwise require one variant candidate (`E0206` if ambiguous) |
| Candidate set | Directly visible sum types; a module import alone does not expose its internal sums |
| Aliases and re-exports | Deduplicate candidates by variant declaration identity |
| Expected type / generic arguments | Expected types never choose a declaration; infer/check arguments after selection |

```ril
-- PascalCase: Types, Constructors, Effects, and Generic Parameters
type UserAccount = .{ id: int }         -- OK: type identifier
type Result<T, E = str> { Ok(T), Err(E) } -- OK: generic parameters and constructors
eff FileIo { read() -> str }           -- OK: effect identifier
type HttpServerConfig = .{ port: int }  -- OK: title-cased acronym

-- snake_case: Variables (local, param, top-level var / let mut), Functions, and Fields
let user_count = 10                    -- OK: local variable identifier
var total_score = 0                    -- OK: local reassignable variable
total_score += 1
var active_workers = 0                 -- OK: top-level reassignable mutable variable
fn start_worker() &up(sub){mut active_workers} -> () { active_workers += 1 }
fn compute_area(width: f64) -> f64 { width * 2.0 } -- OK: function identifier
meta fn pad_align(size: int) -> int { size }       -- OK: compile-time function

-- SCREAMING_SNAKE_CASE: meta let and Top-Level Immutable Variables ONLY
meta let MAX_BUFFER_SIZE = 1024 * 64   -- OK: compile-time constant
let DEFAULT_TIMEOUT_MS = 5000          -- OK: top-level immutable constant

-- Wildcard and Leading-Underscore Identifiers
let _ = user_count                     -- OK: wildcard discard
fn on_event(ev: Event, _ctx: Context) -> () { handle(ev) } -- OK: '_ctx' is a parameter identifier

-- Static Lexical Violations:
-- type user_doc = .{ id: int }         -- Error [E0101]: type identifier must be PascalCase, found 'user_doc'
-- fn Calculate() -> () {}             -- Error [E0101]: function identifier must be snake_case, found 'Calculate'
-- let UserCount = 10                  -- Error [E0101]: variable identifier must be snake_case, found 'UserCount'
-- meta let max_size = 100             -- Error [E0101]: compile-time constant must be SCREAMING_SNAKE_CASE, found 'max_size'
-- var ACTIVE_FLAG = true              -- Error [E0101]: top-level mutable variable must be snake_case, found 'ACTIVE_FLAG'
-- type HTTPServer = .{ port: int }     -- Error [E0102]: acronym in PascalCase must be title-cased, expected 'HttpServer', found 'HTTPServer'
-- let user__name = "Alice"            -- Error [E0102]: consecutive underscores are prohibited, found 'user__name'
-- let Some(USER_ID) = opt             -- Error [E0103]: pattern binding position cannot use uppercase identifier 'USER_ID'
-- let _ = 10; println(_)              -- Error [E0322]: wildcard '_' cannot be evaluated as an expression
```

### Keywords

The following 30 keywords are reserved in all ordinary identifier and field-label positions:

```text
as       eff      else     false    fn
for      halt     if       is       last
let      loop     match    meta     mut
new      next     pub      ref      resume
return   sub      true     type     typeof
use      var      where    while    with
```

```ril
-- let while = 1                     -- Error [E0113]: reserved keyword in a binding position
-- let new = 1                       -- Error [E0113]: new is reserved for construction annotations/handoffs
-- type Record = .{ if: int }         -- Error [E0113]: reserved keyword as a field label
let while_count = 1                   -- OK
let capture = 1                       -- OK: capture is an ordinary identifier
let closure = 1                       -- OK: closure is an ordinary identifier
let up = 1                            -- OK: up is an ordinary identifier
-- let sub = 1                       -- Error [E0113]: reserved keyword
-- let halt = 1                       -- Error [E0113]: reserved keyword
let scoped = 2                        -- OK: ordinary identifier
let opaque = 3                        -- OK: ordinary identifier
-- let meta = 4                       -- Error [E0113]: reserved keyword
-- let pub = 5                        -- Error [E0113]: reserved keyword
let in = 1                            -- OK: ordinary identifier
-- let never = 6                      -- Error [E0113]: intrinsic primitive type name
-- let int = 0                        -- Error [E0113]: intrinsic primitive type name
-- let i64 = 0                        -- Error [E0113]: intrinsic primitive type name
-- fn invalid(bool: int) -> () {}     -- Error [E0113]: intrinsic primitive type name
-- type InvalidField = .{ str: bool }  -- Error [E0113]: intrinsic primitive type name
assert(scoped + opaque + in == 6)
type Bottom = never                   -- Intrinsic bottom type in type syntax
type Config = .{
    capture: bool, up: bool,
    scoped: bool, opaque: bool, in: bool,
    via: bool, infer: bool,
}                                     -- OK: ordinary field labels
```

A reserved keyword or intrinsic primitive type name used as an ordinary identifier or field label is `E0113`.

Contextual keywords are identifiers outside the forms below. Recognize each form by its grammatical position and required following tokens before name resolution. Each form follows its defining production's placement and semantic rules; ordinary names and field labels follow the [casing rules](#identifiers-and-casing-invariants).

| Word | Contextual form | Meaning |
| :--- | :--- | :--- |
| `opaque` | `opaque type`, after optional visibility | [Hidden type representation](#type-declarations-and-opaque-types) |
| `scoped` | Binding modifier in `let scoped [mut] Pattern` | [Scope-exit resource cleanup](#scoped-resource-bindings) |
| `via` | Declared member/access mode, parameter mode, or `let via name` receiver | [Static mode parameters and dependent reception](#access-mode-inference-with-via-and-infer) |
| `infer` | Return modifier in `-> infer T` on a signature with explicit `via` inputs | [Inferred result access modes, sources and dependencies](#return-construction-access-modes-and-sources) |
| `capture` | `&capture` | [Surviving environment creation](#closures-factory-signatures-and-lexical-environments) |
| `up` | `&up`, `&up{...}`, or `&up(owner){...}` | [Callable environment abstraction or named-source access](#state-groups-and-captured-layers) |

In `&up(owner){...}`, `sub` selects the current module's storage, a module path or `Super` selects another module's storage, and a lowercase identifier selects an enclosing callable layer. Invalid mode-inference placements use `E0412` under [access mode inference](#access-mode-inference-with-via-and-infer).

Primitive type spellings listed under [Value Types](#value-types), including `never`, are reserved type names. They denote their intrinsic types and are unavailable as ordinary identifiers or field labels (`E0113`).

```ril
-- Reserved and contextual keywords in action:
pub opaque type Token = int            -- 'pub', 'opaque', 'type'
meta let COMPILE_ID = 101              -- 'meta', 'let'
eff Logger { log(str) -> () }          -- 'eff'
use ril/array::{push}                  -- 'use'
halt fn finite_step() -> bool { true } -- 'halt', 'true', 'fn'
use ril/file
use ril/io::{IoError}
fn manage_resource() @Fiber -> Result<(), IoError> {
    let scoped mut res = File::open("a.txt")?  -- 'scoped', '?' inside function frame
    let ref v = res                       -- 'ref' in handle binding
    with Logger::log(msg) -> resume ()     -- 'with', 'resume' (statement-level handler)
    Ok(())
}

fn calculate(val: ?int) -> int {       -- 'fn'
    let bound = match val {            -- 'let', 'match'
        Some(x) if x > 0 -> x,         -- 'if'
        _ -> 0,
    }
    let is_positive = bound is 1..=10  -- 'is'
    var sum = 0                        -- 'var'
    for [1, 2, 3] as n {               -- 'for', 'as'
        sum += n
        if sum > 10 { last }           -- 'last'
        else { next }                  -- 'else', 'next'
    }
    while false { loop {} }            -- 'while', 'false', 'loop'
    bound                              -- tail expression
where                                  -- 'where' inside block
    type Dummy = never                 -- Intrinsic bottom type
}
```

### Numeric Literals

```ebnf
IntLiteral     ::= DecimalLiteral | HexLiteral | OctalLiteral | BinaryLiteral
DecimalLiteral ::= Digit { [ "_" ] Digit } [ [ "_" ] IntSuffix ]
HexLiteral     ::= "0" ( "x" | "X" ) HexDigit { [ "_" ] HexDigit } [ [ "_" ] IntSuffix ]
OctalLiteral   ::= "0" ( "o" | "O" ) OctalDigit { [ "_" ] OctalDigit } [ [ "_" ] IntSuffix ]
BinaryLiteral  ::= "0" ( "b" | "B" ) BinaryDigit { [ "_" ] BinaryDigit } [ [ "_" ] IntSuffix ]
IntSuffix      ::= "int" | "i8" | "i16" | "i32" | "i64" | "u8" | "u16" | "u32" | "u64"
FloatLiteral   ::= Digit { [ "_" ] Digit } "." Digit { [ "_" ] Digit } [ Exponent ] [ [ "_" ] FloatSuffix ]
Exponent       ::= ( "e" | "E" ) [ "+" | "-" ] Digit { Digit }
FloatSuffix    ::= "f32" | "f64"
Digit           ::= [0-9]
HexDigit        ::= [0-9a-fA-F]
OctalDigit      ::= [0-7]
BinaryDigit     ::= "0" | "1"
```

```ril
-- let bad_digit = 0b102              -- Error [E0111]: digit is not in the selected base
-- let bad_separator = 1__0          -- Error [E0111]: separators must separate digits
-- let bad_exponent = 1.0e+          -- Error [E0111]: exponent requires digits
-- let bad_suffix = 12u7             -- Error [E0111]: unsupported numeric suffix
let valid_digit = 0b10                -- OK
```

A numeric literal violating its base, digit, separator, exponent, or suffix production is `E0111`. A well-formed integer literal whose value does not fit its selected type is `E0326`; this is distinct from overflow while evaluating arithmetic. An immediately applied minus participates in the literal range check.

```ril
let decimal = 1_000_000                -- Type: int
let hex_val = 0xFF_AA                  -- Type: int
let oct_val = 0o755                    -- Type: int (octal)
let bin_val = 0b1010_0110              -- Type: int (binary)
let explicit_int = 42_int              -- Type: int
let big_num = 123456789012345678901234567890 -- Type: int (arbitrary precision)
let explicit_u8 = 255u8                -- Type: u8
let explicit_i16 = -32_i16             -- Type: i16
let float_val = 3.14159_f64            -- Type: f64
let float_f32 = 2.5f32                 -- Type: f32
let scientific = 1.25e-4               -- Type: f64 (exponent)
let smallest: i8 = -128i8              -- OK: signed literal is checked as a whole
-- let too_large: i8 = 128i8           -- Error [E0326]: literal is outside its selected type's range
-- let mixed = 1u8 + 1u16              -- Error [E0301]: no implicit numeric promotion
```

| Form | Type / check |
| :--- | :--- |
| Suffixed literal | Suffix fixes the type |
| Unsuffixed integer | Compatible numeric context, otherwise `int`; round once if selected as floating-point |
| Unsuffixed float | Contextual `f32`/`f64`, otherwise `f64` |
| Fixed-width integer literal | Must fit its selected type (`E0326`); an immediately applied `-` is included in the range check |
| Negating an evaluated fixed-width minimum | Wraps modulo $2^N$ (`MIN` yields `MIN`) |
| Numeric arithmetic/comparison | Same operand type (`E0301`); no conversion of already typed values |
| Shift count | `u32` |

### Text and Byte Literals

```ebnf
StringLiteral     ::= '"' { StringCharacter | EscapeSequence | Interpolation } '"'
RawStringLiteral  ::= { "#" } '`' { RawCharacter } '`' { "#" }
ByteStringLiteral ::= 'bytes"' { ByteCharacter | ByteEscape } '"'
                    | "bytes" RawByteLiteral
RawByteLiteral    ::= { "#" } '`' { RawByteCharacter } '`' { "#" }
Interpolation     ::= "{" Expression [ ":" FormatSpec ] "}"
FormatSpec        ::= [ FillAlign ] [ Width ] [ "." Precision ] [ FormatType ]
FillAlign         ::= [ SourceChar ] ( "<" | "^" | ">" )
Width             ::= Digit { Digit }
Precision         ::= Digit { Digit }
FormatType        ::= "x" | "X" | "b" | "o" | "e" | "f" | "s"
```

```ril
-- let escape = "\q"                  -- Error [E0108]: unsupported escape
-- let scalar = "\u{D800}"            -- Error [E0109]: surrogate is not a Unicode scalar
-- let byte_value = bytes"\xG0"       -- Error [E0110]: byte escape requires two hex digits
-- let non_ascii = bytes"é"           -- Error [E0110]: non-ASCII byte-literal character
-- let raw_non_ascii = bytes`é`       -- Error [E0110]: non-ASCII raw byte-literal character
-- let empty = "value: {}"            -- Error [E0112]: interpolation requires an expression
-- let format = "{1:04q}"             -- Error [E0112]: malformed format specifier
-- let open = "value: {1"             -- Error [E0112]: interpolation lacks its closing brace
let braces = "{{value}}"              -- OK: literal braces
let scalar = "\u{1F642}"              -- OK: Unicode scalar
```

```ril
-- Error [E0107]: string delimiter remains open at end of this source fragment
let text = #`unfinished`
```

An unclosed ordinary, raw, or byte string is `E0107`. Unsupported or malformed ordinary-string escapes are `E0108`; a syntactically well-formed Unicode escape outside the scalar range, including surrogates, is `E0109`. Invalid byte-literal contents or escapes are `E0110`. A recognized interpolation's malformed braces, absent expression, or malformed format syntax is `E0112`; a valid format incompatible with the interpolated type is `E0329`.

```ril
let word = "Ada"
-- let text = "{word:x}"             -- Error [E0329]: integer format applied to str
let text = "{42:x}"                   -- OK
```

```ril
let greeting = "Hello, world!\n"                  -- Type: str
let name = "Alice"
let pi = 3.1415926
let count = 42

let msg1 = "User: {name:>10}"                     -- "User:      Alice"
let msg2 = "Pi: {pi:.2f}"                         -- "Pi: 3.14"
let msg3 = "Hex: 0x{count:04x}"                   -- "Hex: 0x002a"
let raw_path = `C:\new\folder\test`               -- Raw str: no escapes or interpolation
let raw_quote = #`contains `backticks` and {x}`#  -- Multi-delimiter raw str
let raw_nested = ##`embeds #`inner`# delimiter`## -- Closes only on `##
let binary_data = bytes"RIFF\x00\x01\xFF"         -- Escaped bytes literal
let raw_bytes = bytes`GET / HTTP/1.1`             -- Raw ASCII bytes literal
let raw_delim_bytes = bytes#`raw "a" and `b``#    -- Multi-delimiter raw ASCII bytes
```

| Literal form | Delimiter & content rules |
| :--- | :--- |
| `"..."` (`str`) | Unicode scalars; escapes `\n`, `\r`, `\t`, `\0`, `\\`, `\"`, `\u{hex_digits}`; `{{` / `}}` literal braces; `{expr:spec}` interpolation |
| `` `...` ``, `` #`...`# `` (`str`) | Opens with `k >= 0` `#` plus `` ` `` and closes only at `` ` `` plus `k` `#`; no escapes or interpolation; multiline `CRLF` normalizes to `LF` |
| `bytes"..."` (`bytes`) | Printable ASCII (`0x20..=0x7E` except `"` and `\`) plus `\n`, `\r`, `\t`, `\0`, `\\`, `\"`, `\xHH` (two hex digits); no interpolation |
| `` bytes`...` ``, `` bytes#`...`# `` (`bytes`) | `bytes` prefix immediately followed by raw delimiter (`k >= 0` `#`); ASCII bytes only (`E0110` on non-ASCII), no escapes, multiline `CRLF` normalizes to `LF` |

Combine strings and values with interpolation, such as `"Hello, {name}"`. Arithmetic operators do not perform string conversion or concatenation.

```ril
assert("{-42:05}" == "-0042")
assert("{1.25:.1f}" == "1.2")          -- Decimal rounding: nearest, ties to even
assert("{12.5:.2e}" == "1.25e1")
assert("{1.0:.0f}" == "1")
assert("{-0.0}" == "-0.0")
assert("{true}" == "true")
let text = "é🙂x"
assert("{text:.2s}" == "é🙂")
```

| Value type | Admitted format | Precision |
| :--- | :--- | :--- |
| `str` | Omitted or `s`; unchanged scalar sequence | Maximum output scalars; truncate before padding |
| `bool` | Omitted; `true` or `false` | Not admitted |
| Integer | Omitted decimal, `b`, `o`, `x`, `X` | Not admitted |
| `f32` / `f64` | Omitted, `e`, `f` | Only `e`/`f`; digits after the decimal point, default 6 |
| Other types, including wrappers | None; unwrap or convert explicitly | `E0329` |

| Floating conversion | Rule |
| :--- | :--- |
| Omitted type and precision | Shortest round-tripping decimal; among equally short candidates choose the closest value, then an even final digit |
| Default notation | Fixed for decimal exponents -6 through 20, scientific otherwise; fixed integer-like output includes `.0` |
| `f` | Round the exact represented value to the requested digits after the decimal point, nearest with ties to even |
| `e` | Normalize to a coefficient with one integer digit; round its fractional digits nearest with ties to even; a carry to ten renormalizes and increases the exponent |
| Precision zero | Omit the decimal point |
| Scientific output | Lowercase `e`; exponent has no leading zeros or positive sign; zero has exponent zero |
| Special values / sign | `nan`, `inf`, `-inf` independent of precision; preserve negative zero including after rounding |

| Layout property | Rule |
| :--- | :--- |
| Width | Minimum Unicode scalar count after conversion/truncation; never truncates |
| Default alignment / fill | Numbers right, other admitted values left; space fill |
| `<` / `>` / `^` | Left / right / center; odd center padding puts the extra scalar on the right |
| Explicit fill | One scalar other than a brace or line break; requires alignment |
| Numeric width beginning with zero | Zero-pad after a minus sign, unless explicit fill/alignment is present; special floats use spaces |
| Integer output | Sign plus magnitude, no prefix; `X` uses uppercase digits, other bases lowercase |
| Width / precision bounds | Nonnegative decimal values in `0..=0x7FFF_FFFF_FFFF_FFFF`; otherwise malformed format (`E0112`) |
| Unsupported type/format/precision combination | `E0329`; formatting invokes no user conversion |

Each interpolation expression evaluates once in source order. An empty format specifier is the default format. These conversions are available in both evaluation phases.

### Boolean and Unit Literals

```ril
let is_valid = true                    -- Type: bool
let is_done = false                    -- Type: bool
let unit_val = ()                      -- Type: ()
```

---

## Types and Memory Model

### Value Types

```ebnf
PrimitiveType    ::= "bool" | "int" | "i8" | "i16" | "i32" | "i64"
                  | "u8" | "u16" | "u32" | "u64"
                  | "f32" | "f64" | "str" | "bytes" | "(" ")" | "never"
```

Value types have copy-by-value semantics, regardless of their implementation representation.

| Category | Types | Description |
| :--- | :--- | :--- |
| Boolean | `bool` | Truth value (`true` or `false`) |
| Arbitrary-Precision Integer | `int` | Unbounded signed integer; default integer type |
| Fixed-Width Signed Integers | `i8`, `i16`, `i32`, `i64` | Two's-complement $N$-bit signed integers |
| Fixed-Width Unsigned Integers | `u8`, `u16`, `u32`, `u64` | $N$-bit unsigned integers |
| Floating-Point | `f32`, `f64` | IEEE 754 floating-point numbers |
| Text & Data | `str`, `bytes` | Immutable UTF-8 text string, immutable raw byte sequence |
| Integer ranges | `typeof (0..0)` | Immutable integer interval bounds |
| Unit | `()` | Zero-element tuple with the single value `()` |
| Bottom | `never` | Empty uninhabited type |

| Integer property | Rule |
| :--- | :--- |
| Signed width N | $-2^{N-1}$ through $2^{N-1}-1$ |
| Unsigned width N | Zero through $2^N-1$ |
| `i64` layout | Eight bytes on every target |

```ril
let a: int = 42
var b = a
b += 1
assert(a == 42 && b == 43)

-- let mut bad = a                    -- Error [E0402]: use var for value updates
-- let ref bad = a                   -- Error [E0402]: values have no reference target
-- fn bad(ref x: int) -> () {}             -- Error [E0401]: pass values normally
```

Value types, including `str`, `bytes`, and integer ranges, have no shared-object identity and admit no reference/access-mode or construction modifiers:

| Value-type position | Prohibited modes | Diagnostic |
| :--- | :--- | :--- |
| Binding / member / pattern target | Any `mut`, `^mut`, or `ref` mode, with or without `var` | `E0402` |
| Parameter / argument | `mut`, `^mut`, `ref`; `new` | `E0401`; `E0411` |
| Result | `-> new T`; `-> ref(x) T` / `-> ^mut(x) T` | `E0546`; `E0402` |

### Shared Object Types

Arrays (`[]T`), maps (`[K: V]`), records, nonempty tuples, sets, and sum type instances have shared-object identity and may be aliased. Their storage is managed automatically under the [memory semantics](#abstract-machine-and-memory-semantics).

Live access preserves the selected object's identity. Default access exposes immutable snapshot contents, independent of storage identity and sharing. Private construction roots are also shared objects; access modes govern each path.

```ril
-- Shared object types: live object aliasing:
type Node = .{ var val: int }
let mut n1 = Node.{ val: 10 }
let ref n2 = n1                       -- 'n2' observes the exact same record object
let copied = n2.val                    -- Independent value copied through a ref
n1.val = 99                            -- Mutate through 'n1'
assert(n2.val == 99 && copied == 10)

-- n2.val = 100                       -- Error [E0520]: ref grants no writes
-- let ref bad = n2.val              -- Error [E0402]: the member is a value
```

### Record Types and Row Polymorphism

- Record fields and tuple components use the [common binding and access mode axes](#binding-modes-and-storage-matrix). Omitted mode means default immutable access; an explicit `let` member modifier is not admitted.

Records have structural named fields. `.{}` is the closed empty record; closed records reject width subtyping. All record forms use the same `.{}` spelling: record types, record expressions, record patterns, record tests, mapped record types, record type patterns, and sum variant record payloads. A `TypeReference` may prefix a runtime record expression, pattern, or test (`User.{...}`) to select the declaration. Sum and effect declaration bodies keep their outer `{...}`. A final `..` permits extra fields in a structural constraint or direct record parameter of a Ril function/lambda definition. `..Fields` names or expands the remaining row; `Fields` is a user-chosen `PascalCase` name.

```ril
type User = .{ id: int, name: str }
let user = User.{ id: 1, name: "Ada" }
-- let missing: User = .{ id: 1 }     -- Error [E0307]: required field 'name' is absent
-- let unknown = user.age            -- Error [E0336]: this product has no field 'age'
-- type Repeated = .{ id: int, id: int } -- Error [E0210]: field label declared twice
type WithId<Fields> = .{ id: int, ..Fields }
-- type Overlap = WithId<.{ id: int }> -- Error [E0212]: row tail overlaps explicit 'id'
type Extended = WithId<.{ name: str }> -- OK: disjoint row labels
type Extra = .{ name: str }
type Combined = .{ id: int, ..Extra }  -- Same closed type as Extended; no generics
-- type BadTail = WithId<int>        -- Error [E0306]: a row tail must be a record type
```

```ril
fn get_id(item: .{ id: int, .. }) -> int { item.id } -- Implicit anonymous row parameter
fn sum_ids(a: .{ id: int, .. }, b: .{ id: int, .. }) -> int { a.id + b.id }
fn keep<T: .{ id: int, .. }>(item: T) -> T { item }  -- T preserves the entire record
fn keep_record<T: .{ .. }>(item: T) -> T { item }    -- Any record, including .{}
fn add_id<T: .{ ..Rest }>(item: T) -> .{ id: int, ..Rest } { .{ id: 1, ..item } }

assert(get_id(.{ id: 1, name: "Ada" }) == 1)
assert(sum_ids(.{ id: 1, name: "Ada" }, .{ id: 2, active: true }) == 3)
let kept = keep(.{ id: 1, name: "Ada" })
assert(kept.name == "Ada")
assert(add_id(.{ name: "Ada" }).name == "Ada") -- Constraint binds Rest for the result
let empty = keep_record(.{})
-- keep_record(1)                    -- Error [E0301]: int is not a record

-- fn unbound(item: .{ ..Missing }) -> () {} -- Error [E0204]: no binding for Missing
-- type Anything = .{ .. }            -- Error [E0306]: anonymous row outside an admitted position
-- let erased: .{ .. } = .{ id: 1 }   -- Error [E0306]: storage needs a determined type
-- fn erased() -> .{ .. } { .{} }     -- Error [E0306]: an anonymous result row has no binder
-- type Both<Fields> = .{ ..Fields, .. } -- Error [E0120]: at most one final row tail
```

Each anonymous input tail binds an independent implicit universally quantified row parameter, inferred at calls; it occupies no explicit generic-argument position. A structural constraint introduces an otherwise unbound tail name for its enclosing generic declaration; elsewhere named tails must already resolve (`E0204`). Reusing a bound name relates the same remaining fields and member modes. A tail must denote a record type; anonymous tails outside constraints, definition input records and type patterns are `E0306`. Checking preserves the complete actual schema, provenance and access obligations; anonymous tails introduce no erased open-record storage type.

Missing required construction fields use `E0307`. Unknown labels projected or matched against a known product schema use `E0336`. Repeated declared, explicit, or generated field labels use `E0210`; overlap between an explicit type field and a named row uses `E0212`. Projection on a type that does not admit that product projection uses `E0337`. Opacity restrictions take precedence when the representation is inaccessible.

Use `r.field` or a statically known `r.(key)`. Types use the corresponding `T.field`/`T.(key)`. Record bracket indexing and run-time keys are `E0324`.

Named tails preserve row relationships across inputs and results. Pattern destructuring with `..rest` extracts a concrete, statically typed sub-record containing the remaining known fields; bare `..` ignores them.

```ebnf
RecordType       ::= ".{" [ RecordFieldList ] "}"
MemberMode       ::= [ "var" ] [ "mut" | "^mut" | "ref" ]
DeclaredMemberMode ::= MemberMode | [ "var" ] "via"
RecordField      ::= { MetaAttr } [ DeclaredMemberMode ] FieldLabel ":" TypeExpression [ "=" Expression ]
TypeProjection   ::= PrimaryType "." ( FieldLabel | TupleIndex | "(" Expression ")" )
TupleIndex       ::= Digit { Digit }
RecordFieldList  ::= RecordTail | RecordField { "," RecordField } [ "," [ RecordTail ] ]
RecordTail       ::= ".." [ PascalCase ]
FieldLabel       ::= ValueName | PascalCase
```

Field default expressions (`= Expression`) are admitted only on immutable (`let` or `var`) fields of the root record in a `.ril` `TypeDecl`, `OpaqueTypeDecl`, or `NominalDecl` ([Record Construction and Spread Update](#record-construction-and-spread-update)); field `meta(...)` attributes are admitted only on root `NominalDecl` record fields ([Declaration Metadata Attributes](#declaration-metadata-attributes)).

```ril
type Cell = .{ var count: int }
type State = .{
    id: int,                         -- Implicit let: fixed, deeply immutable
    var title: str,                  -- Replaceable immutable value
    mut items: []int,                -- Fixed writable array holding immutable scalar elements
    ^mut shared_cell: Cell,          -- Fixed shared mutable handle
    var mut current: Cell,           -- Replaceable writable reference
    ref source: Cell,                -- Fixed live observation
    var ref cursor: Cell,            -- Replaceable live observation
}
let mut first = Cell.{ count: 0 }
let mut second = Cell.{ count: 0 }
first.count = 1; second.count = 2
let mut state = State.{
    id: 7, title: "draft", items: [1], current: Cell.{ count: 0 },
    shared_cell: ^mut first, source: first, cursor: first,
}
state.title = "ready"
state.items |> mut Array::push(2)
state.current.count += 1
state.current = Cell.{ count: 3 }
state.cursor = second
assert(state.source.count == 1 && state.cursor.count == 2)
-- state.id = 8                      -- Error [E0520]: default member is immutable
-- state.items = []                  -- Error [E0502]: mut pins the member's reference
-- let hidden = state               -- Error [E0535]: writable/live origins survive
```

```ril
type Counter = .{ var count: int }
let immutable = Counter.{ count: 0 }
let repeated = (mut immutable, mut immutable) -- OK: outer let suppresses member access modes
-- let mut bad = repeated.0                  -- Error [E0520]: no writer was created
-- type Bad = .{ ref count: int }           -- Error [E0402]: invalid even under outer let
```

| Member-specific rule | Requirement |
| :--- | :--- |
| Outer immutable reception | Apply [deep immutability](#deep-immutability) before reception; preserve the declaration schema |
| Invalid value-type mode | `E0402` under the [value-type exclusions](#value-types), even under outer immutability |
| Immutable/writable aliases | A live object cannot supply immutable reception (`E0535`) |

```ril
type User = .{ id: int, name: str }
let u: User = .{ id: 1, name: "Alice" } -- OK: exact closed record match

-- Closed record rejects unexpected fields (E0302):
-- let bad_u: User = .{ id: 1, name: "Alice", age: 30 } -- Error [E0302]: unexpected field 'age' in closed record 'User'

-- Field projection uses an identifier or a statically known computed key:
let user_id = u.id                     -- OK: static field projection
-- let bad_index = u["name"]           -- Error [E0324]: records do not support dynamic index lookup
let static_accessor = u.("name")       -- OK: a statically known key, not a dynamic lookup

-- Type-level field projection:
type IdType = User.id                  -- OK: direct static field type extraction (int)
-- type BadIndex = User["id"]          -- Error [E0324]: record types do not support bracket indexing, use User.id

-- Named row tail polymorphism (generic type preservation):
fn with_timestamp<Fields>(r: .{ ..Fields }) -> .{ timestamp: int, ..Fields } {
    .{ timestamp: 1600000000, ..r }
}
let stamped = with_timestamp(.{ id: 1, tag: "audit" })
assert(stamped.tag == "audit" && stamped.timestamp == 1600000000)

-- Type-precise rest destructuring:
type Account = .{ id: int, username: str, email: str, role: str }
let acc: Account = .{ id: 42, username: "admin", email: "adm@ril.org", role: "root" }

let .{ id, ..rest } = acc
-- 'rest' has static inferred type: .{ username: str, email: str, role: str }
assert(rest.username == "admin")
assert(rest.email == "adm@ril.org")
assert(rest.role == "root")
```

### Array, Map, and Tuple Types

Bracket syntax defines homogeneous arrays (`[]T`, `[mut]T`, `[^mut]T`, `[ref]T`) and maps (`[K: V]`, `[K: mut V]`, `[K: ^mut V]`, `[K: ref V]`). Range indexing (`arr[a..b]`) returns a newly allocated array with independent storage. Authority follows the [static mode rules](#binding-modes-and-storage-matrix). Map keys and set elements use deeply immutable reception and the [structural key rules](#relational-and-equality-operators), including eligible shared-object graphs; mutable key modifiers are rejected (`E0402`). `Set<T>` and collection type extractors are standard-library declarations.

Tuple arity is zero or at least two. The zero-element tuple `()` uses the unit type and literal syntax and has [copy-by-value semantics](#value-types). The tuple productions below cover the nonempty shared-object forms such as `(int, str)`. Parenthesizing one type or expression groups it. The spellings `(T,)` and `(e,)` for a one-element tuple are invalid. The same arities let [data constructors](#constructor-tuple-equivalence-invariant) omit the outer tuple grouping of positional payloads.

```ebnf
ArrayType             ::= "[" [ StorageModeExpression ] "]" TypeExpression
ElementAccessMode     ::= "mut" | "^mut" | "ref" | PascalCase
StorageModeExpression ::= ElementAccessMode | "via"
MapType               ::= "[" TypeExpression ":" [ StorageModeExpression ] TypeExpression "]"
TupleType      ::= "(" TupleMember "," TupleMember { "," TupleMember } [ "," ] ")"
TupleMember    ::= [ DeclaredMemberMode ] TypeExpression
TupleExpr      ::= "(" TupleValue "," TupleValue { "," TupleValue } [ "," ] ")"
TupleValue     ::= [ MemberMode ] Expression
ArrayExpr      ::= "[" [ Expression { "," Expression } [ "," ] ] "]"
MapExpr        ::= "[" ":" "]" | "[" MapEntry { "," MapEntry } [ "," ] "]"
MapEntry       ::= Expression ":" Expression
```

```ril
let mut pair: (var int, mut []int) = (0, [1])
pair.0 = 1
pair.1 |> mut Array::push(2)
-- pair.1 = []                       -- Error [E0502]: fixed mutable member
let frozen = clone(ref pair)
-- frozen.0 = 2                      -- Error [E0520]: outer let removes member writes
-- frozen.1 |> mut Array::push(3)    -- Error [E0520]: removal is recursive
assert(frozen.0 == 1 && frozen.1 == [1, 2])
```

Typed product constructors inherit declared member modes; untyped literals default omitted modes to `let`. Explicit literal modes must match the expected schema (`E0301`). Array and map elements follow their storage rules.

```ril
-- Array ([]T):
let numbers: []int = [1, 2, 3]
let empty: []int = []
-- let unconstrained = []             -- Error [E0344]: unconstrained empty array literal requires type annotation
-- let indexed = 42[0]                -- Error [E0352]: target has no element lookup

-- Associative Map ([K: V]):
let mut config: [str: str] = ["env": "prod", "host": "127.0.0.1"]
let empty_map: [str: int] = [:]        -- Empty map literal
let host: ?str = config?["host"]       -- Safe lookup evaluates to ?str (Some("127.0.0.1"))
config["host"] = "10.0.0.1"            -- In-place slot assignment
-- let bad_get = config["host"]        -- Error [E0352]: map lookups require 'm?[k]'
-- config["host"] += "!"               -- Error [E0352]: map compound assignment prohibited

-- Tuple ((T1, T2)):
let coords: (int, str) = (10, "Alice") -- Type: (int, str)
let x = coords.0                       -- Value positional access: 10
let name = coords.1                    -- Value positional access: "Alice"
type CoordX = (typeof coords).0        -- Inferred tuple positional projection: int
type First = (int, str).0              -- Static tuple positional projection: int
-- type OutOfBounds = (int, str).2      -- Error [E0312]: tuple index 2 out of bounds for (int, str)

-- Collections are not product types; dot projection on collections is rejected:
-- type BadArrElem = ([]int).elem      -- Error [E0337]: collection type '[]int' has no named fields or member projections; use 'ril/array::{Elem}'
-- type BadMapKey = ([str: int]).key   -- Error [E0337]: collection type '[str: int]' has no named fields or member projections; use 'ril/map::{Key}'
```

Empty array literals without contextual expected types require explicit annotation (`E0344`). `[via]T` preserves that requirement: an unresolved required element access mode is also `E0344`. A concrete `MemberMode` expression used for element access must have a fixed slot component; it cannot silently discard `var` (`E0356`). Invalid index types on an otherwise indexable receiver use `E0301`. An index outside an array's bounds panics at run time.

Map lookups must use safe bracket navigation (`m?[k]`), evaluating to `?V` (`Option<V>`). Plain bracket lookup expressions (`m[k]`) and compound assignments (`m[k] += v`) are prohibited (`E0352`). In-place slot assignment `m[k] = v` inserts or replaces an entry for `k` (requiring deeply immutable `k` under `E0535`).

#### Collection Extents and Index Types

| Position / operation | Rule |
| :--- | :--- |
| Collection length | `int`, from zero through $2^{63}-1$ per collection |
| Counted units | Array elements; map entries; set members; `str` scalars; `bytes` bytes |
| String UTF-8 extent | Byte count also fits `int` |
| Construction / growth / formatting / conversion | Storage is managed automatically; exceeding collection extent or memory exhaustion panics on allocation (`E0831` in static evaluation) |
| Existing map key / set member | Replacement / reinsertion preserves the count |
| Array element index / sequence slice endpoint | `int`; another typed numeric value is `E0301` |
| Array bounds failure | Ordinary lookup panics; safe lookup returns `None` |
| Map lookup | Declared key type K, including range-typed keys |
| Individual text / byte element | [`String::at` / `Bytes::at`](#text-and-byte-operations); single-element brackets are `E0352` |
| Standalone integer range | Finite bounds; cardinality may exceed `int` |

```ril
let items = [10, 20]
let position: u8 = 1u8
-- let wrong = items[position]         -- Error [E0301]: no implicit widening of an index
assert(items[Numeric::to_int(position)] == 20)
-- let scalar = "ab"[0]                -- Error [E0352]: use String::at
```

```ril
let full: [mut]u8 = [0u8]
assert(len(ref full) == 1)
-- Bounds violations panic at runtime:
-- let out_of_bounds = full[5]         -- Panics: index 5 is outside length 1
```

### Sum Types and GADTs

Sum types represent tagged disjoint unions. Constructor equations allow generalized algebraic data types (GADTs). A present variant payload is always parenthesized; a record payload is the single unnamed payload `(.{...})`. The sum declaration's own `{...}` delimits its variant list.

```ebnf
SumTypeDecl     ::= { MetaAttr } [ "pub" ] "type" PascalCase [ GenericParams ] [ WhereClause ]
                    "{" VariantDeclList "}"
VariantDeclList ::= VariantDecl { "," VariantDecl } [ "," ]
VariantDecl     ::= { MetaAttr } PascalCase [ GenericParams ] [ VariantPayload ] [ "->" TypeExpression ]
VariantPayload  ::= "(" [ VariantFields ] ")"
VariantFields   ::= VariantField { "," VariantField } [ "," ]
VariantField    ::= [ DeclaredMemberMode ] [ FieldLabel ":" ] TypeExpression
```

```ril
type Option<T> {
    Some(T),
    None,
}

type Expr<T> {
    LitInt(int) -> Expr<int>,
    LitBool(bool) -> Expr<bool>,
    Add(Expr<int>, Expr<int>) -> Expr<int>,
}

-- Specialized evaluator: constructor equations prune impossible branches:
fn eval_int(e: Expr<int>) -> int {
    match e {
        LitInt(n) -> n,
        Add(a, b) -> eval_int(a) + eval_int(b),
        -- LitBool(b) -> 0             -- Error [E0304]: unreachable match arm: constructor 'LitBool' binds T = bool, incompatible with Expr<int>
    }
}

-- Generic GADT evaluator: constructor equations refine return type T:
fn eval<T>(e: Expr<T>) -> T {
    match e {
        LitInt(n) -> n,                -- Refines T ~ int
        LitBool(b) -> b,               -- Refines T ~ bool
        Add(a, b) -> eval(a) + eval(b),-- Refines T ~ int
    }
}
```

```ril
type Box<T> { Item<U>(U) -> Box<U> }
let boxed: Box<int> = Box::Item(1)
type Payload = Box<int>.Item           -- int
-- type Packed { Item<U>(U) }          -- Error [E0354]: U is not determined by the result
-- type Wrong<T> { Item(T) -> bool }   -- Error [E0354]: result is not an instance of Wrong
```

| Variant rule | Requirement |
| :--- | :--- |
| Omitted result equation | The enclosing sum applied to its enclosing parameters |
| Explicit result equation | An instance of that same sum declaration (`E0354` otherwise) |
| Variant-local parameter | Recoverable from the result arguments; no hidden existential parameter (`E0354`) |
| Recovery | After transparent expansion, the parameter occurs as a bare argument or beneath rigid nominal, sum, or structural type constructors |
| Computed static argument / type-function inversion | Does not establish recovery of a parameter |
| Matching | Result equations supply arm-local equalities; recovered parameters do not introduce escaping existential types |

Substitution must satisfy every occurrence of a recovered parameter and its declared sort. These declaration checks do not perform inverse evaluation of arbitrary type functions.

#### Constructor-Tuple Equivalence Invariant

A positional data constructor can omit one layer of tuple parentheses in its payload declaration, direct call, or pattern. Tuple arities make the three forms unambiguous.

| Positional items | Payload schema | Equivalent forms |
| :--- | :--- | :--- |
| Zero | Unit `()` | `Ready()` and `Ready(())` declare the same unit payload. A direct `C()` supplies or matches `()` like `C(())` |
| One | The single payload | `C(x)` supplies or matches one value, including a whole tuple |
| Two or more | A tuple of the positional members | `Pair(A, B)` and `Pair((A, B))` declare the same tuple payload. `C(x, y)` and `C((x, y))` supply or match that same tuple |

Resolve the constructor before applying the shorthand. In a direct call, the supplied payload participates in ordinary type inference and reception, so `Some()` infers `Option<()>` just like `Some(())`. Either spelling preserves evaluation order, member modes, and provenance. A single unnamed payload forwards its checked modes and provenance directly. Expansion applies at the outermost constructor boundary. Nested tuples keep their grouping, and an unconstrained generic payload cannot be decomposed into positional members (`E0301`).

A variant declared without a payload clause, such as `None`, is a payload-free tag. `None()` is `E0353`. A bare payload-bearing constructor denotes a first-class callable with one payload parameter in its declared reception mode. For a unit payload the callable type is `fn(()) -> S`. Ordinary calls to callable values follow their declared parameter lists (`E0314`). A constructor with a nonempty tuple payload can adapt to a multi-parameter callable via context-directed $\eta$-expansion ($\backslash x_1, \dots, x_n \to C(x_1, \dots, x_n)$).

```ril
type Status { Ready(), Idle }                    -- Ready() declares the same payload as Ready(())
assert(Status::Ready() == Status::Ready(()))

let present = Some()                            -- Option<()>
assert(present == Some(()))
assert(present is Some() && present is Some(()))
let absent: Option<()> = None
assert(present != absent)
-- let bad_none = None()                         -- Error [E0353]: None is a payload-free tag

let unit_res: Result<(), str> = Ok()
let explicit_unit: Result<(), str> = Ok(())
assert(unit_res == explicit_unit)
let make_some: fn(()) -> Option<()> = Some
assert(make_some(()) == present)
-- make_some()                                  -- Error [E0314]: callable value expects one argument

match unit_res {
    Ok() -> println("success"),                  -- OK: n = 0 matches () unit payload
    Err(e) -> println(e),
}

-- Result construction and matching with tuple payload:
let res: Result<(int, str), str> = Ok(200, "OK") -- OK: n = 2 constructs (int, str) directly
let pair = (200, "OK")
let res_from_pair: Result<(int, str), str> = Ok(pair) -- OK: n = 1 passes existing tuple
let res_compat: Result<(int, str), str> = Ok((200, "OK")) -- OK: explicit tuple literal
assert(res_from_pair is Ok(_))
assert(res_compat is Ok(_))

match res {
    Ok(code, msg) -> println(msg),               -- OK: n = 2 directly unpacks tuple elements
    -- Ok(p) -> println(p.1),                    -- Error [E0304]: preceding Ok arm already covers it
    Err(e) -> println(e),
}

-- Multi-field variant declaration and tuple equivalence:
type Geometry {
    TwoPoints(int, int),                         -- Equivalent to TwoPoints((int, int))
}

let p1 = TwoPoints(10, 20)                       -- OK: positional elements
let p2 = TwoPoints((10, 20))                         -- OK: explicit tuple payload
let TwoPoints(x, y) = p1                         -- OK: positional destructuring
let TwoPoints(raw_tuple) = p1                    -- OK: whole-tuple destructuring

-- Functions keep their declared parameter lists; no implicit tuple expansion:
fn add(a: int, b: int) -> int { a + b }
let sum1 = add(1, 2)                             -- OK: 2 arguments
-- let sum2 = add(pair)                          -- Error [E0314]: expected 2 arguments, found 1 tuple

-- Nested tuples: non-transitive boundary:
type Node {
    Branch((int, int), str),                     -- Payload is 2-tuple: ((int, int), str)
}
let node = Branch((1, 2), "left")                -- OK: n = 2 arguments
-- let bad_node = Branch(1, 2, "left")           -- Error [E0314]: arity mismatch: expected 2 arguments, found 3
```

### Nominal Type Wrappers

A nominal wrapper introduces a distinct type identity while retaining the underlying type's run-time representation. Wrapping or unwrapping introduces no additional shared-object root and preserves the underlying object identity.

```ebnf
NominalDecl      ::= { MetaAttr } [ "pub" ] "type" PascalCase [ GenericParams ] [ "(" [ TypeList ] ")" ] [ WhereClause ]
```

With no parenthesized payload clause, `NominalDecl` defines a **Unit Nominal Type** (e.g. `type Marker`).
- **Value Construction**: The bare identifier `Marker` denotes its canonical singleton value (`let m = Marker`).
- **Pattern Matching**: `Marker` acts as a nullary constructor pattern in `match` expressions (`match event { Marker -> ... }`). In `let` statements, patterns introducing zero variable bindings (such as `let Marker = m`) are prohibited under the **Non-Vacuous Binding Invariant (`E0309: VacuousBindingError`)**.
- **Prelude Unwrapping**: Unwrapping via `inner(Marker)` evaluates to `()`.
- **Nominal Type Identity**: A unit nominal type is distinct from structural `()`. For example, `Result<Marker, E>` requires `Ok(Marker)` and does not permit `Ok()`. This type distinction provides no graph-isolation guarantee.

```ril
-- Unit Nominal Types (domain markers):
type Marker
type AdminToken

let m: Marker = Marker                 -- OK: bare identifier value construction
let raw_unit: () = inner(m)            -- OK: unwrap unit nominal wrapper evaluates to ()
let _ = m                              -- OK: explicit wildcard discard
-- let Marker = m                      -- Error [E0309]: 'let' pattern must bind at least one variable; nullary constructor 'Marker' introduces zero bindings

-- Value-Wrapped Nominal Types:
type UserId(int)
type AccountId(int)
type Coord(int, int)                   -- Equivalent to Coord((int, int))
type Point2D(.{ x: f64, y: f64 })       -- Nominal wrapper over structural record

let uid = UserId(1001)
let aid = AccountId(1001)
let c = Coord(10, 20)                  -- OK: positional tuple expansion (n = 2)
let c_compat = Coord((10, 20))         -- OK: explicit tuple literal (n = 1)
let pt = Point2D(.{ x: 10.0, y: 20.0 })

-- uid == aid                          -- Error [E0305]: mismatched nominal types 'UserId' and 'AccountId'
let raw_id: int = inner(uid)           -- OK: unwrap nominal wrapper via prelude 'inner()' (1001)
let raw_coord: (int, int) = inner(c)   -- OK: unwrap nominal wrapper to underlying tuple (10, 20)
let raw_pt: .{ x: f64, y: f64 } = inner(pt) -- OK: unwrap underlying record via 'inner()'
let UserId(unwrapped_id) = uid         -- OK: pattern-matching unwrap
let Point2D(.{ x, y }) = pt            -- OK: structural record pattern unwrap
let Coord(cx, cy) = c                  -- OK: positional tuple pattern unwrap
let Coord(pair) = c                    -- OK: whole-tuple pattern unwrap
let make_user_id: fn(int) -> UserId = UserId -- OK: constructor function value
```

### Deep Immutability

```ril
type Cell = .{ var count: int }
let mut source = Cell.{ count: 1 }
let snapshot = clone(ref source)
let mut copy = clone(ref source)
copy.count = 2
source.count = 3
assert(snapshot.count == 1 && copy.count == 2 && source.count == 3)
```

Default immutable reception follows the [common mode tables](#binding-modes-and-storage-matrix), including ordinary parameters and default members. Graph-specific rules are:

| Operation / condition | Required behavior |
| :--- | :--- |
| Immutable reception | Recursively suppress effective `var`, `mut`, `^mut`, and `ref` modes, idempotently through cycles; preserve schemas, nominal/opaque identities, and callable contracts |
| Surviving writer or live origin | Reject with `E0535`; reception cannot copy, freeze, consume, or revoke that authority |
| `clone` | Copy data admitted by [`SharedObject`](#normative-rules-for-built-in-operations) into an isolated construction result `new T`. Preserve the schema and nominal or opaque identity. Immutable reception publishes the copied contents as a snapshot, including cyclic contents |
| Copy execution | Read the source once as a stable snapshot; no suspension, user callback, or overlapping write |
| Non-clonable authority | Reject with `E0530` at the root or in a constituent, including retained environments, scoped resources, tasks, and channel endpoints hidden in wrappers or `ref` handles |
| Value types | Copy by ordinary value passage. `clone(value)` fails the type guard (`E0301`). A value-type `ref` argument is `E0401` |
| Function / resource value | Immutable environment-free functions support ordinary copying. Sender duplication (`Channel::clone_sender`) follows the [channel resource contract](#structured-concurrency-channels) |

Writable reception of a clone activates declared writable members. Each writable occurrence of an immutable constituent gets separate storage. This materialization must be finite (`E0530`). Copied live objects retain their internal alias and cycle relationships under the ordinary writable reception checks. A `new` return preserves the construction and reception facts.

```ril
type Cell = .{ var count: int }
fn read(cell: Cell) -> int { cell.count }
fn read_live(ref cell: Cell) -> int { cell.count }
fn snapshot(ref cell: Cell) -> Cell {
    let copied = clone(ref cell)
    copied
}
let original = Cell.{ count: 1 }
assert(read(original) == 1)
-- let mut upgraded = original       -- Error [E0520]: an existing immutable graph stays immutable
let mut live = Cell.{ count: 1 }
live.count += 1
assert(read_live(ref live) == 2)
-- read(live)                        -- Error [E0535]: ordinary parameters require immutable data
-- let invalid = live                -- Error [E0535]: let cannot freeze a surviving writer
let copied = snapshot(ref live)
assert(read(copied) == 2)
```

Ascription grants no authority and cannot turn resources into ordinary data. Root construction and whole-graph publication are separate checks under the [return rules](#return-construction-access-modes-and-sources).

### Type Identity and Subtyping

```ril
type Animal = .{ name: str }
type Dog = .{ name: str, breed: str }
type Getter<T> = fn() -> T
fn make_dog() -> Dog { .{ name: "Fido", breed: "Collie" } }
let get_dog: Getter<Dog> = make_dog       -- OK
-- let get_animal: Getter<Animal> = make_dog -- Error [E0301]: closed records reject width subtyping
```

| Type position | Subtyping |
| :--- | :--- |
| Closed record | No width subtyping; extra fields require an open row |
| Record member | Writable/`ref` schemas retain matching modes; immutable reception compares mode-suppressed data shapes. Writable/replaceable data is invariant; immutable data covariant |
| Callable with identical concrete parameter modes | Parameters contravariant; result shape covariant; independently check result guarantees and exact closed rows. Explicit `via` mode patterns retain their actual verified family; effect/state openness alone does not change modes |
| `&^mut` clause | Includes its prescribed write/retention implications during normalization; a closed `&^mut` row does not match an actual `&mut`-only row, and openness never changes parameter or handle modes |
| Array / map | Element and key/value types invariant |
| Tuple | Components invariant; immutable reception suppresses modes, otherwise modes match; only `var` members permit slot replacement |
| Sum / nominal arguments | Invariant; transparent aliases retain the expanded type's identity |

Member modes participate in structural schemas. Outer immutable reception suppresses mutable/observation modes without changing those declaration identities or introducing container subtyping.



### Complete Provenance and Required Annotations

The compiler infers and verifies complete authority, provenance, effects, and callable contracts. Annotations constrain these judgments; they cannot grant authority or hide obligations. Required named annotations and reception markers remain explicit.

```ril
fn identity<T>(ref value: T) -> ref(value) T { value }
type Cell = .{ var count: int }
let mut source = Cell.{ count: 0 }
let ref packet = .{ ref item: identity(ref source) }
let ref observed = identity(ref packet.item)
source.count += 1
assert(observed.count == 1)
-- let hidden = identity(ref packet.item) -- Error [E0535]: source still has a surviving writer
-- let mut stolen = identity(ref observed) -- Error [E0528]: a ref return cannot grant writes
```

- **Complete Static Provenance**: Track possible origins, access modes, immutable/live facts, aliases, retention/escape dependencies, and scope/task ownership for all storage, references, environments, and resources. Conservative judgments may overapproximate execution; obligations cannot be erased.
- **Propagation**: Preserve these facts through aggregates, projections, branches, recursion, returns, calls, opaque boundaries, handlers, cleanup, and modules. Every handle, member mode, and stored constituent limits the resulting authority. A default member imposes deep immutability; `mut` permits interior writes without slot replacement. Independent value copies carry no shared-object authority; capturing a mutable binding retains its origin.
- **Contract Metadata**: Every function retains its complete inferred contract across source annotation omissions and callable-type abbreviations. Named source completion follows the `via`/`infer` exemptions under [access mode inference](#access-mode-inference-with-via-and-infer); anonymous source annotations are optional. Private dependencies and alias relations are checked metadata. Plain `-> T` establishes immutability; `-> infer T` requests inferred result authority.
- **Conservative Alternatives**: Retain the union of possible origins, accesses, retention, and escape obligations, and only access modes common to all alternatives. Preserve input/output and output-component relations established in every retained alternative. Prune only branches excluded by the specified static computations and typing rules. Treat unknown overlap as possible overlap; mutable access, immutable publication, task crossing, uniqueness, and non-escape require established proofs.
- **Recursive Dependencies**: Loop and recursive call dependencies retain possible origins and unresolved relationships, including inferred Diverge and finite-budget coverage. Freshness, disjointness, non-escape, absence of Diverge, empty callable rows, and [authority use](#reachable-authority-use) require facts grounded in actual operations or verified contracts. A cycle cannot justify its own guarantees. Unresolved dependencies remain obligations at every affected use; an absent proof uses that operation's diagnostic.
- **Authority and Discharge**: Prove each access mode and authority use from a declaration, a traced source, a fresh-data rule, or an explicit resource rule. Local discharge requires confinement of all relevant authority roots and environments. Calculate minimal concrete state and provenance annotations (`E0529`) under these conservative rules.
- **Source Annotations**: Infer and check modes, argument/reception markers, result construction/sources, effects, captures, and state/provenance clauses. Named definitions complete concrete required annotations; `via` retains mode-dependent clauses and `infer` retains result details in metadata. Anonymous functions may omit source annotations. Written/contextual constraints are checked, and ordinary markers retain their authority semantics. Lexical templates elaborate only their verified dependent transfers; inference supplies no absent authority, hidden copy, changed evaluation order, allocation identity, or resource ownership.
- **Diagnostic Provenance**: Semantic diagnostics must make derived access, sharing, escape, and effect obligations and their source explanations available, including facts omitted from source. Identify the relevant origin or declaration, propagation steps, use or boundary, and accepting or rejecting rule. Report possible origins and unproved disjointness explicitly. Explanations are also available for accepted programs and inferred obligations; presentation is optional and validity is independent of it.

For `hidden`, connect `source`'s writer through the `ref` argument, `ref` member, return, and prohibited immutable reception. For `stolen`, identify the return's `ref` mode.

```ril
type Cell = .{ var count: int }
fn copy_cell(value: Cell) -> new Cell { clone(value) }
fn swap(mut a: Cell, mut b: Cell) &mut -> () {
    let saved = a.count
    a.count = b.count
    b.count = saved
}
let base = Cell.{ count: 0 }
let mut first = copy_cell(base)
let mut second = copy_cell(base)
swap(mut first, mut second)           -- OK: separate evaluations produce separate writable copies
let ^mut alias = first
alias.count += 1
-- swap(mut first, mut alias)         -- Error [E0523]: different names for the same writable object
```

- **Local Construction**: A fresh ordinary result may enter `let` when its construction scope or call ends and no relevant outside writer, live dependency, or active environment survives. `new` records construction/handoff and root write authority; complete provenance retains actual allocation history and separately decides publication and initial-reception eligibility. Parameter/external aliases retain their restrictions (`E0528`). Ordinary writable bindings retain their authority until lexical scope ends; last textual use does not revoke it. Reassigning `var mut` replaces its path without revoking other paths.

- **Fresh Evaluation**: Each successful ordinary shared-object allocation establishes a distinct new object identity. A newly constructed aggregate may contain references to pre-existing objects; graph disjointness is a separate judgment. `clone` isolates its writable regions. Freshness across function calls follows the function's verified return relation.

- **Initial Writable Reception**: [Fresh storage inputs](#homogeneous-storage-authority) and [qualified fixed writable locals](#construction-qualified-locals-and-mode-preserving-reception) may receive unpublished construction authority. Ordinary immutable reception ends that path's eligibility; read-only/borrowed parameters acquire none. Temporary observations retain their source's alias restrictions. Allocation identity or last use cannot restore ended qualification.

```ril
-- Cell and swap have the preceding declarations; choose_order is a run-time bool input.
fn permute(flag: bool, ^mut a: Cell, ^mut b: Cell) &^mut &return{^mut a, ^mut b}
    -> new (mut Cell, mut Cell) {
    if flag { (^mut a, ^mut b) } else { (^mut b, ^mut a) }
}
let mut left = Cell.{ count: 1 }
let mut right = Cell.{ count: 2 }
let ^mut pair = permute(choose_order, ^mut left, ^mut right)
swap(mut pair.0, mut pair.1)           -- OK: either ordering preserves the inputs' proven disjointness

let mut cells: [mut]Cell = [Cell.{ count: 0 }, Cell.{ count: 1 }]
cells[0].count += 1
-- i and j are unconstrained run-time integer inputs:
-- swap(mut cells[i], mut cells[j])   -- Error [E0523]: the indices may select the same writable origin
```

The two components returned by `permute` may each originate in either argument, but are disjoint whenever the two actual inputs are disjoint. That common relation survives the branch and return. Distinct parameter names alone establish no such relation. Unrelated run-time selections retain possible overlap unless an applicable rule proves otherwise.

```ril
type Cell = .{ var count: int }
let mut source = Cell.{ count: 0 }
source.count += 1
-- let frozen = source               -- Error [E0535]: source's scope has not ended, even without later use
let finished = {
    let mut builder = Cell.{ count: 0 }
    builder.count += 1
    builder
}
assert(finished.count == 1)           -- OK: construction scope ended without an outside writer
-- let hidden = { let ^mut alias = source; alias.count += 1; alias }
-- Error [E0535]: ending the alias's scope does not end source's authority
```

Escaped environments and stored writable paths survive their creating scope and still prevent immutable publication. Last-use rules for temporary mutable access or `ref` handles do not implicitly consume an ordinary writable binding. Resource consumption follows only its specified rules.

### Access Mode Inference with via and infer

```ril
fn append<T>(mut xs: [via]T, via value: T) &mut -> () {
    xs |> mut Array::push(value)
}
fn preserve<T>(via value: T) -> infer T { value }

type Packet<T> = .{ via item: T }
fn packet<T>(via value: T) -> infer Packet<T> {
    Packet.{ item: value }
}
fn relay<T>(via value: T) -> infer Packet<T> {
    let via intermediate = preserve(value)
    packet(intermediate)
}
```

`via` binds static access-mode parameters, orthogonal to written type generics. Each declaration-owned input/schema occurrence binds independently; checked value flow relates them. A definition denotes a finite mode template specialized at compile time. `infer` derives result access modes and provenance from the checked computation.

| Position | Role |
| :--- | :--- |
| Input `via x: T` / `[via]T` / `[K: via V]` | Bind this function's access-mode parameters |
| Declared `via item: T` / `var via item: T` | Bind the type template's access-mode parameters; never infer `var` |
| `let via x = expression` | Receive access modes and provenance dependent on bound modes or input callable mode patterns |
| `-> infer T` | Infer result access modes, sources, and dependencies for a signature with explicit `via` inputs |
| `fn(via T) -> R` | Open that callable's mode pattern, not an unrelated enclosing function |
| Input callable `fn(via T) -> infer R` / `via cb: fn(...) -> infer R` | Retain its actual result relations as finite input-bound dependencies |

Template checking may substitute a lexically bound outer `P` for an inner parameter `Q`. Before a closed invocation executes, its selected signature, local receptions, result, and member schemas must be concrete. A closure specializes with its enclosing instance; an explicitly quantified finite callable family may retain its bound parameters. Unresolved mode instances in concrete objects, storage, or single-instance entries are `E0344`.

Data types, slot replacement, source authority, and effect-row openness follow their own declarations and checks. `via` ranges over concrete access modes. `E0412` rejects it in static/meta/type-function parameters, effect-operation signatures, handler parameters, bodyless foreign interfaces, map keys, untyped literal modifiers, reassignable/scoped/module receivers, or local reception without an applicable lexical template. Mapped comprehensions preserve known modes. Bodyless boundaries supply explicit trusted contracts.

`-> infer T` requires an ordinary Ril function definition or callable type with at least one explicit `via` in its parameter list, or a parameter callable type whose own parameter binding is directly modified by `via` (`via cb: fn(...) -> infer T`) (`E0412`). In a parameter list, `via` may modify a parameter directly, declare a member, array element, or map value mode in its type, or appear in an input callable's own parameter list. Check other callable signatures independently: a `via` found only through a referenced type declaration, on an unrelated parameter of an enclosing signature, in a result, or in a body cannot qualify the signature. This restriction governs the written modifier. Mandatory contract inference and anonymous annotation omission follow their usual rules.

```ril
type Cell = .{ var count: int }
fn make_cell() -> new Cell { Cell.{ count: 0 } }
fn run_thunk<T>(via cb: fn() @& -> infer T) -> infer T { cb() } -- OK: parameter cb is modified by via
let via = 1                                      -- OK: ordinary identifier
let infer = 2                                    -- OK: ordinary identifier
assert(via + infer == 3)

-- fn bad_factory() -> infer Cell { Cell.{ count: 0 } } -- Error [E0412]: no via input
-- type BadThunk = fn() -> infer Cell                   -- Error [E0412]: standalone callable has no via input
-- type BadReader = fn(ref Cell) -> infer Cell          -- Error [E0412]: no via input
-- fn bad_outer(via x: Cell, cb: fn() -> infer Cell) -> int { x.count } -- Error [E0412]: enclosing via on x does not qualify cb
-- fn bad_result(ref value: Cell) -> via Cell { value } -- Error [E0412]: via is an input/member/receiver modifier
-- fn bad_input(infer value: Cell) -> int { value.count } -- Error [E0412]: infer is a result modifier
-- type BadMember = .{ infer value: Cell }         -- Error [E0412]
-- let infer received = make_cell()               -- Error [E0412]
```

#### Member Modes and Implicit Schema Parameters

```ril
type Fixed<T> = .{ via item: T }       -- Fixed slot; infer access
type Slot<T> = .{ var via item: T }    -- Replaceable slot; infer access
type Items<T> = [via]T
type Node<T> { End, Link(.{ via value: T, ref following: Node<T> }) }
type Alias<T> = Fixed<T>

type Fields = .{ var tag: int, mut items: []int }
meta let FIELD_COORDS = coords(<Fields>)   -- [(MemberMode::Var, "tag"), (MemberMode::Mut, "items")]
```

`MemberMode` pairs slot replacement (replaceable `var` or a fixed slot) with access (default, `ref`, `mut`, `^mut`). Introspection via `coords(<T>)` yields both components alongside member coordinate keys. Access modes have distinct source and retention rules; slot replacement is explicit.

```ril
type Cell = .{ var count: int }
type Holder = .{ mut item: Cell }
let mut source = Cell.{ count: 0 }
let mut holder = Holder.{ item: ^mut source }
holder.item.count += 1                         -- OK: acknowledged shared constituent

let mut owned: [mut]Cell = []
owned |> mut Array::push(new Cell.{ count: 0 }) -- OK: construction input
-- owned |> mut Array::push(^mut source)        -- Error [E0406]: this boundary requires new
```

Reception checks the boundary, slot/access schema, input mode, full provenance, and lifetime. Isolation requires a separate proof; arrays follow their stricter storage rules. A fixed contextual schema determines reception. For a newly constructed `via` member without one, use the following classification:

| Verified input | Inferred access |
| :--- | :--- |
| Immutable / copied value | Default |
| Observation | `ref` |
| Eligible construction / storage handoff | `mut` |
| Acknowledged retained writer | `^mut` |

Temporary `mut` cannot become persistent writable storage. `via` cannot invent observation/sharing for ordinary writable inputs; unresolved or non-unique required instances are `E0344`, without a run-time union.

| Implicit schema rule | Requirement |
| :--- | :--- |
| Binding | Each declaration-owned member/element/value `via` binds access by declaration identity and coordinate path; function-owned occurrences belong to that function |
| Instantiation | Freshen the finite whole signature at independent outside uses; one concrete instance has a fixed schema |
| Initial reception | Context and checked value flow may constrain admitted mode instances; justify authority from the actual source under concrete reception rules, never from the receiver's requested mode |
| Later replacement | Check the incoming value against the destination's instantiated declared schema; assignment does not freshen or re-infer that concrete storage instance's mode parameters. `var via` members permit slot replacement, not mode replacement |
| Recursion | Forward the current signature through self references; mutually recursive declarations use finite group equations, with no fresh binders on cycles |
| Other declarations | Add only finite syntactic-site parameters; transparent aliases forward identity/signature, nominal/opaque types retain identity and checking facts |
| Checking | Preserve schema identity, invariance, dependencies, and homogeneous elements; symbolic reflection is allowed, required concrete resolution is `E0344` |
| Operand elaboration | Only verified lexical mode/callback dependencies permit implicit markers; each selected concrete operation must satisfy source, alias, sharing, lifetime, retention, exclusivity, and consumption checks |
| Alternatives | Retain every possible origin and obligation and only common guarantees, preserving verified correlations under [provenance propagation](#complete-provenance-and-required-annotations). Construction paths remain affine under the [handoff rules](#fresh-construction-parameters) |

Concrete template instances must satisfy constraints from initialization and later assignments; those constraints need not admit every mode. Fixed declared schemas still permit the specified reductions of effective access through observation and immutable reception.

```ril
type Cell = .{ var count: int }
type Slot<T> = .{ var via item: T }

let mut source = Cell.{ count: 0 }
let mut other = Cell.{ count: 10 }
let mut slot = Slot.{ item: ref source }     -- OK: this instance has a ref member
slot.item = ref other                      -- OK: replace the observed object, keeping ref
source.count += 1
other.count += 1
assert(slot.item.count == 11)

-- slot.item.count += 1                    -- Error [E0520]: the ref member grants no writes
-- slot.item = ^mut source                 -- Error [E0527]: read-only reception does not use shared-write acknowledgment
-- slot.item = clone(ref source)           -- Error [E0543]: an independent copy has no established observation origin

let frozen = Cell.{ count: 1 }
let mut snapshot = Slot.{ item: frozen }    -- OK: an independent instance with a default member
snapshot.item = Cell.{ count: 2 }           -- OK: replace the immutable member value
assert(snapshot.item.count == 2)
-- snapshot.item = source                  -- Error [E0535]: the fixed immutable member cannot receive a surviving writer
```

Implicit member parameters supplied by a function's input types may be bound schema parameters in its lexical checking environment, even without an explicit `via` parameter modifier. Dependent projections may use template elaboration under that schema and the parent's effective access. This does not parameterize a fixed `ref`/`mut` root or grant an unrelated concrete operand a missing marker. A nested callable's own binders remain scoped to it; a verified selected call may nevertheless expose a finite result dependency bound to that input callable.

#### Inference Domains and Contract Completion

```ril
type Cell = .{ var count: int }
fn bump(mut x: Cell) &mut -> () { x.count += 1 }

-- fn redundant(via x: Cell) &mut -> () { bump(x) }
-- Error [E0550]: exact forwarding fixes the parameter to mut

-- type Redundant = .{ via count: int }
-- Error [E0550]: a value member has only ordinary immutable access

-- fn redundant_array(mut xs: [via]int, n: int) &mut -> () {
--     xs |> mut Array::push(n)
-- } -- Error [E0550]: the declaration-owned element mode is fixed too
```

Infer the admitted finite domain from the body, schemas, verified dependencies, and explicit semantic constraints; then normalize the whole family; finally validate named annotations. Missing annotations never prune alternatives. A proper inferred subdomain is allowed, but explicitly promised instances cannot be removed. Check every admitted alternative's type, authority use, provenance, escape, exclusivity, resources, full effects including Diverge, and budget obligations; unknown facts remain obligations.

`E0550` rejects a declaration-owned `via` parameter/schema whose mode is invariant over all admitted type/static arguments and dependencies, including nested array/map occurrences. A template-local `let via` requires access modes or provenance dependent on lexically bound mode parameters or selected-call relations from an input callable's open mode pattern, including contained schemas and consumption/source relations. Check this dependency at template level. Open callable patterns and `-> infer` are exempt from this redundancy check. Invalid/empty families use their underlying diagnostic; `E0527` checks each mutable/shared alternative's actual use.

```ril
fn store(mut xs: [^mut]Cell, ^mut value: Cell) &^mut -> () {
    xs |> mut Array::push(^mut value)
}
-- The same body with only &mut: Error [E0510]
-- Replacing value's fixed mode with via also gives E0550, not a state-annotation exemption.
```

Named definitions spell concrete effects other than the automatically retained [Diverge label](#termination-and-halt-contracts), state/provenance clauses, and known external/captured source groups, including known effect instances parameterized by ordinary type arguments. Only genuine mode/callback dependencies remain symbolic; selecting an instance makes its concrete obligations the caller's responsibility after lawful handling/discharge. A variable solved to a constant supplies no exemption. Explicit `&{}` closes the full total.

For signatures with explicit `via` inputs, `-> infer T` infers result access modes, sources, and dependencies while requiring the result data type. Preserve complete metadata and check written constraints and every root/contained guarantee. Results requiring a fresh/live root combination use an explicit aggregate or variant under the [return rules](#return-construction-access-modes-and-sources).

#### Preserving Reception and Forwarding

```ril
type Cell = .{ var count: int }
fn preserve<T>(via x: T) -> infer T { x }

let mut source = Cell.{ count: 0 }
let ref seen = preserve(ref source)
-- let via seen = preserve(ref source)     -- Error [E0412]: no lexical mode template
let ^mut writer = preserve(^mut source)
writer.count += 1
assert(seen.count == 1)

let mut fresh = preserve(new Cell.{ count: 2 })
let mut moved = preserve(new fresh)          -- Explicit concrete handoff
moved.count += 1
-- let count = fresh.count                  -- Error [E0549]

let mut views: [ref]Cell = []
append(mut views, ref source)               -- Preceding append declaration
-- append(mut views, source)                -- Error [E0405]: no caller marker is inferred
```

Within a lexical mode template, `via` formals and dependent local, member, payload, and capture modes support automatic operand elaboration through their bound mode parameters and input callable mode patterns. Each instance uses ordinary concrete operations. Projections and captures are bounded by every parent, current effective modes, and true source, preserving affine construction paths.

| Inferred operand mode | Argument | Root return | Persistent reception |
| :--- | :--- | :--- | :--- |
| Immutable/value | Ordinary | Ordinary | Immutable/copy rules |
| Observation | `ref` | Bare value + `ref(sources)` | Preserve eligible origins |
| Temporary writer | `mut` | No retained writable root | Cannot prolong authority |
| Retained writer | `^mut` | Bare value + `^mut(sources)` | Sharing acknowledgment and extra-retention obligations |
| Construction path | `new` handoff | Checked construction return | Qualified local/storage reception |

```ril
fn bump(mut x: Cell) &mut -> () { x.count += 1 }
fn clear_and_bump(mut xs: [via]Cell, mut x: Cell) &mut -> () {
    xs |> mut Array::truncate(0)
    -- let via count = x.count            -- Error [E0550]: fixed scalar mode
    -- bump(x)                             -- Error [E0405]: concrete x is not via-dependent
    bump(mut x)
}
```

Concrete callers, independent locals, and closed results use explicit argument markers. Elaborate only operands dependent on bound mode/schema parameters or input callable patterns. Exact template forwarding preserves the mode; explicit `ref x` / `mut x` may request permitted temporary access. Root returns use their return annotation without a duplicate sharing expression.

Every transfer evaluates once and ends its old construction path during operand preparation, before later operands/defaults/cleanup, including on failure (`E0549`). Metadata preserves sharing, origins, consumption, and graph preconditions; operand elaboration is lexical.

#### Lexical Mode Templates and Closures

```ril
type Pair<T> = .{ via first: T, via second: T }
fn make<T>(via x: T) &capture
    -> infer (fn(via T) @& -> infer Pair<T>) {
    \via y: T -> Pair.{ first: x, second: y }
}
let build = make(3)
let pair = build(4)
assert(pair.first == 3 && pair.second == 4)
```

A closure may reference the enclosing template's bound type/mode parameters and input-callable dependencies. Capture schemas, call operands, and result modes and provenance specialize with the outer instance to a concrete escaping environment. Nested callables retain lexical relationships; separately supplied callbacks use their own checking environments.

Check the actual capture operation and each environment use against the effective captured modes and origins, including environment-handle, capture/retention, provenance, lifetime, exclusivity, and budget requirements. Non-consuming observation/shared instances permit repeated invocation when these checks succeed.

Construction state is affine. A call-local capture may use an active path under its activation/lifetime and alias proofs. An escaping capture ends or lawfully consumes the originating construction qualification. A construction-consuming instance requires a verified invocation or slot-extraction summary supporting that handoff; other valid instances remain admissible.

#### Inferred Interfaces and Callable Families

```ril
fn apply<T, R>(via value: T, action: fn(via T) @& -> infer R) -> infer R {
    action(value)
}

fn through<T, R>(ref x: T, action: fn(via T) @& -> infer R) -> infer Packet<R> {
    let via intermediate = action(ref x)   -- Bound to this selected callback result
    packet(intermediate)
}
```

`via` in a callable type opens only the mode-pattern dimension; `@&` opens only effects and state/provenance rows. Preserve the supplied callable's actual domain, acceptance/use conditions, result relations, and obligations; a concrete callback may satisfy a selected instance without becoming an all-mode family. Without `via`, concrete modes match exactly (`E0407`). Handle and data-parameter modes remain distinct.

A selected call's result may depend on the input callable's declared open mode pattern. Instantiate its quantifiers, substitute actual argument/source relations, and project the verified result modes and provenance. Preserve origins, invocation-specific construction state/allocation history, affine consumption, and root/graph/lifetime preconditions. This finite input-bound relation supports dependent reception/forwarding in the enclosing lexical template; the input callable's internal binders stay scoped to it. Operand elaboration follows the [lexical forwarding rules](#preserving-reception-and-forwarding).

Dynamic targets permit calls valid for every target, with common guarantees and the union of obligations. Origins and domains require established proofs. Determine ordinary type arguments before run-time family emission. Finite checked entries may share a lawful environment, with compile-time mode selection and ordinary dispatch costs; equivalent/static entries may be shared or specialized.

```ril
-- Published compatibility baseline:
type Cell = .{ var count: int }
fn read(via x: Cell) -> int { x.count }

-- Replacement checked against that baseline:
-- fn read(via x: Cell) &mut -> int { x.count += 1; x.count }
-- Error [E0552]: the same via spelling no longer preserves the accepted read inputs
```

Every emitted interface must retain normalized domains, schemas, result/payload correlations, origins/history, store/return relations, consumption, graph preconditions, callback/environment dependencies, complete effect rows including Diverge, and budget-coverage conditions. Hidden opaque names retain their checking facts in metadata. Tools expose concise summaries and full expansions.

Compatibility is checked against the normalized declared/emitted interface baseline. `E0552` rejects narrower inputs, stronger requirements, weaker results, or incompatible schemas. An explicitly new interface version may establish a new baseline; otherwise invalidate and recheck dependents. Local/private changes recheck ordinary dependents.

### Functional Updates via Derive

`derive` supports local updates of deeply immutable data. Reusing unchanged contents can avoid work required by a complete independent copy.

```ril
type Cell = .{ var count: int }
type Pair = .{ left: Cell, right: Cell }
let cell = Cell.{ count: 1 }
let base = Pair.{ left: cell, right: cell }
let updated = base |> derive \mut draft -> {
    draft.left.count += 1
}
assert(base.left.count == 1 && base.right.count == 1)
assert(updated.left.count == 2 && updated.right.count == 1)

let external = Cell.{ count: 10 }
let inserted = base |> derive \mut draft -> {
    draft.left = external
    draft.left.count += 1
}
assert(external.count == 10 && inserted.left.count == 11)
```

#### Normative Rules for Functional Updates

| Aspect | Rule |
| :--- | :--- |
| Input / result | Receive a deeply immutable root admitted by [`SharedObject`](#normative-rules-for-built-in-operations), including eligible nominal and opaque representations. Return an immutable result of the same data type and declared member modes |
| Invalid root (`E0536`) | Ineligible type, contained authority, or live origin. Check root eligibility before the draft parameter |
| Draft | `Draft<T>` is the scoped projection of the current draft of `T`. The recipe receives a fixed `mut` handle and returns `()` |
| Projection | Resolve paths and member data types using `T` and its verified constraints, including generic record rows. At each otherwise accessible path, draft updates may replace fixed members and traverse immutable members subject to the stored-key and shape rules below. Nominal and opaque boundaries follow their ordinary visibility rules |
| Update | Resolve the path in the current draft. Replace the selected value and rebuild its ancestors with their other contents intact. A finite path through a cycle follows the same rule |
| Draft access | Reads and borrows refer to the selected path. Overlap is checked on draft paths, independently of storage shared by their values |
| Storage | Implementations may reuse unchanged storage, including the entire root for a no-op recipe |
| Insertion (`E0535`) | Insert an immutable value or publish recipe-local fresh data with confined writers as a snapshot |
| Collections | Element and structural updates preserve the base snapshot's length, entries, and order |
| Stored keys (`E0535`) | Stored keys and set elements are immutable values. Collection operations replace entries; writes to other paths leave stored keys and elements intact |
| Declared shape (`E0336`, `E0312`) | Preserve tuple arity, record fields, and sum variants; members may be replaced |
| Confinement (`E0607`) | `derive` creates the draft handle. `Draft<T>` may be named in recipe and helper parameter types. Draft paths, references, and captures remain within the recipe and its non-escaping helpers. Publish after normal completion |
| Effects / abort | Forward the actual recipe's effects and external state/provenance obligations, including surviving captures. Discharge draft writes locally. Abort preserves immutable inputs and prior external writes |
| Finiteness | Propagate the actual recipe's [Diverge effect](#termination-and-halt-contracts) and budget-coverage requirements, including cleanup and recovery; derive does not itself remove Diverge |

```ril
fn update_title<T: .{ title: str, .. }>(item: T, new_title: str) -> T {
    item |> derive \mut draft -> { draft.title = new_title }
}
let item = .{ title: "old", published: true }
let revised = update_title(item, "new")
assert(item.title == "old" && revised.title == "new" && revised.published)
```

```ril
type Board = .{ title: str, items: []int, tags: [str: int] }
let base = Board.{ title: "draft", items: [1, 2], tags: ["a": 1] }
let coords = (10, "Ada")

let revised = base |> derive \mut draft -> {
    draft.items |> mut Array::push(3)  -- []int stays []int
    draft.items[0] = 9                 -- element write
    draft.tags["b"] = 2                -- entry insertion
}
let moved = coords |> derive \mut draft -> { draft.0 = 11 }

assert(len(base.items) == 2 && base.items[0] == 1)      -- base keeps its snapshot
assert(len(revised.items) == 3 && revised.items[0] == 9)
assert(len(base.tags) == 1 && len(revised.tags) == 2)   -- entry inserted
assert(coords.0 == 10 && moved.0 == 11)                 -- tuple type unchanged

-- let wider = base |> derive \mut draft -> { draft.owner = "me" }
-- Error [E0336]: this product has no field 'owner'
-- let longer = coords |> derive \mut draft -> { draft.2 = true }
-- Error [E0312]: tuple index 2 out of bounds for (int, str)
```

```ril
let mut current = Cell.{ count: 0 }
let ref live = current
-- let invalid = live |> derive \mut draft -> { draft.count += 1 }
-- Error [E0536]: derive requires immutable input
let snapshot = clone(ref live)
let version = snapshot |> derive \mut draft -> { draft.count += 1 }
current.count += 1
assert(snapshot.count == 0 && version.count == 1)
```

```ril
-- let number = derive(1, \mut draft -> {})       -- Error [E0536]: value root
-- let text = derive("ab", \mut draft -> {})      -- Error [E0536]: value root
type UserId(int)
-- let id = derive(UserId(1), \mut draft -> {})   -- Error [E0536]: value representation
let changed = .{ count: 1, text: "ab" } |> derive \mut draft -> {
    draft.count = 2
    draft.text = "cd"
}
assert(changed.count == 2 && changed.text == "cd")
```

### Generic Parameters, Defaults, and Value Sorts

```ril
fn log_id<T: .{ id: int, .. }>(item: T) -> int { item.id }
```

Generics admit type, const-value, and member-mode parameters. Const generic parameters support pipeline constraints (e.g. `key: str |> Key<T>`). They apply to data, wrapper, sum, and callable declarations. Access-mode inference supplies implicit static access parameters. `MemberMode` denotes both slot and access components; generic member-mode arguments use concrete modes or static mode expressions.

```ebnf
GenericParams         ::= "<" GenericParamDecl { "," GenericParamDecl } [ "," ] ">"
GenericParamDecl      ::= TypeParamDecl | ConstParamDecl | ModeParamDecl
TypeParamDecl         ::= PascalCase [ TypeConstraint ] [ "=" TypeExpression ]
TypeConstraint        ::= [ ":" TypeSort ] { "|>" PipelineConstraint }
TypeSort              ::= TypeSetSort | "Type" | KindSignature | RecordConstraint
TypeSetSort           ::= TypeReference "|" TypeReference { "|" TypeReference }
PipelineConstraint    ::= QualifiedName [ GenericArgs ]
ConstParamDecl        ::= ValueName ":" ValueType { "|>" PipelineConstraint } [ "=" Expression ]
KindSignature         ::= "Type" "->" ( "Type" | KindSignature )
RecordConstraint      ::= ".{" [ RecordConstraintField { "," RecordConstraintField } "," ] RecordTail "}"
RecordConstraintField ::= [ MemberMode ] FieldLabel ":" TypeExpression
GenericArgs           ::= "<" GenericArg { "," GenericArg } [ "," ] ">"
GenericArg            ::= TypeExpression | Expression | MemberModeLiteral
ModeParamDecl         ::= PascalCase ":" ModeSortReference [ "=" ( MemberModeLiteral | QualifiedName ) ]
MemberModeLiteral     ::= "var" [ "mut" | "^mut" | "ref" ] | "mut" | "^mut" | "ref"
ModeSortReference     ::= [ "ril/reflect::" ] "MemberMode"
ValueType             ::= TypeExpression
```

- **Trailing Defaults Invariant (`E0316`)**: If a generic parameter declares a default argument (`= Default`), all subsequent generic parameters in the same parameter list must declare default arguments.
- **Left-to-Right Default Scope Invariant (`E0320`)**: A default argument expression $D_i$ may reference generic parameters declared to its left ($X_1, \dots, X_{i-1}$). Forward references and direct/indirect circular dependencies are statically rejected (`E0320`).
- **Member Mode Sorts (`M: MemberMode`, `E0356`)**: Static parameters may constrain to the ambient `MemberMode` sort. Arguments accept member mode literals (`var`, `mut`, `^mut`, `ref`, etc.) or static expressions yielding `MemberMode`. Incompatible sorts fail with `E0356`.
- **Generic Closed Type Sets (`TypeSetSort`, `E0301`, `E0304`)**: A generic parameter or type function parameter may constrain its admitted domain to a finite union of types (`T: int | f64` or `\T: int | f64`). Body operations and signature type functions must be valid for every $\tau \in \{T_1, \dots, T_n\}$ (`E0301`). At call sites, $T$ resolves to a rigid member before signature type functions evaluate. Static `match <T>` arms covering all members of the closed set are exhaustive; adding a redundant `_` arm is rejected (`E0304`). Result types must normalize to a single rigid type per member (`E0318`).
- **Pipeline Type Constraints (`T |> Guard`, `E0301`, `E0306`)**: A type parameter may pipe into one or more pure type functions (`T |> Numeric`). The guard must be a compile-time pure `type` function of kind `Type -> Type` (`E0306`). An argument type $T_{arg}$ satisfies the guard if and only if:
  $$\text{Valid}(T_{arg}) \iff T_{arg} \not\equiv \text{never} \quad \wedge \quad \text{Guard}\langle T_{arg} \rangle \equiv T_{arg}$$
  The bottom type `never` is statically rejected before guard evaluation, preventing vacuous satisfaction. If $\text{Guard}\langle T_{arg} \rangle$ does not produce definitional identity with $T_{arg}$, the argument is rejected under `E0301`. Multiple guards pipe from left to right: `T |> Guard1 |> Guard2` $\equiv \text{Guard2}\langle \text{Guard1}\langle T \rangle \rangle$.
- **Pipeline Constraint Input Sorts**: A constraint passes its type or static value as the guard's first argument, followed by written arguments; each argument must match its declared sort. Value-parameter constraints require explicit `meta` in ordinary function parameter lists; const generic and type-function value parameters are already static.
- **Constraint Composition**. A structural row constraint and a pipeline guard both apply to the argument type. The `AuditGuard` example below requires an audit field in addition to the value field used by the function.
- **Static Value Sorts**: Const parameters admit scalar values, atomic type tokens, and finite immutable aggregates without resource or callable authority. `tok: Type<T>` is a static value parameter, distinct from a type parameter `T: Type`. A value argument is admitted only for a parameter declared with one of these value sorts. Admission of static-only token values never permits their run-time materialization.
- **Const Generic Evaluation & Purity Invariant (`E0814`, `E0323`)**: Const generic arguments evaluate at compile time within the pure static domain (no outward effects except implicit Diverge and no outward state/provenance obligations). `halt` is optional; evaluation remains subject to the compiler budget. Non-constant runtime expressions passed to const parameters trigger `E0814`. Arguments failing sort constraints or pipeline constraints (e.g. `key: str |> Key<T>`) trigger `E0323`.
- **Strict Generic Argument Sorts (`E0306`, `E0323`, `E0814`)**: Every generic argument is checked against the formal parameter's declared sort. A type parameter admits a type expression; a value parameter admits a static value of its declared sort. A value is never converted to its type; write `typeof e` to supply the type of a value. A value supplied to a type parameter is `E0306`; a value of the wrong sort supplied to a declared value parameter is `E0323`; a non-static value is `E0814`. Adaptation is one-way: a type expression may supply a `Type<T>`-sorted value parameter as a token.
- **No Untagged Literal or Storage Union Types (`E0318`)**: Concrete values (strings, integers, booleans) and untagged value unions (`int | str`) cannot serve as storage, variable, or binding types (`E0318`). Tagged alternatives are declared with sum types (`type HttpMethod { Get, Post }`). Concrete values may be supplied as compile-time arguments only to parameters declared with a const/value sort (`Buffer<u8, 1024>`, `Matrix<f64, 4>`). Finite type sets (`T: int | f64`) are permitted exclusively as static domain constraints on generic parameters (`TypeSetSort`); each call specializes to a single rigid type.
- **Definition-Site Evidence**: Check ordinary generic operations under [K-GEN](#generic-evidence-and-definition-checking). A guard's admission predicate does not by itself establish an arbitrary operation capability; finite token-match evidence and explicit constraints supply their prescribed facts.
- **Function Generic Default Prohibition (`E0317`)**: Function generic parameters cannot declare defaults (`fn f<T = int>` is rejected); function types are inferred bidirectionally at call sites.

Generic arguments follow the declaration's parameter category: type syntax for a type parameter, a static token/value expression for a value parameter. Passing a quoted type or an ordinary value to a type parameter is `E0306`; write `typeof e` when the type of a value is intended. `Type<T>` is the exact static metatype for target `T`; type quotes require a type, and declared value parameters accept values such as `42` in `Buffer<u8, 42>`.

```ril
-- Closed Type Set Constraint:
fn add<T: int | f64>(a: T, b: T) -> T { a + b }
assert(add(1, 2) == 3)
assert(add(1.5, 2.5) == 4.0)
-- let bad_add = add("a", "b")          -- Error [E0301]: type 'str' does not satisfy constraint 'int | f64'

-- Pipeline Type Function Constraint:
type Numeric = \T -> match <T> {
    <int> | <f64> -> <T>,
    _ -> <never>,
}
fn multiply<T |> Numeric>(a: T, b: T) -> T { a * b }
assert(multiply(3, 4) == 12)
-- let bad_mul = multiply("x", "y")     -- Error [E0301]: type 'str' does not satisfy constraint 'Numeric'

-- Value-parameter pipeline constraint:
type NonNegative = \value: int ->
    if value >= 0 { <()> } else { <never> }
fn checked_count(meta count: int |> NonNegative) -> int { count } -- NonNegative<count>
assert(checked_count(3) == 3)
-- checked_count(-1)                  -- Error [E0323]: fails NonNegative
fn scale_count(count: int) -> int {
    -- checked_count(count)            -- Error [E0814]: requires a static value
    multiply(count, 2)                 -- OK: Numeric<int>; count may be a run-time value
}
-- fn missing_meta(count: int |> NonNegative) -> int { count } -- Error [E0120]: requires 'meta'

-- Type Function Specialized to One Member of a Closed Type Set:
type TargetType = \T: int | f64 -> match <T> {
    <int> -> <f64>,
    <f64> -> <int>,
}
fn swap_num<T: int | f64>(x: T) -> TargetType<T> {
    match <T> {
        <int> -> 0.0,
        <f64> -> 0,
    }
}
assert(swap_num(10) == 0.0)
assert(swap_num(2.5) == 0)
-- type BadRedundant = \T: int | f64 -> match <T> {
--     <int> -> <f64>,
--     <f64> -> <int>,
--     _     -> <never>,               -- Error [E0304]: unreachable pattern arm
-- }

-- Rejections: Unspecialized type set application (E0306) and untagged union return (E0318):
-- type BadApp = TargetType<int | f64>  -- Error [E0306]: type parameter 'T' requires a rigid type, not a type set
-- type BadRet = \T -> <int | f64>      -- Error [E0318]: untagged unions cannot be quoted or returned as storage types

-- Composed Structural and Pipeline Constraint:
type AuditGuard = \T -> match <T> {
    <.{ audit_id: int, .. }> -> <T>,
    _ -> <never>,
}
fn get_val<T: .{ val: int, .. } |> AuditGuard>(item: T) -> int { item.val }
assert(get_val(.{ val: 42, audit_id: 1 }) == 42)
-- get_val(.{ val: 42 })             -- Error [E0301]: missing audit_id required by AuditGuard

type Token<value: f64>(int)
meta let _ = assert(<Token<0.0>> != <Token<-0.0>>)
meta let _ = assert(<Token<0.0 / 0.0>> == <Token<0.0 / 0.0>>)

type Choose = \entries: [str: int] ->
    if Map::keys(entries)[0] == "a" { <int> } else { <str> }
type FirstOrder = Choose<["a": 1, "b": 2]>  -- int
type OtherOrder = Choose<["b": 2, "a": 1]>  -- str

-- Member Mode Sort Constraint:
halt type ApplyMode = \T, M: MemberMode -> <.{ M [coords(<T>) as (_, k)]: T.(k) }>
type Slots<T> = ApplyMode<T, var>              -- OK: keyword literal lifting to MemberMode::Var
-- type BadMode<T> = ApplyMode<T, int>         -- Error [E0356]: expected MemberMode sort, found 'int'

-- Strict value/type argument separation:
type Id = \T -> <T>
type IntType = Id<typeof 1024>        -- int: explicit value-to-type conversion
type ByteType = Id<typeof 255u8>      -- u8
-- type BadTypeArg = Id<1024>         -- Error [E0306]: a value cannot supply a type parameter
```

Static argument equivalence determines type and effect instantiation identity. It is distinct from run-time `==`. Arguments must first have the same admitted sort.

| Static value | Equivalence |
| :--- | :--- |
| Booleans, integers, strings, bytes, unit | Exact value; strings are exact scalar sequences |
| Floating values | Canonical IEEE bit representation; signed zeros differ, canonical NaNs agree |
| Type tokens, after adaptation to the formal value sort | Represented target types are definitionally equal, preserving nominal/opaque identity and full schemas; not token address, variable name, or display spelling. Adaptation is one-way: a type expression may supply a `Type`-sorted value parameter |
| Records | Same labels and recursively equivalent fields; written field order is irrelevant |
| Arrays / tuples | Same length and recursively equivalent positional values |
| Maps / sets | Same insertion-ordered entries/members, recursively equivalent |
| Sums / nominal or ordinary opaque values | Same declaration/instance identity and tag where present, then equivalent representation constituents |
| Integer ranges | Same endpoint type, endpoints, and inclusive/exclusive flag |

Sharing multiplicity and allocation identity do not distinguish static arguments. For eligible finite cyclic graphs, use the greatest relation satisfying the table's constituent rules. Live values, callable authority, and resources remain ineligible. Type equality compares these instantiation identities; it does not substitute ordinary collection or floating-point equality.

```ril
-- type TooMany = Option<int, str>    -- Error [E0340]: Option has one generic parameter
fn make_empty<T>() -> new []T { [] }
-- let unknown = make_empty()        -- Error [E0344]: no context determines T
let known: []int = make_empty()       -- OK: result context determines T
```

An explicit generic argument list that cannot fit the declared parameter list is `E0340`, distinct from ordinary value-argument arity (`E0314`) and a supplied argument's kind/sort (`E0306`/`E0323`). Defaults and permitted inference apply before diagnosing absent generic arguments. Where a type or static argument must be determined and neither supplied information nor contextual constraints determine it, use `E0344`; this does not invent a default type for an unconstrained parameter. Incompatible determined types still use their specific mismatch diagnostic.

Every required generic argument at a function call must be determined, including defaults on any instantiated data types. Function generic parameters have no defaults. For an `Ok(1)` argument, the call needs information choosing the error type `E` as well as the success type `T`; if neither the parameter context nor explicit function type arguments determine `E`, the call is rejected with `E0344`.

```ril
-- Sum Type with default type argument:
pub type Result<T, E = str> {
    Ok(T),
    Err(E),
}

let r1: Result<int> = Ok(42)                    -- OK: resolves to Result<int, str>
let r2: Result<int, int> = Err(404)             -- OK: explicit override of default E
assert(r1 is Ok(_))
assert(r2 is Err(_))

-- Nominal wrapper with default const generic and type parameter:
pub type Buffer<T = u8, cap: int = 1024>(.{
    data: []T,
    len: int,
})

let b1: Buffer = Buffer.{ data: [], len: 0 }    -- OK: resolves to Buffer<u8, 1024>
let b2: Buffer<u8, 2048> = Buffer.{ data: [], len: 0 } -- OK: explicit capacity override
let b3: Buffer<i32> = Buffer.{ data: [], len: 0 } -- OK: resolves to Buffer<i32, 1024>
-- type BadTypeArg = Buffer<u8, u8>   -- Error [E0323]: a type cannot supply const parameter 'cap'
-- type BadTypeParam = Buffer<1024>   -- Error [E0306]: a value cannot supply type parameter 'T'

-- Dependent default arguments (left-to-right scope):
pub type Matrix<T, rows: int, cols: int = rows> = .{
    data: []T,
}

let m_sq: Matrix<f64, 4> = .{ data: [] }        -- OK: square matrix, cols defaults to rows (4)
let m_rect: Matrix<f64, 4, 2> = .{ data: [] }   -- OK: explicit rectangular override

pub type Pair<First, Second = First> = .{
    first: First,
    second: Second,
}
let p1: Pair<int> = .{ first: 1, second: 2 }    -- OK: Second defaults to First (int)

-- Rejection: Non-trailing default generic parameter (E0316):
-- type BadOrder<T = int, U> = .{ a: T, b: U }
-- Error [E0316]: generic parameter without default 'U' cannot follow generic parameter with default 'T'

-- Rejection: Forward reference in default argument (E0320):
-- type BadForward<T = U, U = int> = .{ a: T }
-- Error [E0320]: default argument for 'T' contains forward reference to parameter 'U'

-- Rejection: Function generic parameter with default (E0317):
-- fn bad_fn<T = int>(x: T) -> T { x }
-- Error [E0317]: function generic parameter 'T' cannot declare default type; functions rely on caller-site bidirectional inference

-- Rejection: Literal types and untagged unions prohibited (E0318):
-- type BadMethod = "GET" | "POST"
-- Error [E0318]: literal values cannot be used as types; declare a tagged sum type instead

-- Rejection: Runtime expression passed to const generic (E0814):
fn check_buf(runtime_size: int) -> () {
    -- let bad_b: Buffer<u8, runtime_size> = Buffer.{ data: [], len: 0 }
    -- Error [E0814]: const generic parameter 'cap' expects compile-time constant, found runtime expression 'runtime_size'
}

-- Rejection: Const generic sort mismatch (E0323):
-- let bad_sort: Buffer<u8, "1024"> = Buffer.{ data: [], len: 0 }
-- Error [E0323]: const generic parameter 'cap' of sort 'int' supplied with incompatible argument of sort 'str'
```

### Type Definition Boundaries

```ril
use ril/io::{IoError}
eff Io { read_line() -> str, write_line(str) -> () }
eff AsyncIo { ..Io, ..Fiber }
type StateNode = .{ var count: int, tag: str }
type ReaderFn = fn() @Io -> str
type AsyncWorker<T> = fn(T) @AsyncIo -> ()
type Mutator<T> = fn(mut target: T) &mut -> ()
type SharedLogger = fn(str) &up &^mut -> ()
type SocketHandler =
    fn(mut buffer: []u8, timeout_ms: int) @Fiber &mut -> Result<int, IoError>

type TaskStatus {
    Pending,
    Running(fn() @ -> ()),
    Mutating(fn(mut StateNode) &mut -> ()),
    Suspended(.{ duration_ms: int }),
    Completed(int),
}
let status: TaskStatus = Running(\-> Fiber::yield())
assert(status is Running)

type ValidChannel = .{
    mut buffer: []u8,
    stream: fn() @& -> str,
    writer: fn(mut []u8) &mut -> (),
}
with {
    Io::read_line() -> resume "ready",
    Io::write_line(_text) -> resume (),
}
let mut ch = ValidChannel.{
    buffer: [],
    stream: \-> Io::read_line(),
    writer: \mut buf -> { buf |> mut Array::push(0) },
}
ch.buffer |> mut Array::push(42)
ch.writer(mut ch.buffer)              -- Callable field writes its explicit data argument
assert(ch.buffer == [42, 0])

fn test_valid_binding() @Io -> () {
    let result: str = Io::read_line() -- The call has Io; the resulting str has no effect suffix
    assert(result == "ready")
}
assert(ch.stream() == "ready")
test_valid_binding()

halt type MakeNullable = \T -> <?T>
type NullableInt = MakeNullable<int>
```

```ril
-- Io has the preceding declaration. Module storage for the named-state cases:
var app_cache = 0
fn update_cache() &up(sub){mut app_cache} -> () { app_cache += 1 }

-- type BadEffect = @Io               -- Error [E0330]: a single effect is not a data type
-- type BadCombined = @Io + Async     -- Error [E0330]: neither is an effect set
-- type BadMut = &mut                 -- Error [E0331]
-- type BadShare = &^mut              -- Error [E0331]
-- type BadModuleState = &up(sub){mut app_cache} -- Error [E0331]
-- type BadClosure = &up              -- Error [E0331]

-- type BadVariant { Running @Async } -- Error [E0332]: tag annotation
-- type BadMutableVariant { Mutating &mut } -- Error [E0332]: state annotation on a tag
-- type BadPayload { Suspended(int) @Fiber } -- Error [E0332]: payload does not permit a suffix
-- type BadField = .{ value: str @Io } -- Error [E0333]
-- type BadMutableField = .{ buffer: []u8 &mut } -- Error [E0333]: field type is not a callable
-- type BadNamedField = .{ value: int &up(sub){mut app_cache} } -- Error [E0333]
-- type BadTuple = (str @Io, int)     -- Error [E0333]
-- type BadArray = []int @Async       -- Error [E0613]

-- type BadEffectBound<T: @Io> = T    -- Error [E0334]
-- type BadStateBound<T: &mut> = T    -- Error [E0334]
-- halt type BadTypeFn = \T @Io -> <T> -- Error [E0335]
-- type BadTypeState = \T &mut -> <T>  -- Error [E0335]
-- halt type BadTypeBoth = \T @Async &up -> <T> -- Error [E0335]
-- let bad: str @Io = "text"          -- Error [E0613]
-- let @Io bad_prefix = "text"        -- Error [E0613]
```

```ebnf
TypeExpression   ::= PrimaryType
                   | RecordType
                   | TupleType
                   | ArrayType
                   | MapType
                   | CallableType
                   | TypeProjection
                   | TypeFunctionExpr
                   | "?" TypeExpression
                   | "typeof" Expression
                   | MappedRecordType | MappedTupleType
PrimaryType      ::= PrimitiveType
                   | NominalRef
                   | TokenType
                   | "(" TypeExpression ")"
                   | "<" Expression ">"
NominalRef       ::= QualifiedName [ GenericArgs ]
```

| Position | Rule |
| :--- | :--- |
| Data types | Inert shapes: structural products/collections, sums and GADTs, nominal wrappers, opaque types, or pure type-function results |
| Record/tuple member mode | Binding and access mode bound; `var` controls replacement, `mut` interior writes, `ref` observation; no ambient state or provenance clause |
| Callable arrow | Carries a complete latent contract; closed rows match exactly, explicit open markers preserve additional actual obligations, and callable values may be stored, passed, returned, and nested in data |
| Bare `@Eff` / `&State`, or open markers `@` / `&` / `@&`, as a data type | `E0330` / `E0331`; effects use `eff` declarations, state/provenance clauses and callable-row markers are not standalone values or data types |
| Direct effect or state/provenance suffix on a variant | `E0332`, with or without a payload |
| Direct effect or state/provenance suffix on a record field or tuple component | `E0333`; a callable constituent may carry its own suffix |
| Effect or state/provenance constraint on a generic parameter | `E0334`; shape, kind, const, and const-generic pipeline constraints remain allowed |
| Effect or state/provenance annotation on a type function | `E0335` |
| Effect annotation on a value binding or non-callable array expression | `E0613` |

Binding and origin access modes govern access. Effects govern evaluation and handler dispatch; the implicit non-operational `Diverge`, `Panic`, and `Fatal` labels track divergence, unwinding defects, and process-terminating faults. Completed passive values have no direct effect annotation. Stored callables retain full invocation contracts, including latent `Diverge`, `Panic`, and `Fatal`. Finite-budget and panic-absorption coverage remain primitive eligibility conditions, separate from authority and operational effect-row matching.

## Static Semantics and Type Kernel

The following judgments connect the detailed language rules.

### Static Contexts and Judgment Forms

**K-CTX.** Judgments use the following specification context:

```text
C = (D; Delta; Gamma; Phi; F; q)
J = (access, provenance, current obligations, latent contracts,
     consumption/escape/budget conditions, normal-successor flow)
```

| Context | Contents |
| :--- | :--- |
| `D` | Resolved declarations/scopes, schemas, primitive contracts, verified interfaces |
| `Delta` | Rigid type/constructor, const, mode and row binders with their sorts |
| `Gamma` | Value bindings: declared types, slot/access modes, callable contracts, scopes |
| `Phi` | Declared/formation constraints and established local equality evidence |
| `F` | Refinements, origins, lifetime/construction state, consumption, aliases, separation |
| `q` | Type computation, meta-value evaluation, or run-time evaluation |

```text
C |- A : Type                         well-formed data type
C |- H : Type -> ... -> Type          constructor kind
C |- a : Static(S)                    static argument of sort S
C |- A equiv B                        definitional identity
C |- A <: B                           subtyping
C |- Receive(actual, receiver)        reception
C |- MatchCallable(actual, expected)  complete callable matching
C |- e => T ; J                       synthesis
C |- e <= T ; J                       checking
C |- e <= TypeResult ; J              type-producing result checking
```

| Rule | Condition |
| :--- | :--- |
| K-CTX-BIND | Lexically scoped binder identity; alpha-renaming includes all dependent occurrences |
| K-CTX-RIGID | Definition parameters remain rigid; arm-local equations are evidence in `Phi` |
| K-CTX-META | Solve an inference variable at its declared sort/scope; satisfy constraints and occurs check |
| K-CTX-EVIDENCE | Use established premises; recursive cycles do not establish their own guarantees |
| K-CTX-CLOSE | Determine required concrete arguments (`E0344`); retain explicitly admitted symbolic families |

```ril
type Keep = \T -> <T>
type Kept = Keep<int>                  -- OK: a type argument
-- type Wrong = Keep<42>              -- Error [E0306]: an ordinary value is not a type
type TokenKey<token: Type<int>>(int)
type Keyed = TokenKey<int>             -- OK: the declared value sort admits token adaptation
-- type WrongKey = TokenKey<42>       -- Error [E0323]: int value, not Type<int>
```

### Type Formation and Binding

**K-TYPE.** Formation checks the resolved declaration, argument sorts,
constraints and constituent schemas.

| Rule | Premises → result |
| :--- | :--- |
| K-TYPE-PRIM | Primitive `P`, including `never` and `()` → `P : Type` |
| K-TYPE-VAR | `Delta(T) = Type` → `T : Type` under its constraints |
| K-TYPE-APP | Arguments satisfy the constructor's declared sorts/constraints → its declared result kind |
| K-TYPE-PRODUCT | Distinct labels, well-formed constituent types, legal modes/arity → record/tuple type |
| K-TYPE-STORAGE | Well-formed types, legal storage modes and key eligibility → array/map type |
| K-TYPE-CALLABLE | Well-formed parameters, result, modes, rows, sources and dependencies → callable type |
| K-TYPE-TOKEN | `A : Type` → static metatype `Type<A>` |
| K-TYPE-COMPUTE | Admitted forward computation returns one valid token for `A` → computed type `A` |

**K-TYPE-SUBST.** Substitute well-sorted arguments simultaneously, avoiding
capture and scope escape. Traverse types, modes, rows, static arguments, result
sources, contracts and constraints; retain declaration identities and obligations.
Defaults follow [left-to-right substitution](#generic-parameters-defaults-and-value-sorts).
Static arguments use that section's equivalence relation.

**K-TYPE-SYMBOLIC.** Rigid parameters are available symbolic inputs:

```text
forward reduction: substitution; quote/unquote; known type constructors;
                   branch selection justified by Phi
unknown shape/static value: retain dependency until determined
required unsolved inference argument: E0344
```

```ril
halt type WrapField = \T -> <.{ field: T }>
fn wrap_field<T>(value: T) -> WrapField<T> { .{ field: value } } -- OK: forward substitution
let wrapped: .{ field: int } = wrap_field(1)
fn make_empty<T>() -> new []T { [] }
-- let unknown = make_empty()          -- Error [E0344]: no argument or result context determines T
```

**K-TYPE-ROW.** A row position contributes record-kind and absent-label
constraints; check them when its actual remainder is determined.

```text
R : RecordRow     labels(R) intersect L = empty
fields L: distinct labels, well-formed types and modes
---------------------------------------------------- K-TYPE-ROW-EXTEND
.{ fields L, ..R } : Type
```

Anonymous input rows bind independently; named tails preserve their relationship.
A non-record tail is `E0306`; explicit-field/tail overlap is `E0212`, including
when the corresponding value spread permits overriding.

<a id="kernel-fixture-rows"></a>

```ril
type WithId<Fields> = .{ id: int, ..Fields }
type GoodRow = WithId<.{ name: str }>  -- OK
-- type WrongRow = WithId<int>        -- Error [E0306]
-- type Overlap = WithId<.{ id: int }> -- Error [E0212]
fn add_id<T: .{ ..Rest }>(item: T) -> .{ id: int, ..Rest } {
    .{ id: 1, ..item }
}
assert(add_id(.{ name: "Ada" }).id == 1) -- OK: Rest lacks id
-- add_id(.{ id: 2 })                 -- Error [E0212]: result type's remainder overlaps id
```

Tuple arity is zero or at least two. Value-type access modes use `E0402`;
array/map element modes with slot replacement use `E0356`. Sum recovery, opaque
visibility and local-identity confinement remain formation premises.

```ril
type Apply = \M: Type -> Type, T -> <M<T>>
type Present = Apply<Option, int>      -- OK: Option has the admitted constructor kind
-- type WrongKind = Apply<int, int>   -- Error [E0306]
-- type WrongField = .{ ref count: int } -- Error [E0402], including under immutable reception

type ModeBox<M: MemberMode>
halt type TagMode = \M: MemberMode -> <ModeBox<M>>
type MutableTag = TagMode<mut>         -- OK: static mode parameter, nonempty literal
-- type WrongModeSort = Option<mut>  -- Error [E0306]: mode argument in a type position
-- type EmptyArguments = ModeBox<>   -- Error [E0120]: no generic argument
-- type EmptyMode<M: MemberMode = >  -- Error [E0120]: no default value
```

### Definitional Equality and Recursive Types

**K-EQ.** `equiv` is reflexive, symmetric, transitive and respects
capture-avoiding binder renaming. Compare these identity-bearing components:

| Type | Equality |
| :--- | :--- |
| Primitive / grouping | Same primitive; parentheses preserve identity |
| Transparent alias | Its checked expansion; no additional identity |
| Record | Same labels, constituent types and declared modes; field order irrelevant |
| Tuple | Same arity, constituent types and declared modes |
| Collection | Same constructor/storage mode, equal types and equivalent static arguments |
| Nominal / sum / opaque / foreign | Same declaration identity and equal/equivalent arguments |
| Callable | Equal schemas/modes and normalized complete contracts; bound sources renamed by parameter position |
| `Type<A>` | Exact `A` identity |
| Computed type | Equal forward results, or congruent symbolic applications |

Opaque tokens/interfaces preserve declaration identity. Representation equivalence
permits data operations and reception only in the exact defining scope; an inner
`sub` is outside that scope.

**K-EQ-RECURSION.** Transparent alias cycles require nominal or sum indirection
(`E0313` otherwise). A repeated recursive comparison establishes equality only
when the intervening rigid constructors, arguments and schemas match.
Recursive type-function evaluation remains budgeted computation (`E0811`).

<a id="kernel-fixture-equality"></a>

```ril
type Link = Option<Link>               -- OK: the sum reference is an indirection boundary
type Node(.{ var next: ?Node })        -- OK: a recursive nominal representation
-- type Direct = Direct               -- Error [E0313]: no nominal or sum indirection
-- type Bad = .{ next: Bad }           -- Error [E0313]: structural alias cycle
type FirstNode(.{ next: ?FirstNode })
type SecondNode(.{ next: ?SecondNode })
meta let _ = assert(<FirstNode> != <SecondNode>) -- Different nominal declarations
```

```ril
type Left = .{ first: int, second: str }
type Right = .{ second: str, first: int }
type Wrapped(int)
meta let _ = assert(<Left> == <Right>)  -- OK: record field order does not distinguish types
meta let _ = assert(<Wrapped> != <int>) -- OK: representation does not erase nominal identity
meta let _ = assert(<.{ var count: int }> != <.{ count: int }>)
```

### Subtyping, Reception, and Contract Compatibility

**K-SUB.** Equality implies subtyping in both directions; subtyping is
reflexive and transitive.

```text
C |- A : Type
-------------------- K-SUB-BOTTOM
C |- never <: A
```

| Position | Required relation |
| :--- | :--- |
| Closed record | Same labels; immutable members covariant; writable, replaceable or `ref` schemas invariant with matching modes |
| Array / map | Same storage mode; element/key/value types invariant |
| Tuple | Same arity and modes; components invariant |
| Sum / nominal / opaque | Same declaration; arguments invariant |
| `Type<A>` | Exact target identity |
| Callable | Same concrete parameter modes; input shapes contravariant, result shapes covariant; complete `MatchCallable` |

Closed records have no width subtyping. An open input row denotes its quantified
row relationship. Callable result/source guarantees and effect/state rows are
checked independently of data variance; apply them to every retained alternative.

**K-RECV.** Reception uses the actual `T, J` and the receiver's fixed schema:

| Rule | Reception |
| :--- | :--- |
| K-RECV-VALUE | Copy matching value-type data |
| K-RECV-IMM | Prove immutable publication; compare recursively mode-suppressed immutable data views |
| K-RECV-LIVE | Prove actual path authority, matching schema, lifetime, exclusivity and retained-sharing conditions |
| K-RECV-NEW | Prove eligible construction/handoff; end source and derived paths at the transfer point |
| K-RECV-CALLABLE | Check environment-handle reception and `MatchCallable` |

Mode suppression changes the reception view, while declaration/token identity,
invariant container arguments and callable contracts remain fixed. A surviving
writer blocks immutable publication. Later assignment checks the same instantiated
storage schema.

```ril
type Counter = .{ var count: int }
let frozen = Counter.{ count: 1 }
let read_shape: .{ count: int } = frozen -- OK: immutable reception compares suppressed data modes
meta let _ = assert(<Counter> != <.{ count: int }>) -- Declaration schemas remain different
let mut live = Counter.{ count: 1 }
live.count += 1
-- let bad_snapshot = live             -- Error [E0535]: reception cannot freeze a surviving writer
-- let mut bad_upgrade = frozen        -- Error [E0520]: ascription supplies no writer
-- let ref bad_value = frozen.count    -- Error [E0402]: the selected member is a value type
```

```ril
type Small = .{ id: int }
type Wide = .{ id: int, name: str }
let wide = Wide.{ id: 1, name: "Ada" }
-- let erased: Small = wide            -- Error [E0301]: no closed-record width subtyping
let byte: u8 = 1u8
-- let widened: int = byte             -- Error [E0301]: no implicit numeric conversion
-- meta let BAD_TARGET: Type<int> = <never> -- Error [E0301]: target subtyping is not target identity
```

### Bidirectional Expression Checking

**K-EXPR.** Synthesis derives a type; checking propagates an expected type.
Both retain the actual checking metadata in `J`.

```text
C |- e => S ; J     C |- S <: T     compatible result/latent contracts
-------------------------------------------------------------------- K-CHECK
C |- e <= T ; J

C |- e => S ; J     Receive(C, S, J, receiver T) succeeds
------------------------------------------------------- K-RECEIVE
C |- e <= T ; checked reception result

C |- statements => C' ; Jprefix     C' |- tail <= T ; Jtail
--------------------------------------------------------- K-TAIL
C |- { statements; tail } <= T ; sequence(Jprefix, Jtail)
```

Receiving positions use `Receive`'s data view; callable positions also use
`MatchCallable`. Propagate constraints before diagnosing a required instance.

| Form | Checking step |
| :--- | :--- |
| Literal / name | Contextual literal type/defaults; resolve binding and instantiate only its quantified variables |
| Operator / range / interpolation | Check the registered domain/result and sequence operands; short-circuit forms analyze their alternatives |
| Product / collection | Propagate expected member schemas; check each reception; allocate shared-object roots, copy unit/value cases; enforce homogeneous storage and immutable keys |
| Constructor / wrapper | Instantiate declaration, arity and result equations; check payload reception |
| Projection / indexing | Check key/index, select constituent; copy values or preserve bounded object access/origins; payload access requires variant evidence |
| Assignment | Prove slot/interior authority, check fixed schema, invalidate overlapping facts; compound forms evaluate once |
| Call / callable | K-CALL; creation checks latent body/environment and records actual captures |
| Block / binding | Lexical sequencing plus hoisted scopes; reception/decomposition, unit missing tail, Result inspection, cleanup and identity confinement |
| Conditional / match | Check subject once, derive branch evidence, check expected results, K-JOIN; guards are `bool` and do not prove coverage |
| Loop / transfer | Explicit control target; `loop` joins reachable `last` values or is `never`; `while`/`for` and their `last` values are unit |
| Handler / scoped operation | Check arguments, answer type, affine resumption, environment and cleanup; parameterized `with` supplies the remaining computation as its action |

All forms propagate access, origins, writes, consumption and escape under K-CALL.
Static bodies also apply K-PHASE. Detailed surface rules appear in the
[coverage index](#core-rule-coverage).

### Structural Joins and Normal Continuations

**K-JOIN.** With expected `T`, check each normally returning alternative
against `T`. Without context, synthesize by these structural rules:

| Alternatives | Result |
| :--- | :--- |
| No normal successor | `never` |
| One normal result; others `never` | That result |
| Equal types | That type, retaining actual checking metadata |
| Same closed record labels/modes | Recursively join immutable covariant data; invariant data matches |
| Compatible callables | Common determined data shape and all actual contract alternatives |
| Invariant containers / tuple / sum / nominal | Equal required arguments/components |
| Incompatible determined types | `E0351` |
| Undetermined required type/static argument | `E0344` |

For callable synthesis, identical parameter shapes and compatible concrete modes
admit structurally joined results. Other data variance may use an already
determined operand shape admitted by all targets. Require common result/source
guarantees and valid handle reception, including mixed-root and lifetime checks.
Calls and explicit expected contracts check every actual alternative; closed
rows match exactly. Contextual checking can succeed where synthesis lacks a result.

```text
normal-successor facts = facts common to normal alternatives
invocation obligations = union of evaluated operations/state/escapes/transfers
result correlations = relations proved in every retained alternative
```

Static pruning uses the specified rules; ordinary typing still checks unselected
branches under their valid evidence. A terminating branch retains prior operations.
Preserve joint origin correlations, as in `permute`, through the join.

**K-TYPE-RESULT.** `TypeResult` is the internal result-checking sort for a
type-producing computation:

```text
normal branch/transfer produces Type<A>     C |- A : Type
--------------------------------------------------------- K-TYPE-RESULT
C |- branch/transfer <= TypeResult ; J
```

Propagate it through blocks, if/match tails, the callable's `return`, a result
`loop`'s `last`, and admitted static budget actions/results. Different selected
branches may produce different `A`; closed evaluation returns one completed token.
Ordinary token storage remains exact `Type<A>`; `while`/`for` remain unit.

<a id="kernel-fixture-joins"></a>

```ril
let stopped: int = if flag { 1 } else { panic("stop") } -- OK
let absent: ?int = if flag { Some(1) } else { None }    -- OK: context reaches both constructors
let empty: []int = if flag { [] } else { [1] }         -- OK: expected element type
-- let bad = if flag { 1 } else { "one" }             -- Error [E0351]
-- let unknown = []                                   -- Error [E0344]: no element context
fn no_value() -> never { if flag { panic("a") } else { panic("b") } }
```

### Generic Evidence and Definition Checking

**K-GEN.** Check a named generic body's ordinary typing for every admitted
instance at definition time. Its premises include declared constraints and
formation-derived row/mode/parameter eligibility. Body operations do not silently
narrow an explicitly declared domain.

| Evidence | Definition-site check |
| :--- | :--- |
| Closed type set | Check each rigid member |
| Structural / kind / const / mode bound | Use its stated schema/sort facts |
| Registered primitive guard | Use its registered eligibility facts |
| Type equation | K-EQ and rigid constructor recovery |
| Transparent finite guard | Check every admission path under K-GEN-MATCH below |
| Other pure guard | Evaluate admission at determined inputs; its fixed-point equation grants no extra operation capability |

**K-GEN-MATCH.** After transparent aliases/grouping, a finite guard is an
unguarded type-pattern decision tree:

```text
decisions: match <T> with type patterns, including separate or-pattern alternatives
leaves:    <T> or <never>
accept:    leaf <T> and T not equivalent to never
Phi_path:  positive match evidence + exclusions proved by earlier patterns
check:     ordinary generic body under every accepting Phi_path
```

Apply the existing pattern coverage/reachability rules. Calls, arm `if` guards,
recursion and other computations are outside this finite evidence rule; they
remain valid guard programs checked by ordinary admission evaluation. Unproved
ordinary body typing is `E0301`. Symbolic types reduce under K-TYPE-SYMBOLIC;
required closed calls determine all static/generic arguments before concrete
signature evaluation.

| Prescribed dependent condition | Check when its required input is determined |
| :--- | :--- |
| Static introspection/layout/key | Registered target eligibility (`E0306`), coordinate membership (`E0323`), static availability (`E0814`) |
| Meta result / run-time materialization | Token/type-producing-authority exclusion (`E0812`); run-time phase eligibility (`E0816`) |
| Callback/mode/use/source/budget dependency | Its specified family or concrete-use boundary |

These conditions preserve the existing instantiation checks; ordinary operation
capabilities such as `T * T` still require definition-site evidence. Anonymous
inferred families follow K-ANON.

<a id="kernel-fixture-generics"></a>

```ril
halt type Numbers = \T -> match <T> { <int> | <f64> -> <T>, _ -> <never> }
fn square<T |> Numbers>(x: T) -> T { x * x } -- OK: both admission paths checked
halt type AnyType = \T -> <T>
-- fn bad<T |> AnyType>(x: T) -> T { x * x } -- Error [E0301]: no numeric evidence
fn identity<T |> AnyType>(x: T) -> T { x }  -- OK: identity needs no numeric evidence
fn explicit<T: int | f64>(x: T) -> T { x * x } -- OK
assert(square(3) == 9)
-- square("three")                          -- Error [E0301]: failed guard admission
```

Compiler-budget exhaustion during guard evaluation is `E0811`, rather than false admission.
The [selected-use example](#disjoint-call-families-evaluation-budgets-and-branch-pruning)
still rejects `selected_write<false>` with `E0527`.

### Pattern Evidence and GADT Branches

**K-PAT.** Checking a pattern against a subject schema/reception yields
binder types/modes, path refinements, equality evidence and coverage. Use the
[pattern rules](#pattern-matching) for refutability, binders, guards and authority.

```text
subject S<A>     constructor belongs to S                 different owner: E0301
recover local parameters; solve A ~ B under rigid rules   contradiction: E0304
Phi' = Phi + proved equations     C[Phi'] |- arm <= R ; J
--------------------------------------------------------------------- K-GADT-ARM
arm checks against R under Phi'
```

Constructor recovery follows [sum rules](#sum-types-and-gadts), including opaque
boundaries and the prohibition on arbitrary type-function inversion. Evidence
applies throughout the arm to the same rigid parameter, including legal return
or closure transport. The outer binder identity and declared storage schema stay
fixed; arm exit and or-pattern joins retain only common evidence.

`is` introduces no binders. Stable constructor tests supply local evidence under
[narrowing and invalidation](#flow-sensitive-type-narrowing); a failed payload
comparison alone excludes no constructor. Token patterns refine their snapshot.

<a id="kernel-fixture-gadt"></a>

```ril
type Evidence<T> { Int(int) -> Evidence<int>, Bool(bool) -> Evidence<bool> }
fn use_evidence<T>(e: Evidence<T>, y: T) -> T {
    match e {
        Int(n) -> { let next: T = y + n; next }, -- OK: T ~ int in this arm
        Bool(b) -> { let next: T = y && b; next }, -- OK: T ~ bool in this arm
    }
}
fn evidence_scope<T>(e: Evidence<T>, y: T) -> T {
    let chosen: T = match e { Int(n) -> n, Bool(b) -> b }
    -- let invalid = y + 1                      -- Error [E0301]: no equation outside the match
    chosen
}
-- fn impossible(e: Evidence<int>) -> int {
--     match e { Int(n) -> n, Bool(_) -> 0 }     -- Error [E0304]
-- }
```

### Anonymous Generalization and Fixed Storage

**K-ANON.** Infer the anonymous callable's parameter/result constraints and
complete latent contract. Generalize its independent local unknowns:

```text
quantified = local unknowns independent of:
             lexical environment, fixed/captured storage, outer rigid parameters,
             explicit contextual constraints
instantiate = freshen quantified binders; retain environment/schema/origin identities
check = body valid for the inferred family; constraints hold at required uses
```

An independent argument may remain generic in a mutable capturing closure.
Writing an argument into captured `[]int` fixes that argument to `int`.
Concrete storage still requires a determined schema (`E0344`); recursive checking
uses the current declared/verified family.

<a id="kernel-fixture-generalization"></a>

```ril
let identity = \x -> x                 -- OK: generic anonymous identity
assert(identity(1) == 1)
assert(identity("one") == "one")
let read_id = \record -> record.id     -- OK: inferred structural constraint
assert(read_id(.{ id: 1, name: "a" }) == 1)

let mut numbers: []int = []
let mut add = \value -> { numbers |> mut Array::push(value) }
add(1)                                -- OK: retained environment writes numbers
-- add("one")                         -- Error [E0301]: the captured schema remains []int
-- let mut unknown = []               -- Error [E0344]: no generalization of concrete storage
```

### Authority, Calls, and Contract Operations

**K-CALL.** These judgments relate `C`, checked types and `J`:

| Judgment | Input → output |
| :--- | :--- |
| `Receive` | Actual type/`J`, receiver schema → checked reception and updated `F, J` |
| `InstantiateCall` | Target alternatives, static arguments, prepared actuals/entry graph, summaries → result type/`J` and post-call state |
| `NormalizeContract` | Complete obligations, identities, return baseline, alternatives → comparable contracts with actual conditions/metadata |
| `Discharge` | Actual handlers/cleanup and confinement/escape facts → residual obligations and boundary state |
| `MatchCallable` | Actual alternatives, expected callable → input/row/result/environment/lifetime compatibility |

The target must be a checked callable. Explicit operands prepare once in source
order, followed by omitted defaults in their specified order. Each preparation
applies reception and ends transferred construction sources and derived paths at
that point. The call-entry graph is the identity/reachability relation of the
prepared actuals at entry. Each possible target's verified contract applies to
those actuals; the result retains their obligations and only common guarantees.

Termination stops subsequent operands/invocation while retaining earlier
obligations. Callee writes do not extend the frozen entry graph. Concrete markers
follow the ordinary or verified template-elaboration rules.

Substitute formal positions, constituent paths, static/mode arguments, callback
and environment/provider dependencies. Preserve actual aliases, proven separation
and joint input/output correlations. Allocation is fresh per invocation; handoff
preserves identity. Check every result reception against the fixed receiver schema.

| Result | Root proof; contained dependencies remain separately checked |
| :--- | :--- |
| `ref(x)` / `^mut(x)` | Select from `x`'s entry graph |
| `new T` | Verified construction/handoff |
| Plain shared-object `T` | Immutable publication |
| Value type | Copy without reference origin |

Normalization expands aliases, compares static argument identity, canonicalizes
sources/providers, alpha-renames formal sources by position, and includes return
baselines plus prescribed write/retention implications. Retain distinct capture
activations, conditions, mode history, entry relations, footprints and alternatives.

```text
MatchCallable: for every actual alternative
  check data variance, concrete modes, result/source guarantees,
        contained dependencies, environment access and resource/scope lifetime
  closed dimension: exact normalized effect/state-provenance row
  open dimension:   satisfy every explicit entry; retain additional actual entries
```

```text
footprint(direct operation) = that operation
footprint(known callable)   = verified actual operation footprint
footprint(abstract @Effect) = every permitted operation, unless refined by evidence
residual requests          = requests not intercepted by selected handler arms
effect row                 = instances of residual requests + inferred Diverge/Panic/Fatal
```

Footprints and alternatives survive aliases, ascriptions, storage and export.
Callback dependencies remain symbolic until determined. `Diverge`, `Panic`, and `Fatal` have no operations.

| Boundary | Rule |
| :--- | :--- |
| Handler | Arm operations use outer handlers; resumed continuation uses the reinstalled handler; include actual arm/environment/cleanup obligations |
| `resume` | Check operation-result type separately from block-answer type; each retained arm answer fits its boundary |
| Affine resumption | Preserve possible consumption across joins; starting resume ends temporary operation `mut` and derived access permanently; independent retained authority keeps its lifetime rules |
| State discharge | Prove confinement of all relevant roots/environments and no escape; retain reachable-use evidence, independent retention/capture/named-source obligations |
| Cleanup / budget | Cleanup independently excludes residual operations and Diverge; apply K-PHASE for covered invocation Diverge and separate argument/recovery/latent obligations |

<a id="kernel-fixture-calls"></a>

```ril
type Cell = .{ var count: int }
fn forward(new cell: Cell, count: int) -> new Cell { cell }
let mut cell = Cell.{ count: 0 }
type Inspected = typeof forward(new cell, 0) -- OK: the query does not consume cell
-- type Invalid = typeof forward(new cell, cell.count) -- Error [E0549]: invalid internal sequencing
-- forward(new cell, cell.count)      -- Error [E0549]: the second operand uses the ended path
let saved = cell.count
let mut forwarded = forward(new cell, saved) -- OK: the scalar was copied before the handoff
forwarded.count += 1
```

```ril
eff Pair { first() -> int, second() -> int }
fn first_only() @Pair -> int { Pair::first() }
fn handled_first() -> int {
    with Pair::first() -> resume 1
    first_only()                      -- OK: the known footprint contains only first
}
-- fn incomplete(action: fn() @Pair -> int) -> int {
--     with Pair::first() -> resume 1
--     action()
-- }                                  -- Error [E0612]: second remains possible
```

```ril
eff Trace { mark() -> () }
fn plain() -> () {}
fn traced() @Trace -> () { Trace::mark() }
let selected: fn() @& -> () = if choose_trace { traced } else { plain }
let inferred = if choose_trace { traced } else { plain } -- OK: retain actual alternatives
-- let wrong: fn() @Trace -> () = inferred -- Error [E0534]: plain still lacks Trace
-- let exact: fn() @Trace -> () = selected -- Error [E0534]: the plain alternative lacks Trace
```

### Recursive Summaries and Grounded Inference

**K-FIX.** Recursive groups retain stable declaration-owned binder identities
and all call/callback, storage, capture, handler, cleanup and schema dependencies.
Allocation sites and invocation identities remain distinct.

| Judgment | Requirement |
| :--- | :--- |
| Grounding | Facts follow from actual operations, verified contracts, and non-circular dependencies |
| Required use | The least closure of grounded facts under the specified transfer rules |
| `via` family | Its admitted domain and normalized contracts follow from those facts; written annotations are validated against that family |

Unknown relationships remain obligations. Freshness, separation, publication,
non-escape, empty rows, absence of Diverge and budget coverage require grounded proofs;
cycles cannot justify themselves. Potential invocation cycles introduce Diverge.
Discharge removes outward obligations while retaining grounding uses.

Static inference must terminate while preserving storage schemas and consumption
order. Explicitly promised instances remain in the family, and missing
annotations cannot prune it. Static evaluation keeps its separate budget outcome.

```ril
type Cell = .{ var count: int }
fn grounded(mut cell: Cell, remaining: int) &mut -> () {
    if remaining > 0 { cell.count += 1; grounded(mut cell, remaining - 1) }
}                                     -- OK: the write grounds use; recursion still contributes Diverge
-- fn circular(mut cell: Cell) -> () { circular(mut cell) }
-- Error [E0527]: forwarding around the cycle supplies no grounded writable use
```

### Phase Checking and Static Evaluation

**K-PHASE.** Check calls under `q` and their registered phase contract.
Type elaboration/generic metadata is static inside ordinary functions; `halt`
preserves the declaration's call family.

```text
arguments determined/sorted     call permitted in q
forward evaluation under compiler root budget => complete v
v satisfies the required result/token restrictions
--------------------------------------------------------- K-STATIC-APP
static application succeeds with v
```

Symbolic inputs follow K-TYPE-SYMBOLIC. Wait on unknown required inputs; unresolved
closed arguments use `E0344`. Materialization checks the instantiated graph,
opaque metadata, environments and latent type-producing authority:

| Position / outcome | Rule |
| :--- | :--- |
| Run-time parameter/result/storage/capture/constant | Recursively exclude tokens/static-only metatypes (`E0816`) |
| Meta result | Exclude tokens and type-producing authority (`E0812`) |
| `meta let` | Tokens may remain static; eligible token-free ordinary results may become constants |
| Completed type token | One well-formed target, retaining schema/identity |
| Source budget exhaustion | `Err(BudgetError::Exhausted)` after cleanup; inspect/propagate/return Result |
| Compiler root exhaustion | Uncatchable `E0811`; partial previews remain diagnostic data |
| Static panic / assertion / alias cycle | `E0831` / `E0830` / `E0313` |

```text
typeof e:
  check e in an isolated state, including internal order/modes/authority/affine checks
  obtain its checked type
  discard outgoing execution state, consumption, use and effect contributions
```

The potential operand call is unevaluated, so `typeof runtime_call()` can describe
its result in static type elaboration. A malformed operand still fails normally.
Quotation, introspection and mapped types preserve their checked target schemas.

Source budgets remove only independently covered invocation Diverge. Explicit/default
arguments, recovery, cleanup and returned latent callables keep their own checks.
All static roots remain under the compiler limit, including `halt` and source
budgets. Only completed valid results enter semantic interfaces.

<a id="kernel-fixture-phase"></a>

```ril
meta fn size<T>(token: Type<T>) -> int { byte_size(token) }
meta let WIDTH = size(<int>)                    -- OK: ordinary static result
-- meta let BAD_LAYOUT = size(<Type<int>>)      -- Error [E0306]: no ordinary layout
fn runtime_call() -> int { 1 }
type RuntimeResult = typeof runtime_call()     -- OK: checks without invoking
-- meta let BAD_CALL = runtime_call()          -- Error [E0810]
halt type Chosen = \flag: bool -> if flag { <int> } else { <str> }
type IntegerChoice = Chosen<true>              -- OK: int, not a union of token types
type StringChoice = Chosen<false>              -- OK: str
type ChooseLoop = \flag: bool -> loop {
    if flag { last <int> }
    last <str>
}
type LoopChoice = ChooseLoop<true>             -- OK: type-producing last; loop still has Diverge
meta let _ = { var fixed = <int>; fixed = <int> } -- OK: ordinary slot remains exact
-- meta let _ = { var fixed = <int>; fixed = <str> } -- Error [E0301]
meta let TOKEN = <int>                         -- OK: static token remains static
-- meta fn leak<T>(token: Type<T>) -> Type<T> { token } -- Error [E0812]
fn runtime(value: int) -> int {
    -- let token = <int>                       -- Error [E0816]
    value
}
halt fn increment(value: int) -> int { value + 1 }
-- meta let BAD_FAMILY = increment(1)          -- Error [E0810]: halt does not change family
```

[Exhaustion fixtures](#type-evaluation-exhaustion-diagnostics) distinguish
compiler previews from valid types; [source budgets](#finite-evaluation-with-diverge)
return ordinary inspected Result data.

### Semantic Interfaces and Diagnostic Boundaries

**K-IFACE.** Preserve the information needed to recheck consumers:

| Semantic information | Required preservation |
| :--- | :--- |
| Declarations | Scopes, binder sorts/constraints, static arguments, complete schemas |
| Authority | Actual/effective modes, construction history, affine/scope/task/resource conditions |
| Provenance | Root/contained origins, entry paths, aliases, store/return and output correlations |
| Invocation | Admitted families, use conditions, operation footprints, alternatives, callbacks |
| Environments | Environment/provider identities, latent contracts, result publication and escape |
| Obligations | Full rows including `Diverge`/`Panic`/`Fatal`, defaults/cleanup, coverage and dependent static conditions |
| Diagnostics | Source-completion requirements and diagnostic dependency chains |

Aliases forward this metadata; opaque export retains private checking facts.
Relevant interface changes invalidate dependent judgments. Retain the source,
propagation path, boundary and governing rule for diagnostic explanations.
Use [specific diagnostics](#diagnostic-classification): unresolved required
instances are `E0344`, while determined mismatches use their defining code.

### Core Rule Coverage

Surface forms either check directly or elaborate through the listed rules.
Preserve evaluation order, copies, allocation identity, control targets and
consumption points.

| Surface area | Core checking obligation | Defining rules |
| :--- | :--- | :--- |
| Names, scope, imports, `sub`, visibility, entry point, initialization | K-CTX identities; K-TYPE; declaration and boundary checks | [Modules](#modules-and-compilation-units), [initialization](#top-level-initialization-and-purity), [entry](#program-entry-point) |
| Type declarations, aliases, nominal/opaque forms, recursive types | K-TYPE; K-EQ; scope and representation boundaries | [Type declarations](#type-declarations-and-opaque-types), [nominal wrappers](#nominal-type-wrappers) |
| Generic applications, defaults, constraints, implicit rows/modes | K-TYPE-SUBST; K-GEN; K-FIX | [Generics](#generic-parameters-defaults-and-value-sorts), [rows](#record-types-and-row-polymorphism), [mode inference](#access-mode-inference-with-via-and-infer) |
| Primitive literals, strings/interpolation and bytes | K-EXPR contextual literals and primitive domains | [Literals](#numeric-literals), [text literals](#text-and-byte-literals), [text operations](#text-and-byte-operations) |
| Unary, arithmetic, bitwise, equality, ordering, explicit conversions, ranges, holes | K-EXPR operand/result contracts; K-SUB; `E0360` completeness | [Operators](#expressions-and-operators), [equality/key rules](#relational-and-equality-operators) |
| Record/tuple/array/map literals, sums and wrapper constructors | K-TYPE; K-EXPR construction; K-RECV; constructor equations | [Collections](#array-map-and-tuple-types), [sums](#sum-types-and-gadts), [record spread](#record-construction-and-spread-update) |
| Member/computed projection, indexing, safe navigation and slicing | K-EXPR projection; K-PAT evidence; actual path authority | [Indexing](#range-and-sequence-indexing-expressions), [static coordinates](#static-coordinate-parameters-and-computed-value-projection), [narrowing](#flow-sensitive-type-narrowing) |
| `let`/`var`, `mut`/`ref`/`^mut`, pinning, assignment, decomposition | K-RECV; K-EXPR sequencing/fixed schemas; K-PAT | [Bindings](#binding-modes-and-storage-matrix), [assignments](#assignments-and-compound-assignments), [pattern reception](#pattern-reception-and-decomposition) |
| `new`, verified storage handoff, clone, derive, resources and cleanup | K-RECV-NEW; K-CALL confinement/lifetimes; K-PHASE coverage | [Construction locals](#construction-qualified-locals-and-mode-preserving-reception), [handoffs](#verified-storage-handoffs), [derive](#functional-updates-via-derive), [scoped bindings](#scoped-resource-bindings) |
| Calls, named arguments, defaults, pipelines, projection accessors | K-CALL; K-EXPR sequencing and argument mapping | [Defaults](#default-parameters-and-named-arguments), [pipelines](#pipeline-operators), [accessors](#anonymous-functions-trailing-closures-and-projection-accessors) |
| Named/anonymous callables, closures, captures, higher-order calls | K-GEN; K-ANON; K-CALL; K-IFACE | [Callable contracts](#callable-contracts), [closures](#closures-factory-signatures-and-lexical-environments), [higher-order calls](#higher-order-calls) |
| Blocks, tails, `where`, statement results and fallible inspection | K-EXPR sequencing; K-JOIN; scope checks | [Blocks](#block-expressions-tail-values-and-hoisted-declarations), [where](#dual-tier-where-invariants), [Result inspection](#mandatory-inspection-of-fallible-results) |
| `if`, `match`, guarded bindings, `is`, GADT and or-patterns | K-PAT; K-JOIN; stable evidence and invalidation | [Conditionals](#conditional-expressions), [patterns](#pattern-matching), [value tests](#value-tests-with-is), [narrowing](#flow-sensitive-type-narrowing) |
| `loop`/`while`/`for`, `return`/`last`/`next`, short circuit, `?`/`??` | K-EXPR transfer targets; K-JOIN; K-FIX | [Loops](#loop-expressions), [transfers](#control-transfers), [logical operations](#logical-operators), [fallback](#error-and-fallback-operators) |
| Effect declarations/aliases, operation calls, handlers, `resume`, parameterized `with` | K-TYPE concrete operation signatures; K-CALL discharge/answer/affine checks | [Effects](#effect-declarations-and-operation-signatures), [handlers](#effect-handlers), [resumption](#affine-resumption-and-delimited-early-abort) |
| State groups, provenance, callable-handle modes, task crossing | K-CALL actual identities/footprints; K-IFACE | [State](#state-and-provenance-tracking), [exclusivity](#law-of-exclusivity-and-cross-argument-disjointness), [concurrency](#structured-concurrency-and-panic-containment), [channels](#structured-concurrency-channels) |
| `halt`, `Diverge`/`Panic`/`Fatal`, `diverge_budget`, `absorb_panic`, deterministic parallel primitives | K-CALL; K-PHASE coverage, unwind safety, residual obligations and cleanup | [Halt](#termination-and-halt-contracts), [budgets](#finite-evaluation-with-diverge), [panic absorption](#panic-absorption-with-absorb_panic), [data parallelism](#deterministic-data-parallelism-and-divide-and-conquer-primitives) |
| Type quotation, type/meta functions, `meta let`, `typeof` | K-TYPE-COMPUTE; K-GEN; K-PHASE | [Static types](#static-type-values-and-type-quotation), [type computation](#pure-type-functions-and-result-restrictions), [call families](#disjoint-call-families-evaluation-budgets-and-branch-pruning) |
| Type patterns, introspection, mapped types, layout queries | K-PAT; K-EQ; K-PHASE | [Introspection](#static-introspection), [type patterns](#structural-type-pattern-matching), [layout](#compile-time-evaluation-and-layout-queries) |
| Built-ins, prelude, foreign interfaces, exported metadata | K-TYPE; K-CALL registered/trusted contract; K-IFACE | [Built-ins](#built-in-foundational-operations), [foreign declarations](#external-interface-declarations), [contract completion](#mandatory-contract-inference-and-completion) |

Primitive contracts are selected by registered identity; bodyless declarations
must match that registration. Foreign `.d.ril` declarations use their explicit
trusted contracts.

## Declarations and Bindings

### Binding Modes and Storage Matrix

These common mode tables apply to bindings, members, patterns, and callable handles together with boundary-specific parameter, return, storage, and resource rules. Modes are checked statically and erased from run-time representations.

| Axis | Meaning |
| :--- | :--- |
| `let` / `var` | Fixed / replaceable slot; independent of interior access |
| Default access | Deeply immutable snapshots; freely passable across tasks |
| `mut` | Exclusive writable reception; invocation checks current origins and aliases |
| `^mut` | Shared interior/environment write authority; retention follows the state/provenance and local discharge rules |
| `ref` | Read-only observation; a writable target remains live |

Every access is bounded by its traced source, enclosing path, and member mode. Each plain `let` or `var` receives a snapshot; reassigning a `var` selects another snapshot for that slot. All initialization and replacement requires ordinary typing, complete provenance, lawful scope, and authority use. Specialized contexts use the [anti-laundering diagnostic](#monotonic-mode-degradation-and-anti-laundering-matrix).

| Source / condition | Prohibited receiver | Diagnostic |
| :--- | :--- | :--- |
| Value type | Any `mut`, `^mut`, or `ref` binding | `E0402` |
| Immutable shared-object data or any read-only `ref` path | Any writable binding (`let mut`, `var mut`, `let ^mut`, `var ^mut`) | `E0520` |
| Graph with a surviving writer or live dependency | Plain `let` / `var` | `E0535` |
| Existing writable aliases, including internal aliases in a fresh copy, without shared reception | Exclusive `let mut` / `var mut` | `E0510` |
| Explicit shared initializer `^mut expression` | Exclusive `let mut` / `var mut`; declare `let ^mut` / `var ^mut` instead | `E0406` |
| Reassignable writable root without a pinned live origin | Persistent `let ref` / `var ref` | `E0531` |
| Independent allocation / copy or new writable environment, without an established observation origin | Persistent `let ref` / `var ref` | `E0543` |

| Prohibited operation / omission | Diagnostic / requirement |
| :--- | :--- |
| Rebind plain `let`; rebind a fixed `mut`, `^mut`, or `ref` handle | `E0501`; `E0502` |
| Write through default access or `ref` | `E0520`; specialized path diagnostics follow the [anti-laundering table](#monotonic-mode-degradation-and-anti-laundering-matrix) |

#### Reachable Authority Use

The compiler infers uses from all retained possible sources and reachable operations before validating annotations. Each mode or marker requires evidence from those uses. Missing uses and excessive state/provenance annotations reject the program (`E0527` / `E0529`).

| Declaration / executable marker | Required reachable evidence (`E0527` if absent) |
| :--- | :--- |
| `var` / `var ref` | Slot replacement |
| `let mut` / ordinary `mut` parameter | Writable use: an interior write or an authorized writable return, store, capture, or forwarding use |
| `var mut` | Slot replacement and writable use, checked independently |
| `let ^mut` / `var ^mut` | Shared writable reception plus writable use; `var ^mut` also requires slot replacement. Check the entire binding lifetime, including later shared assignments and internal aliases in a copy |
| `^mut` parameter / handler binder | Actual retention of that parameter's writer beyond its temporary call/operation authority; writing alone is insufficient |
| `^mut expression` | A new shared writable receiving path in at least one covered constituent; a purely read-only reception does not use this marker |

| Analysis concern | Rule |
| :--- | :--- |
| Paths | Use source-semantic reachability before optimization. Each required use is independently possible on a retained reachable path; uses need not occur on the same path or on every execution. Statically excluded operations do not count; executed operations before return, panic, or abort still count |
| Call boundaries | Map verified callee, selected-handler, and implicit-cleanup uses to actual origins, lifetimes, and escape relations at the boundary being checked. A callee's returned writer is not caller-level retention unless it survives the caller's relevant boundary |
| Recursion | Compute use summaries from actual base operations and verified primitive/foreign contracts to a monotone least fixed point; retain unresolved provenance and obligations |
| Dependent uses | Preserve static/generic and callback-dependent use conditions in summaries; check them when the required arguments or callable values are determined. A known absent use is an error |
| Latent bodies | Creating a callable or installing an untriggered handler does not execute its body. Check that body's own invocation uses separately; count any actual capture, retention, or environment creation at its creation/escape site |
| Local discharge | Remove discharged outward obligations, not the actual local use evidence. A confined write can justify a local writable binding without adding outward `&mut` |
| Permitted degradation | A defined read-only observation or temporary `mut` call through a shared handle may reduce current access; preserve all origins, aliases, and lifetimes. It neither invents use nor permits idle stronger annotations or arbitrary parameter-mode conversion |

Declared member schemas have no independent `E0527` requirement; immutable reception may suppress their effective mutable/observation modes under [deep immutability](#deep-immutability). Otherwise-valid executable markers and bindings must meet the table above; existing type, mode, origin, and lifetime diagnostics retain precedence. In particular, `let ref seen = ^mut source` is `E0527` when `seen` could lawfully observe `source` without the unused marker. When writable reception is required, a fresh unshared root uses `mut`, not `^mut`, unless an independently specified context requires that degradation.

For an inferred mode family, retain use conditions for every admitted alternative and validate selected instances when their arguments/dependencies are known. `E0550` checks declaration-level mode redundancy; `E0527` checks required uses independently. Valid families may have value-type or otherwise monomorphic instantiations.

Aliases retain all source restrictions; immutable publication cannot revoke a surviving writer. Creating an explicit shared alias preserves the original binding; each invocation checks the resulting alias facts rather than assuming uniqueness from its `mut` spelling.

```ril
type Cell = .{ var count: int }
fn maybe_bump(flag: bool, mut cell: Cell) &mut -> () {
    if flag { cell.count += 1 }
}                                       -- OK: a possible write, not a write on every call
fn keep(^mut cell: Cell) -> ^mut(cell) Cell { cell } -- OK: root return uses retention
fn forward(^mut cell: Cell) -> ^mut(cell) Cell { keep(^mut cell) } -- OK: writer survives this call
-- fn no_escape(^mut cell: Cell) -> () { keep(^mut cell); } -- Error [E0527]: child return alone supplies no retention across this call
fn choose(flag: bool, ^mut a: Cell, ^mut b: Cell) -> ^mut(a | b) Cell {
    var ^mut selected = a
    if flag { selected = ^mut b }
    selected                            -- OK: replacement plus writable return; no interior write needed
}
-- fn read(mut cell: Cell) -> int { cell.count } -- Error [E0527]: no writable use
-- fn write_only(^mut cell: Cell) &mut -> () { cell.count += 1 } -- Error [E0527]: no retention
-- fn circular(mut cell: Cell) -> () { circular(mut cell) } -- Error [E0527]: forwarding is ungrounded
-- let ^mut excess = Cell.{ count: 0 }; excess.count += 1 -- Error [E0527]: no shared reception
let mut source = Cell.{ count: 0 }
source.count += 1
let ref seen = source                    -- OK: required observation uses reduced access
assert(seen.count == 1)
-- let ref redundant = ^mut source     -- Error [E0527]: no writable receiving path
```

```ril
type Document = .{ var title: str }
let original = Document.{ title: "Original" }
let mut draft = clone(original)
let ^mut alias = draft                 -- Explicit writable sharing; no copy
let ref observed = draft
alias.title = "Revised"
draft.title = "Final"
assert(observed.title == "Final" && original.title == "Original")
-- let hidden = draft                 -- Error [E0535]: surviving writer
-- let mut stolen = observed          -- Error [E0520]: ref cannot grant writes
-- let mut hidden = draft             -- Error [E0510]: missing shared reception
-- let mut wrong = ^mut draft          -- Error [E0406]: exclusive declaration with shared initializer
```

### Construction-Qualified Locals and Mode-Preserving Reception

```ril
type Cell = .{ var count: int }
fn transform(new x: Cell) -> new Cell { x }

fn make(flag: bool) -> new Cell {
    let mut cell = if flag { Cell.{ count: 0 } } else { Cell.{ count: 1 } }
    cell.count += 1
    cell
}
fn normalize(new x: Cell) &mut -> new Cell {
    let mut y = transform(new x)
    y.count += 1
    y                                      -- -> new Cell supplies the handoff context
}
fn put(mut cells: [mut]Cell) &mut -> () {
    let mut cell = Cell.{ count: 0 }
    cells |> mut Array::push(new cell)
    -- let count = cell.count               -- Error [E0549]
}
```

A fixed writable local directly receiving a checked constructor, prepared `new` result, or explicit legal handoff may retain a construction path as static provenance. Every retained branch must supply a valid prepared construction result. The concrete receiver must satisfy its reception rules, including necessary shared acknowledgment.

```ril
fn receive(new x: Cell) -> new Cell {
    let mut y = new x
    -- let count = x.count                  -- Error [E0549]: ended during initialization
    y                                      -- Return preparation ends y before cleanup
}
fn borrowed(mut x: Cell, mut cells: [mut]Cell) &mut -> () {
    x.count += 1
    cells |> mut Array::truncate(0)
    -- cells |> mut Array::push(new x)      -- Error [E0548]: mut input did not transfer construction
}
```

| Separate fact | Requirement |
| :--- | :--- |
| Construction history | Retain actual allocation identity and constructor/`new`-call/handoff origins |
| Active construction qualification | Established by checked initial reception; its lifetime follows the rules below |
| Current root privacy | No independently usable surviving alias to the root |
| Initial graph eligibility | Strong complete-graph qualification, checked again for `new` input / exclusive storage |

Construction paths require eligible ordinary shared-object data or movable endpoint carriers admitted by [`Movable`](#task-handles-movable-guard-and-combinators) (`E0411` otherwise); callable, environment, and non-movable resource results follow their reception rules. A fixed `let mut`, or a `let ^mut` justified by its constituent/alias rules, can retain a private construction root. Check root privacy and complete-graph isolation separately, including obligations from shared constituents.

Immutable publication, independent escape/sharing of the qualifying path, or escaping capture ends the affected qualification permanently. Ordinary parameters, module bindings, reassignable/scoped roots, and bare alias initializers are ineligible for initial qualification. Temporary observation/`mut` borrowing may preserve qualification under non-escape and lifetime checks.

Active paths are pinned and affine. A declared `-> new T` supplies construction reception at the return boundary; a bare qualified formal/local is handed onward during return preparation, before cleanup. Arguments and local initializers use the [handoff markers](#fresh-construction-parameters). Each handoff ends the source and derived accesses at its defined preparation point, including on failure. Parameter-derived local writes require `&mut`, as in `normalize`.

```ebnf
ModePreservingBinding ::= "let" "via" ValueName [ ":" TypeExpression ] "=" Expression
```

`let via` receives dependent access modes and provenance within a lexical mode template, including a nested closure using its bound dependencies. Its received mode, schema, contained origins, or environment modes must depend on bound modes or selected-call relations from input callable mode patterns; a merely data-dependent scalar or otherwise fixed reception is redundant (`E0550`). Check the dependency at template level. Each instance uses a concrete lawful reception.

Ordinary `let` is immutable, including inside a template. Outside a template, use a concrete `let`/`ref`/`mut`/`^mut` receiver; `let via` is `E0412`. Every reception requires its source's sharing acknowledgment and authority-use, capture, branch/loop and completion checks.

### Shared Writable Authority

`let ^mut` and `var ^mut` declare shared writable authority directly. The [common mode tables](#binding-modes-and-storage-matrix) define their slot behavior, rejected receptions, and authority-use checks.

```ebnf
SharedMutDecl ::= ( "let" | "var" ) "^mut" ValueName
                  [ ":" TypeExpression ] "=" Expression
```

| Shared-reception site | Required spelling / rule |
| :--- | :--- |
| Single-identifier initialization | `let ^mut x[: T] = expr` or `var ^mut x[: T] = expr`; types are optional |
| Later assignment, field/container reception, or destructuring | Explicit `^mut expression`, or a dependent template operand carrying that acknowledgment; each constituent retains its own mode |
| Template-dependent fixed receiver | `let via` retains verified shared access dependent on bound modes/input callable patterns; concrete reception uses the usual `let ^mut` rules. Neither form invents sharing from an ordinary writable initializer |
| Outward retention | Preserve `&^mut` or the corresponding named obligation after lawful local discharge |
| Pattern, member, or scoped declaration | Use its boundary-specific mode grammar |

Shared reception, parameter retention, and outward state/provenance obligations are distinct [use facts](#reachable-authority-use). Initializing a fresh root and writing it does not by itself justify a shared binding; conversely, a later genuine shared assignment can justify `var ^mut` even when its initializer was unshared.

```ril
type Cell = .{ var count: int }
fn child(^mut x: Cell) -> ^mut(x) Cell { x }
fn make() -> new Cell { Cell.{ count: 0 } }
fn tagged(_tag: int, ^mut x: Cell) -> ^mut(x) Cell { x }

let mut parent = make()
let ^mut fixed: Cell = child(^mut parent)
fixed.count += 1
assert(parent.count == 1)
-- fixed = make()                     -- Error [E0502]: fixed slot

var ^mut current = child(^mut parent)
current.count += 1
current = ^mut child(^mut parent)      -- Every later shared reception needs its own marker
current = make()                      -- Private new result needs no sharing marker
current.count += 1
assert(parent.count == 2 && current.count == 1)
-- current = child(^mut parent)        -- Error [E0510]: declaration does not mark later assignments

let ^mut piped = 0 |> tagged(^mut parent) -- Marker covers the pipeline result, not the scalar input
piped.count += 1
assert(parent.count == 3)

let immutable = Cell.{ count: 0 }
let ref observed = parent
-- let ^mut bad = immutable           -- Error [E0520]: declaration cannot grant write authority
-- let ^mut bad = observed            -- Error [E0520]: a ref cannot become writable
-- let ^mut bad = 1                   -- Error [E0402]: value types use ordinary let/var
```

Mixed patterns use an expression marker:

```ril
type Cell = .{ var count: int }
let mut packet = .{ count: 7, mut item: Cell.{ count: 0 } }
let .{ count, mut item } = ^mut packet -- Explicit expression marker for mixed destructuring
item.count += 1
assert(count == 7 && packet.item.count == 1)
```

### Immutable Bindings

```ebnf
LetDecl ::= [ "pub" ] "let" Pattern [ ":" TypeExpression ] "=" Expression [ "else" Block ]
          | ModePreservingBinding
```

Plain `let` uses default access in the [common mode tables](#binding-modes-and-storage-matrix). The fixtures distinguish immutable publication from live observation.

```ril
type Counter = .{ var count: int }
let x = 10
-- x = 20                              -- Error [E0501]: cannot reassign immutable binding 'x'

let mut source = Counter.{ count: 0 }
let ref observer = source
source.count += 1
-- let bad = source                    -- Error [E0535]: a surviving writer prevents immutable publication
-- let bad_ref = observer             -- Error [E0535]: wrapping or aliasing a live ref is not immutable

fn make_items() -> new []int {
    let mut items: []int = []
    items |> mut Array::push(1)
    items
}
let items = make_items()               -- OK: construction authority ended; immutable publication
let alias = items                     -- OK: multiple references to immutable data
-- let mut stolen = items             -- Error [E0520]: ordinary aliasing cannot recover write authority

-- Pattern destructuring:
let (a, b) = (1, 2)
type Config = .{ capacity: int, items: []int }
let cfg = Config.{ capacity: 64, items: [] }
let .{ var capacity, items: _ } = cfg
capacity += 1                         -- OK: independent scalar copy
-- let .{ capacity: _, mut bad } = cfg -- Error [E0521]: immutable reference cannot acquire write authority
```

### Pinned Mutable Handles

```ebnf
LetMutDecl ::= "let" "mut" Pattern [ ":" TypeExpression ] "=" Expression [ "else" Block ]
```

#### Normative Rules for Pinned Handles

Use the [common mode tables](#binding-modes-and-storage-matrix) for rebinding, value-type exclusions, and authority use. A pinned handle keeps its initial object as the stable root required by [persistent observation](#normative-rules-for-read-only-references).

```ril
type Buffer = .{ mut items: []int }
let mut buf = Buffer.{ items: [1, 2] }
buf.items |> mut Array::push(3)        -- OK: in-place write to pinned buffer
-- buf = Buffer.{ items: [] }          -- Error [E0502]: use 'var mut' for both reassignment and interior writes
-- let mut count: int = 0              -- Error [E0402]: value type 'int' has no interior mutability; use 'var'

-- Pattern-level pinned mutable destructuring:
type NodePair = .{ mut left: Buffer, mut right: Buffer }
let mut pair = NodePair.{ left: Buffer.{ items: [] }, right: Buffer.{ items: [] } }
let .{ mut left, mut right } = ^mut pair
left.items |> mut Array::push(10)      -- OK: pinned mutable handle
right.items |> mut Array::push(20)     -- Both destructured authorities are exercised
-- left = Buffer.{ items: [] }        -- Error [E0502]: cannot reassign pinned handle 'left'

-- Reachable Authority-Use Requirement:
-- let mut unused = Buffer.{ items: [] } -- Error [E0527]: variable 'unused' declared 'let mut' but never modified in-place
```

### Reassignable Mutable Variables

```ebnf
VarDecl    ::= "var" Pattern [ ":" TypeExpression ] "=" Expression [ "else" Block ]
VarMutDecl ::= "var" "mut" Pattern [ ":" TypeExpression ] "=" Expression [ "else" Block ]
```

#### Normative Rules for Reassignable Variables

Use the [common mode tables](#binding-modes-and-storage-matrix) for `var` modes, prohibited exchanges, and authority use. Replacing a slot selects another value/object without retargeting an existing alias to its previous object.

```ril
-- 1. Plain var: reassignable scalar
var counter = 0
counter += 1                           -- OK: reassignable scalar
counter = 10                           -- OK: direct reassignment
assert(counter == 10)

-- 2. Plain var: replaceable snapshot
let original = .{ count: 1 }
var current = original
current = .{ count: 2 }
assert(original.count == 1 && current.count == 2)

-- 3. Reassignable mutable shared-object variable:
type Buffer = .{ mut items: []int }
var mut active_buf = Buffer.{ items: [1] }
active_buf.items |> mut Array::push(2) -- OK: in-place mutation
active_buf = Buffer.{ items: [10, 20] } -- OK: handle reassignment permitted on 'var mut'
assert(len(ref active_buf.items) == 2)
-- var mut scalar = 0                  -- Error [E0402]: scalar mutation uses plain var

-- 4. Reassignable writable root cannot supply a persistent live ref:
-- let ref bad_ref = active_buf       -- Error [E0531]: var mut is not a pinned mutable root

-- 5. Pattern-level var destructuring:
var (start_idx, end_idx) = (0, 10)
start_idx += 1; end_idx -= 1           -- OK: both variables reassignable

-- 6. Reachable Authority-Use Requirement:
-- var unused_var = 100                -- Error [E0527]: variable 'unused_var' declared 'var' but never modified or reassigned
```

### Scoped Resource Bindings

```ril
type Resource = .{ var name: str, var mut on_close: fn() & -> () }
let mut events: []str = []
{
    let scoped mut first = Resource.{
        name: "first", on_close: \-> { events |> mut Array::push("first") },
    }
    let scoped mut second = Resource.{
        name: "second", on_close: \-> { events |> mut Array::push("second") },
    }
    second.name = "renamed"
}
assert(events == ["second", "first"])
```

```ril
-- Resource has the structural declaration above.
let mut events: []str = []
{
    let scoped mut resource = Resource.{
        name: "r", on_close: \-> { events |> mut Array::push("old") },
    }
    resource.on_close = \-> { events |> mut Array::push("new") }
}
assert(events == ["new"])
-- let scoped scalar = 42              -- Error [E0541]: no cleanup operation
```

#### Normative Rules for Scoped Bindings

| Concern | Rule |
| :--- | :--- |
| Ordinary resource | Accessible zero-argument unit-result cleanup callable required (`E0541`); `on_close: fn() & -> ()` preserves actual state and provenance obligations, while operational cleanup effects (`E0616`), finiteness (`E0617`), and invocation authority retain their separate checks |
| Opaque resource | Requires an explicit scoped-cleanup operation, such as [channel endpoint cleanup](#structured-concurrency-channels); opacity alone supplies none (`E0541`) |
| Registration | After successful initialization; per binding and per loop activation; failed initialization registers nothing |
| Exit | Invoke once in reverse registration order, including cancellation/abort; double-fault exception below |
| Callback selection | Read the current `on_close` at exit; retain no earlier snapshot. Opaque resources use their specified action |
| Initialization/replacement | Preserve cleanup eligibility and access modes; no residual operational effects (`E0616`) or `Diverge` (`E0617`) |
| Mutable cleanup environment | Requires `let scoped mut` and `mut`/`var mut on_close`; replacement also needs `var`; cleanup invocation satisfies `E0527` |
| Other binding modes | Plain `let scoped` requires immutable data; rebinding: `E0502`; `var`/`var mut`: `E0532` |
| Invocation | Internal handlers and permitted writes allowed; check exclusivity then, not as continuous registration access |
| Escape | `ref` handles, closures, containers, and transfer cannot carry scoped authority out (`E0604`); detached ordinary-data copies are exempt |
| Children | Finish before cleanup of resources they could access |

```ril
type WrongCleanup = .{ on_close: int }
-- let scoped bad = WrongCleanup.{ on_close: 0 } -- Error [E0541]: on_close is not fn() -> ()
type Cleanup = .{ on_close: fn() -> () }
{ let scoped good = Cleanup.{ on_close: \-> () } } -- OK: finite cleanup lambda
```

Missing, inaccessible, or shape-incompatible scoped cleanup operations are `E0541`. For a shape-compatible cleanup, residual operational effects use `E0616`, residual or unresolved `Diverge` uses `E0617`, and insufficient authority uses the applicable mode/authority diagnostic. Opaque resources require explicit cleanup support and preserve representation opacity.

| Cleanup panic occurs during | Outcome |
| :--- | :--- |
| Normal exit | Begin `@Panic` unwinding of remaining resources |
| Panic, cancellation, or abort | `DoubleFaultFatal`: abandon remaining cleanup and terminate the OS process immediately (`@Fatal`) |

Abandoned computations cannot resume. A pure parallel branch exposes a double fault only when that branch is visible in reference evaluation; see [parallel faults](#parallel-faults-fatal-visibility-and-budgets).

```ebnf
ScopedDecl ::= "let" "scoped" [ "mut" ] Pattern [ ":" TypeExpression ] "=" Expression [ "else" Block ]
```

### Read-Only Reference Bindings

```ebnf
LetRefDecl ::= "let" "ref" Pattern [ ":" TypeExpression ] "=" Expression [ "else" Block ]
VarRefDecl ::= "var" "ref" Pattern [ ":" TypeExpression ] "=" Expression [ "else" Block ]
```

```ril
type Cell = .{ var count: int }
let fallback = Cell.{ count: 0 }
let ref fixed = fallback              -- Immutable reference is a valid target
let immutable_alias = fixed            -- Proven immutable origin survives ref reception

var selected = fallback
let ref saved = selected              -- Select the current object once
selected = Cell.{ count: 9 }
assert(saved.count == 0 && selected.count == 9)

let mut live = Cell.{ count: 1 }
let ref chosen = if use_live { live } else { fallback } -- use_live is a bool input
var ref cursor = fallback
cursor = live
live.count = 2
assert(cursor.count == 2 && chosen.count == if use_live { 2 } else { 0 })
cursor = fallback
assert(cursor.count == 0 && immutable_alias.count == 0)
-- let ^mut bad = fixed              -- Error [E0520]: immutable-backed refs grant no writes
-- let hidden = chosen                -- Error [E0535]: a possible live origin remains live
```

#### Normative Rules for Read-Only References

Persistent observation follows the [common mode tables](#binding-modes-and-storage-matrix) and these origin and evaluation rules:

| Concern | Rule |
| :--- | :--- |
| Eligible origin | Proven immutable shared object/environment, or live shared object rooted in pinned `let mut`; trace projections, existing `ref` handles, and verified calls |
| Branch, cursor replacement, or forwarded result | Preserve and validate every possible origin; immutable targets stay constant, writable targets remain live |
| Independent allocation / copy / new writable environment | Establish an immutable or lawful writable root before persistent observation (`E0543`) |
| Passive aggregate / observer closure | Combine only established eligible origins and immutable values; wrappers cannot repair origins |
| Initializer / projection | Evaluate once; keep the selected object alive; later source-slot/member replacement does not retarget it |
| Observer closure invocation | Read captures at invocation time |
| Task crossing | A `ref` handle cannot cross (`E0601`) |

These origin rules also apply to `ref` members and shared-object pattern targets. Value-member reads copy their current value. [`ref` parameters](#parameter-modes-caller-obligations-and-defaults) instead use call-time observation rules.

```ril
type Cell = .{ var count: int }
let mut cell1 = Cell.{ count: 1 }
let mut cell2 = Cell.{ count: 0 }

let ref observed = cell1
let ref packet = .{ ref item: observed, offset: 1 }
let ref read_count = \-> packet.item.count + packet.offset
cell1.count = 5
assert(read_count() == 6)
-- observed.count = 10                -- Error [E0520]: no write authority
-- observed = cell2                   -- Error [E0502]: pinned ref
-- let reader = \-> observed.count    -- Error [E0535]: live capture
-- let ^mut stolen = observed        -- Error [E0520]: no access-mode upgrade
let immutable = Cell.{ count: 1 }
let ref constant = immutable         -- OK: fixed immutable observation
assert(constant.count == 1)
-- let ref bad = Cell.{ count: 0 }    -- Error [E0543]: independent new data
let snapshot = clone(ref observed)   -- Independent immutable copy

var ref cursor = cell1
cell2.count = 2
cursor = cell2
assert(cursor.count == 2)
-- cursor.count = 20                  -- Error [E0520]: reassignability grants no writes
-- cursor = clone(ref cell2)         -- Error [E0543]: independent new data

-- Single evaluation and selected-object survival:
type Parent = .{ var mut child: Cell }
let mut parent = Parent.{ child: Cell.{ count: 1 } }
let ref child = parent.child
parent.child = Cell.{ count: 9 }
assert(child.count == 1)                -- Keeps the original child, not a reactive projection

type TaskStatus { Pending(str), Finished(int) }
let mut tasks: []TaskStatus = [TaskStatus::Pending("waiting")]
let ref v = tasks[0]                   -- 'v' holds a read-only ref of the Pending object
tasks[0] = TaskStatus::Finished(42)     -- Slot 0 is updated; 'v' safely keeps the original object

-- Pattern-level ref destructuring:
type NodePair = .{ mut left: Cell, mut right: Cell }
let mut pair = NodePair.{ left: Cell.{ count: 10 }, right: Cell.{ count: 20 } }
pair.left.count += 1
let ref .{ left: v_left, right: v_right } = pair
assert(v_left.count == 11 && v_right.count == 20)
```

### Type Declarations and Opaque Types

```ebnf
MetaAttr         ::= "meta" "(" MetaArgList ")"
MetaArgList      ::= Expression { "," Expression } [ "," ]
TypeDecl         ::= [ "pub" ] [ "halt" ] "type" PascalCase [ GenericParams ] [ WhereClause ] "=" TypeExpression
OpaqueTypeDecl   ::= { MetaAttr } [ "pub" ] "opaque" "type" PascalCase [ GenericParams ] [ WhereClause ] "=" TypeExpression
LocalTypeDecl    ::= TypeDecl | OpaqueTypeDecl | NominalDecl | SumTypeDecl
WhereClause      ::= SignatureWhereClause
TypeList         ::= TupleMember { "," TupleMember } [ "," ]
TypeReference    ::= QualifiedName [ GenericArgs ]
```

```ril
-- Transparent Type Declarations:
pub type AccountId = int              -- Direct type alias, transparent across module boundaries
type Point = .{ x: int, y: int }        -- Local record type alias

-- Cyclic structural type alias rejection (E0313):
-- type BadCyclicA = .{ following: BadCyclicB }
-- type BadCyclicB = .{ prev: BadCyclicA } -- Error [E0313]: structural type aliases 'BadCyclicA' and 'BadCyclicB' form a cyclic dependency without nominal or sum indirection

-- Opaque Type Declarations:
-- In file: auth/session.ril

-- Declares an opaque type with representation 'str' within its exact defining sub:
pub opaque type SessionToken = str

-- Inside defining sub 'Session': SessionToken and 'str' are bidirectionally equivalent:
pub fn create_token(raw: str) -> ?SessionToken {
    if len(raw) >= 16 {
        Some(raw)                      -- OK: internal code constructs SessionToken from str directly
    } else {
        None
    }
}

pub fn reveal_token(token: SessionToken) -> str {
    token                              -- OK: internal code unwraps SessionToken to str directly
}

-- Inside defining sub, underlying operations work natively:
fn validate_token(token: SessionToken) -> bool {
    token == "admin_override"          -- OK: underlying string operations available inside defining sub
}

-- Inline sub boundary seals opaque representation even within the same file:
pub sub Audit {
    pub fn check_same(a: Super::SessionToken, b: Super::SessionToken) -> bool {
        -- let raw: str = a            -- Error [E0301]: opaque across sub boundary
        a == b                         -- OK: same-type equality permitted
    }
}

-- In file: app/main.ril
use auth/session::{SessionToken, create_token, reveal_token}

-- let bad_top_token = create_token("secret_token_1234")? -- Error [E0205]: postfix '?' operator used outside function or closure body; no enclosing activation frame to receive early return

fn authenticate_client() -> ?SessionToken {
    let token = create_token("secret_token_1234")? -- OK: propagated via '?' inside function frame

    -- External boundary invariants:
    -- let bad_assign: SessionToken = "raw" -- Error [E0301]: expected opaque 'SessionToken', found 'str'
    -- let bad_unfold: str = token         -- Error [E0301]: cannot implicitly convert opaque 'SessionToken' to 'str'
    -- let bad_inner = inner(token)        -- Error [E0308]: 'inner()' cannot penetrate opaque type 'SessionToken' (requires type W(T))
    -- let SessionToken(s) = token         -- Error [E0308]: opaque type 'SessionToken' does not expose a pattern deconstructor

    -- Valid external operations:
    let same_eq = (token == token)         -- OK: same-type equality permitted when underlying type supports '=='
    -- let cross_eq = (token == "raw")     -- Error [E0301]: cannot compare distinct types 'SessionToken' and 'str'

    -- Operations via explicit exports & pipeline:
    let raw_str = token |> reveal_token()  -- OK: explicit deconstruction via exported function

    -- Nominal wrappers in collections:
    let active_tokens: []SessionToken = [token]
    let token_map: [SessionToken: int] = [token: 42]

    Some(token)
}
```

#### Declaration Metadata Attributes

```ril
pub type Tool(str)
pub type Flag(.{ short: str, required: bool = false })

meta(Tool("search_docs"))
pub type SearchArgs(.{
    meta(Flag.{ short: "-q", required: true })
    query: str,
    meta(Flag.{ short: "-n" })
    limit: int = 10,
})

pub type ErrorKind {
    meta("retryable")
    Timeout,
    InvalidInput(str),
}

-- meta("alias") type RawAlias = .{ x: int }         -- Error [E0708]: transparent alias has no declaration identity
-- type Anon = .{ meta("x") x: int }                 -- Error [E0708]: structural record field cannot carry meta(...)
-- meta(runtime_val) type BadNominal(int)            -- Error [E0814]: attribute argument must be static
-- meta(<int>) type BadTokenAttr(int)                -- Error [E0812]: attribute value cannot contain type tokens
```

| Attribute rule | Requirement |
| :--- | :--- |
| Admitted targets | `NominalDecl` and its root record fields, `OpaqueTypeDecl`, `SumTypeDecl` and `VariantDecl`, `FunctionDecl`, `MetaFnDecl`, `EffectDecl` and `EffectOpDecl`, `SubDecl`, and `.d.ril` `DeclUnitItem`s other than `TypeDecl` / `UseDecl` (`E0708` elsewhere) |
| Static evaluation | Each expression in `meta(...)` evaluates at compile time in the pure static domain (`E0814` on runtime expressions) to an ordinary value free of type tokens, callables, and resources (`E0812` / `E0816`) |
| Passive data | Attributes never alter type identity (`K-EQ`), subtyping, member modes, layout, exhaustiveness, effects, or run-time execution; compile-time queries use [`Reflect`](#metadata-and-documentation-introspection) |

### External Interface Declarations

External interface declarations are declaration-only modules in `.d.ril` files, specifying host contracts, uninterpreted foreign types, and data-exchange rules without implementation bodies.

| Direction / interface | Contract |
| :--- | :--- |
| Ril calls host | `.d.ril` declarations |
| Host calls translated Ril | Host-language declarations plus a supported entry protocol |
| ABI | Each target binding must document supported type mappings, calling conventions, and compatibility; Ril defines no universal binary ABI |

Shape declarations and `byte_size` establish no external binary layout.

```ebnf
DeclUnitItem     ::= { MetaAttr } [ "pub" ] ( DeclFunction | DeclType | DeclLet | DeclForeignType | DeclSub )
                   | UseDecl

DeclSub          ::= "sub" PascalCase "{" { DeclUnitItem Separator } [ DeclUnitItem ] "}"

DeclFunction     ::= "fn" ValueName [ GenericParams ]
                     "(" [ ParameterList ] ")" [ EffectAnnot ] [ StateAnnot ]
                     [ ReturnSpec ]
                     [ SignatureWhereClause ]

DeclType         ::= SumTypeDecl | NominalDecl | TypeDecl
DeclForeignType  ::= "type" PascalCase [ GenericParams ]
DeclLet          ::= "let" ScreamingSnakeCase ":" TypeExpression
```

#### Normative Rules for External Interface Modules
- **Body Prohibition Invariant (`E0901`)**: Functions declared in `.d.ril` must not contain implementation bodies (`{ ... }`). Top-level constants must not declare initialization expressions (`= expr`). Supplying an implementation body or initializer in a `.d.ril` file is statically rejected under `E0901: BodyInDeclModuleError`.
- **Missing Body Invariant (`E0902`, `E0909`)**: Functions declared in `.ril` modules require an implementation body unless they match a registered built-in primitive identity. Unregistered bodyless functions trigger `E0902: MissingBodyInStandardModuleError`; signature mismatches against registered primitive contracts trigger `E0909: BuiltinSignatureMismatchError`. External host signatures reside in `.d.ril` modules.
- **Uninterpreted Foreign Types**: A type declaration in `.d.ril` without a definition body (`pub type DomWindow`) defines an uninterpreted foreign nominal type. Direct field access (`x.field`), bracket indexing (`x[0]`), nominal unwrapping (`inner(x)`), pattern deconstruction, and direct value instantiation are statically rejected under `E0907: ForeignStructuralFieldPenetrationError`.
- **Exchange Data Types**: Transparent type aliases, records, and tagged sum types may provide full shape definitions in `.d.ril` for foreign data exchange.
- **Top-Level Immutability**: Top-level variables in `.d.ril` are restricted to immutable handles (`let`). Declaring `var` or `let mut` is statically rejected under `E0901`.
- **Signature `where`**: `DeclFunction` supports signature `where` (`SignatureWhereClause`) for aliasing signature callback types. Foreign declarations permit only this tier.
- **Foreign Fault Containment**: A conforming external implementation must prevent host traps and exceptions from escaping as foreign control flow or corrupting Ril execution state. The declared boundary contract maps domain failures to `Result<T, E>` and defects to Ril panic unwinding. Panic containment follows `absorb_panic` and task-boundary rules; a scope does not catch a panic from its own body, and `@Fatal` terminates the process immediately.
- **Ordinary Exchange**: Ordinary inputs, outputs, and constants must be value types or deeply immutable ordinary shared-object data with no surviving foreign writer. They cannot contain live `ref` handles, callables, tasks, or resources. This excludes even immutable environment-free function values: only a separate callback parameter receives the temporary callback rules below. An immutable returned graph may share immutable storage; a plain return type does not establish freshness or write authority (`E0528`).
- **Temporary Callbacks**: Invoke only during the current foreign call, on the current task. Preserve actual effects, origins, environment modes, and exclusivity; mutable invocation requires `mut` on parameter and argument. No environment inspection, retention, return, or cross-task transfer is permitted. Arguments/results must satisfy ordinary exchange or explicit resource rules; mutable data and nested callables gain no exemption.
- **Explicit Resource Contracts (`E0908`)**: Only an explicit resource contract may extend ordinary exchange. Opaque declarations and `@Fiber`/`mut`/`^mut` alone grant no resource mutation, callback retention, copying, closing, or transfer. Reject unsupported requests. Ordinary opaque data retains its actual provenance. Resource contracts cannot grant manual control of Ril managed storage or physical addresses.
- **Trusted Boundary**: An external entity's conformance to its declared contract is a trusted premise. Static checking verifies the Ril program against that contract. Diagnostic explanations identify the foreign contract as the origin of trusted facts; other authority requires proof.
- **Termination and Fault Boundary**: A bodyless external function automatically carries implicit `Diverge`, `Panic`, and `Fatal`, including when its source omits `@`; other omitted operational effect and state rows remain closed. Its declaration cannot assert absence of `Diverge` or budget coverage, and cannot be marked `halt`. A reachable external call propagates `Diverge`, `Panic`, and `Fatal` and is inadmissible within `diverge_budget` (`E0822`) or `absorb_panic` (`E0608`). Language-defined built-ins follow their specified contracts; verified ordinary Ril definitions retain their full effect rows across module boundaries.

| Boundary condition | Required behavior |
| :--- | :--- |
| Immutable exchange | Establish the snapshot before exposing it to Ril; host aliases cannot change it. Host operations cannot mutate ordinary immutable Ril arguments |
| Ril reception | Adaptation grants no writer and cannot turn a live Ril argument into ordinary immutable reception (`E0535`) |
| Value fidelity | Supported mappings preserve every admitted value, including numeric precision, text/bytes, tags, and required identity/alias relationships |
| Retention | Preserve values for every permitted use and retention. Binding-created, otherwise unreachable cycles are reclaimed automatically, including across reclamation domains; lawful host-held values remain reachable |
| Resource lifetime | Closing follows the explicit resource contract, independently of descriptor reclamation |
| Host entry | Expose only signatures with a protocol preserving reception, results, effects, handler/task context, lifetimes, and exclusivity, including on reentry. Ordinary exchange and explicit resource rules apply; a synchronous callback permits entry only during its current call |

```ril
-- In file: platform/dom.d.ril

-- Uninterpreted foreign types:
pub type DomWindow
pub type DomElement

-- Ambient external handle:
pub let WINDOW: DomWindow

-- Transparent exchange data types:
pub type QueryOptions = .{
    timeout_ms: int,
    all_matches: bool,
}

pub type DomError {
    ElementNotFound,
    SecurityViolation(str),
}

-- External function signatures:
pub fn query_selector(win: DomWindow, sel: str) @Fiber -> Result<DomElement, DomError>
pub fn read_attribute(elem: DomElement, key: str) @Fiber -> Result<?str, DomError>

-- Body prohibition in .d.ril (E0901):
-- pub fn bad_body() -> int { 42 }     -- Error [E0901]: functions in '.d.ril' cannot have an implementation body
-- pub let BAD_CONST: int = 100        -- Error [E0901]: constants in '.d.ril' cannot have an initializer expression

-- Opaque penetration prohibited (E0907):
-- fn test_penetrate(elem: DomElement) -> () {
--     let id = elem.id                 -- Error [E0907]: cannot access field on opaque type 'DomElement'
-- }

-- Missing body in standard .ril module (E0902):
-- In file: platform/dom.ril (standard module)
-- fn unimplemented_render(elem: DomElement) -> () -- Error [E0902]: function 'unimplemented_render' declared in standard '.ril' module must have an implementation body
```

The DOM interface above admits read-only `DomWindow`/`DomElement` resource descriptors, the `WINDOW` constant, and the two displayed operations. Repeated queries may designate the same external object; a stable descriptor does not make that object immutable. These operations grant no ordinary write authority, clone/transfer authority, or authority to pass a descriptor to another task. Attribute results are ordinary immutable data. Mutation and retained listener registration are not declared in this interface.

```ril
-- In file: platform/text.d.ril; default ordinary exchange and temporary callback rules:
pub fn get_data() -> []int
pub fn transform_text(text: str, transform: Transformer) @{} &{} -> str
where
    type Transformer = fn(str) -> str

-- pub fn edit(mut items: []int) @Fiber &mut -> ()
-- Error [E0908]: ordinary mutable data cannot cross a foreign boundary
-- pub fn keep(^mut callback: fn() &up -> ()) &^mut -> ()
-- Error [E0908]: default callback authority cannot be retained
-- pub fn hidden_callback() -> .{ action: fn() -> () }
-- Error [E0908]: ordinary returned data cannot conceal callable authority
-- pub fn use_writer(callback: fn(mut []int) &mut -> ()) -> ()
-- Error [E0908]: a callback cannot receive a foreign ordinary writer under the default exchange rules
```

```ril
-- Invocation fixture using the preceding Text module:
let data = Text::get_data()            -- Immutable; not necessarily fresh
-- let mut stolen = Text::get_data()  -- Error [E0528]: the foreign return grants no writer
let original_len = len(data)
let mut copy = clone(data)
copy |> mut Array::push(1)
assert(len(data) == original_len && len(ref copy) == original_len + 1)
let text = Text::transform_text("hello", \value -> value)
```

```text
host updates its original buffer         => data remains unchanged
host alters data or retains transform    => trusted-contract violation
```

Static checking validates the Ril declaration and call; the foreign body's conformance is trusted.

---

## Expressions and Operators

### Expression Grammar

```ebnf
Literal         ::= IntLiteral | FloatLiteral | StringLiteral | RawStringLiteral
                  | ByteStringLiteral | "true" | "false" | "(" ")"
Expression      ::= Literal | HoleExpr | QualifiedName [ GenericArgs ] | EffectOperationRef | "(" Expression ")"
                  | TupleExpr | RecordExpr | ArrayExpr | MapExpr | Block
                  | CallExpr | AnonFnExpr | AccessorExpr | MatchExpr
                  | IfExpr | LoopExpr | WhileExpr | ForExpr | ControlTransfer
                  | ResumeExpr | AssignmentExpr | UnaryExpr | BinaryExpr | PipelineExpr | SharingExpr | ConstructionTransferExpr
                  | MemberExpr | IndexExpr | RangeExpr | IsExpr
                  | Expression "?" | TypeQuoteExpr
HoleExpr        ::= "..."
UnaryExpr       ::= ( "-" | "!" | "~" | "typeof" | "^mut" ) Expression
TypeQuoteExpr   ::= "<" TypeExpression ">"
ConstructionTransferExpr ::= "new" Expression
ArgumentMode    ::= "ref" | "mut" | "^mut" | "new"
PipelineExpr    ::= Expression "|>" [ ArgumentMode ] Expression
BinaryExpr      ::= Expression BinaryOperator Expression
BinaryOperator  ::= "*" | "/" | "%" | "/?" | "%?" | "+" | "-"
                  | "<<" | ">>" | "&" | "^" | "|" | "==" | "!=" | "<" | "<=" | ">" | ">="
                  | "&&" | "||" | "??"
MemberExpr      ::= Expression ( "." | "?." ) ( FieldLabel | TupleIndex )
                  | Expression "." "(" Expression ")"
IndexExpr       ::= Expression ( "[" | "?[" ) ( Expression | SliceRangeExpr ) "]"
```

#### Expression Holes

```ril
type Buf = .{ var len: int }

fn fill(mut buf: Buf, n: int) &mut -> Result<int, str> {
    if n > 0 {
        ...                                -- Type: never; suppresses cascading E0527 / E0549 on this path
    } else {
        buf.len = 0
        Ok(0)
    }
}                                          -- Error [E0360] in complete builds while '...' remains
```

| Property | Rule |
| :--- | :--- |
| Type & modes | `never`; compatible with any expected type `T` and any parameter, return, or binding mode (`mut`, `^mut`, `ref`, `new`) |
| Partial checking | Suppresses cascading `E0527` (unused authority) and `E0549` (incomplete handoff) along control-flow paths ending in `...` |
| Complete build | Statically rejected with `E0360: UnfinishedExpressionHoleError` |

### Operator Precedence and Associativity

| Level | Operators | Associativity | Description |
| :---: | :--- | :---: | :--- |
| **1** | `.` `?.` `?[` `[]` `()` `::` postfix `?` | Left | Member access, safe navigation, indexing, invocation, postfix `?`; a type quote is a primary operand |
| **2** | `-` `!` `~` `typeof` `^mut` `new` | Unary Prefix | Arithmetic negation, logical NOT, bitwise NOT, static introspection (`typeof`), explicit local writable sharing (`^mut`), construction transfer (`new`) |
| **3** | `*` `/` `%` `/?` `%?` | Left | Multiplication, division, remainder, safe division/remainder |
| **4** | `+` `-` | Left | Addition, subtraction |
| **5** | `<<` `>>` | Left | Bitwise shift left, bitwise shift right |
| **6** | `&` | Left | Bitwise AND |
| **7** | `^` | Left | Bitwise XOR |
| **8** | `\|` | Left | Bitwise OR |
| **9** | `..` `..=` | Non-associative | Half-open range, closed range |
| **10** | `\|>` `\|> ref` `\|> mut` `\|> ^mut` `\|> new` | Left | Pipeline `\|>` with optional first-argument mode |
| **11** | `==` `!=` `<` `<=` `>` `>=` `is` | Non-associative | Relational, equality, value test `is` |
| **12** | `&&` | Left | Logical AND (short-circuiting) |
| **13** | `\|\|` | Left | Logical OR (short-circuiting) |
| **14** | `??` | Right | Fallback coalescing operator |
| **15** | `let ... else` | Non-associative | Guarded destructuring binding |
| **16** | `=` `+=` `-=` `*=` `/=` `%=` `&=` `\|=` `^=` `<<=` `>>=` | Non-associative | Assignment and compound assignment |
| **17** | `where` | Non-associative | Block-level trailing hoisted declaration clause |

<a id="arithmetic-and-wrapping-operators"></a>

### Arithmetic Operators

```ril
-- 1. Default arbitrary-precision int (exact, 0 @Panic):
let exact = 9_223_372_036_854_775_807 * 100

-- 2. Fixed-width modular arithmetic (two's-complement wrap, 0 @Panic):
let wrap_add: u8 = 255u8 + 1u8             -- 0u8
let wrap_sub: u8 = 0u8 - 1u8               -- 255u8
let wrap_mul: u8 = 128u8 * 2u8             -- 0u8
let wrap_neg: i8 = -(-128i8)               -- -128i8
let min_div: i8  = -128i8 / -1i8           -- -128i8; -128i8 % -1i8 == 0i8

-- 3. Division and remainder:
-- let zero_lit = 10 / 0                   -- Error [E0361]: constant zero divisor
let half = exact / 2                       -- Nonzero constant divisor: 0 @Panic
fn ratio(a: int, d: int) -> int {
    if d != 0 { a / d } else { 0 }         -- Flow-narrowed nonzero divisor: 0 @Panic
}
fn unchecked_div(a: int, d: int) -> int {
    a / d                                  -- Unproved dynamic divisor: infers implicit @Panic
}
let safe_div = exact /? 0 ?? 0             -- 0 ('/?' and '%?' return ?T; 0 @Panic)
let safe_rem = 10 %? 3                     -- Some(1)
```

| Integer operation | Rule |
| :--- | :--- |
| `int` `+`, `-`, `*`, unary `-` | Exact mathematical integer result; never overflows (`0` `@Panic`) |
| Fixed-width `+`, `-`, `*`, unary `-` | Modular $2^N$ arithmetic (two's complement for `i8..i64`); never panics (`0` `@Panic`) |
| Signed `/`, `%` | Quotient truncates toward zero; nonzero remainder has dividend's sign; fixed-width `MIN / -1 == MIN` and `MIN % -1 == 0` |
| Constant zero divisor (`/`, `%`) | Compile-time error (`E0361: DivisionByZeroError`) |
| Statically nonzero divisor (`/`, `%`) | Nonzero constant, flow-narrowed nonzero condition (`d != 0`, `d > 0`, `d < 0`), or signature guard discharges `@Panic` |
| Unproved dynamic divisor (`/`, `%`) | Evaluates to `T` and infers implicit `@Panic` (panics if divisor is `0`) |
| Safe `/?`, `%?` | Evaluates to `?T` (`None` for zero divisor, `Some(result)` otherwise; `0` `@Panic`) |

| Floating-point property | Rule |
| :--- | :--- |
| Precision | IEEE 754 widths; round each operation to nearest, ties to even; no implicit fusion |
| Special values | Preserve subnormals and signed zero; every NaN result uses the canonical quiet-NaN bits below |
| Overflow / division by zero | Infinity or NaN, without panic |
| Decimal literals | Round once to the contextual floating type |
| Safe division/remainder | `None` for a zero divisor; otherwise retain the IEEE result |
| Remainder | Truncating remainder |

| Floating type | Canonical NaN bits |
| :--- | :--- |
| `f32` | `0x7fc00000` |
| `f64` | `0x7ff8000000000000` |

Arithmetic, unary operations, conversions, and binary decoding/encoding use these same positive-sign NaN patterns. NaN sign and payload from an input are not preserved. These bit rules do not change NaN equality or ordering.

### Explicit Numeric Conversions

The prelude module `Numeric` provides pure, finite, dual-phase conversions.

| Operation | Admitted types | Result |
| :--- | :--- | :--- |
| `Numeric::to_int<From>(value: From) -> int` | Any integer source (`int`, `i8..i64`, `u8..u64`) | Exact lossless conversion to `int` (`E0301` on non-integer) |
| `Numeric::convert<To, From>(value: From) -> ?To` | Numeric source and target | Checked conversion under the rules below |
| `Numeric::saturate<To, From>(value: From) -> To` | Integer source, fixed-width integer target | Clamp mathematical integer to `[To::MIN, To::MAX]` |
| `Numeric::trunc<To, From>(value: From) -> ?To` | Floating source, integer target | Truncate toward zero, then range-check; nonfinite input yields `None` |
| `Numeric::wrap<To, From>(value: From) -> To` | Integer source, fixed-width integer target | Reduce the mathematical integer modulo $2^N$; interpret target signedness using two's complement |
| `Numeric::reinterpret<To, From>(value: From) -> To` | Equal-width fixed integers and/or floats | Transfer the $N$ representation bits; canonicalize a floating NaN input or result |

| `convert` source / target | Rule |
| :--- | :--- |
| Integer / integer | Preserve the exact value; `None` outside the target range; `int` has no range bound |
| Integer / float | Round once to nearest, ties to even; `None` if the rounded result is infinite; finite precision loss is allowed |
| Float / integer | `Some` only for a finite, integral value within the target range; fractions, infinities, and NaN yield `None`; either signed zero becomes integer zero |
| Float / float | Round once to nearest, ties to even; a finite source overflowing to infinity yields `None`; preserve existing infinities and signed zero, canonicalize NaN; underflow to a subnormal or signed zero is allowed |

| Common rule | Contract |
| :--- | :--- |
| Numeric domain | Intrinsic integers/floats; nominal wrappers use explicit unwrapping; opaque representations follow defining-scope transparency |
| Inference | Infer omitted `From` from the argument; an expected result may determine omitted `To` |
| Invalid source / target | `E0301` |
| `trunc` | Range-check the mathematical integer after truncation |
| Reinterpretation | Abstract $N$-bit representation; floating inputs/results use [canonical NaN bits](#arithmetic-operators) |

```ril
-- Overflow-free multi-step fixed-width formulas via Numeric::to_int:
fn checked_offset(x: i32, y: i32, stride: i32) -> ?i32 {
    Numeric::convert(Numeric::to_int(y) * Numeric::to_int(stride) + Numeric::to_int(x))
}
fn clamped_gain(sample: u16, factor: u16) -> u16 {
    Numeric::saturate(Numeric::to_int(sample) * Numeric::to_int(factor) / 100)
}

assert(Numeric::to_int(255u8) == 255)
-- let bad_float = Numeric::to_int(1.5)                 -- Error [E0301]: float requires trunc or convert
assert(Numeric::convert<u8>(256) == None)
assert(Numeric::saturate<u8>(300) == 255u8)
assert(Numeric::saturate<i8>(-200) == -128i8)
assert(Numeric::convert<int>(3.5) == None)
assert(Numeric::trunc<int>(-3.5) == Some(-3))
assert(Numeric::wrap<u8>(-1) == 255u8)
assert(Numeric::convert<f32>(16_777_217) == Some(16_777_216.0f32))
assert(Numeric::convert<int>(0.0 / 0.0) == None)
assert(Numeric::convert<i64>(9_223_372_036_854_775_808.0) == None)
assert(Numeric::convert<int>(9_223_372_036_854_775_808.0) == Some(9_223_372_036_854_775_808))
assert(Numeric::convert<f32>(1.0e300) == None)
assert(Numeric::reinterpret<u32>(1.0f32) == 0x3f800000u32)
let canonical = Numeric::reinterpret<f32>(0x7fa00001u32)
assert(Numeric::reinterpret<u32>(canonical) == 0x7fc00000u32)
-- let wrong_width = Numeric::reinterpret<u64>(1.0f32) -- Error [E0301]
-- let unbounded = Numeric::wrap<int>(1)               -- Error [E0301]
```

### Bitwise and Shift Operators

```ril
-- let text_sum = "a" + "b"           -- Error [E0327]: arithmetic does not concatenate strings
let left = "a"
let right = "b"
let text = "{left}{right}"            -- OK: interpolation
```

An operator applied to a type for which that operation is not defined is `E0327`, including unsupported equality constituents and ordering operands. Different otherwise admissible operand types still use `E0301`; there is no implicit numeric promotion. Boolean conditions and logical operands use the more specific `E0350`.

```ril
let and_val = 0b1100 & 0b1010          -- 0b1000 (8)
let or_val  = 0b1100 | 0b1010          -- 0b1110 (14)
let xor_val = 0b1100 ^ 0b1010          -- 0b0110 (6)
let not_val = ~0b1100                  -- -13 (unbounded two's-complement NOT)
let shl_val = 1u8 << 4u32              -- 16u8 (shift count is u32)
let over_u8 = 0xFFu8 << 8u32           -- 0u8 (overshift count >= N yields 0; 0 @Panic)
let over_i8 = (-8i8) >> 99u32          -- -1i8 (signed overshift yields sign fill)
let big_shl = 1 << 100                 -- Exact 2^100 in int (contextual 100 is u32)
```

| Bitwise / shift operation | Rule |
| :--- | :--- |
| `&`, `\|`, `^`, `~` | Same integer operand type (`E0301`); `int` uses unbounded two's complement |
| Shift count (`<<`, `>>`, `<<=`, `>>=`) | Right operand has type `u32` (`E0301` otherwise) |
| Fixed-width shift (`count < N`) | `<<` discards high bits; unsigned `>>` zero-fills; signed `>>` sign-extends (`0` `@Panic`) |
| Fixed-width overshift (`count >= N`) | `<<` and unsigned `>>` yield `0`; signed `>>` yields `-1` when LHS `< 0` and `0` otherwise (`0` `@Panic`) |
| `int` shift | `x << k` computes $x \cdot 2^k$; `x >> k` computes $\lfloor x / 2^k \rfloor$ |

### Relational and Equality Operators

```ril
let eq = (10 == 10)                    -- true
let ne = (10 != 20)                    -- true
let lt = (5 < 10)                      -- true
let lte = (10 <= 10)                   -- true
let gt = (20 > 10)                     -- true
let gte = (20 >= 20)                   -- true

-- Value test via 'is' (bool result, no bindings):
let opt: ?int = Some(42)
let expected = 40
let matches = opt is Some(expected + 2) -- true; expected is an existing value
```

```ril
assert([1, 2] == [1, 2])               -- Structural equality, independent of allocation identity
assert(.{ x: 1, y: 2 } == .{ y: 2, x: 1 })
let nan = 0.0 / 0.0
assert(!(nan == nan) && nan != nan)
let mut ordered: [str: int] = ["b": 1, "a": 2]
ordered |> mut Map::set("b", 3)
let snapshot = clone(ref ordered)
assert(Map::keys(snapshot) == ["b", "a"]) -- Replacing a value preserves its key's position
-- let bad_keys: [f64: int] = [nan: 1] -- Error [E0328]: floating-point keys are not admitted
let graph_key = [.{ id: 1 }: 0]       -- OK: deeply immutable structural key
assert(graph_key?[.{ id: 1 }] == Some(0))
let coordinates: [(int, int): str] = [(1, 2): "home"]
assert(coordinates?[(1, 2)] == Some("home"))
let shared = [1]
let by_shape = [(shared, shared): 7]
assert(by_shape?[([1], [1])] == Some(7)) -- Structurally equal keys
let by_map = [["a": 1, "b": 2]: 8]
assert(by_map?[["b": 2, "a": 1]] == Some(8)) -- Key map insertion order is ignored
let by_range = [(1..3): 9]
assert(by_range?[(1..3)] == Some(9))   -- Range-typed key
-- let nested_float = [.{ value: 1.0 }: 0] -- Error [E0328]: floating constituent
```

`!=` negates `==`. Equality requires compatible same-typed values (`E0301` otherwise), except the Option/None tag test below and static type tokens: any two tokens compare their represented types by definitional identity, independent of exact/widened metatypes. Token ordering remains unsupported (`E0327`).

| Values | Equality |
| :--- | :--- |
| Numbers | Same numeric type; IEEE NaN unequal to everything, signed zeros equal |
| `bool`, `str`, `bytes`, `()` | Value, exact Unicode scalar sequence, byte sequence, unit |
| Integer ranges | Same endpoint type, endpoint values, and inclusive/exclusive flag |
| Records / tuples / arrays | Labels and values / positions and values / length and elements |
| Sums / nominal wrappers | Constructor and payload / same nominal identity and underlying value (`E0305` for distinct wrappers) |
| Maps / sets | Key-value membership / membership; insertion order ignored |
| Ordinary opaque types | Same-type equality when the representation supports it |
| Option compared to `None` | Tag only; payload need not support equality |
| Callable, task, resource, type-function values | `E0327`, including nested constituents |

Ordering (`<`, `<=`, `>`, `>=`) accepts same-typed numbers, strings, or bytes only (`E0327` for an unsupported operand type; `E0301` for different otherwise admissible types). Strings/bytes use lexicographic order; every ordered comparison involving NaN is false.

For finite cyclic graphs, equality is the greatest binary relation satisfying these structural rules; allocation identity and sharing count are irrelevant. Comparison terminates without user code or overlapping writes; reads follow provenance and exclusivity rules.

| Map key / set element type | Eligibility |
| :--- | :--- |
| `bool`, integers (`int`, `i8..i64`, `u8..u64`), `str`, `bytes`, integer ranges, `()` | Allowed |
| Records, tuples, arrays, sums, maps, sets | Allowed as deeply immutable graphs when every constituent type recursively satisfies this table |
| Nominal / ordinary opaque wrappers | Allowed when their representation recursively satisfies this table; opacity remains enforced |
| Floats, callables, tasks, resources, static-only values, or any nested occurrence of them | `E0328` |

| Key rule | Contract |
| :--- | :--- |
| Type eligibility | Check the complete recursive schema, including map values and every sum alternative |
| Reception | Deeply immutable at insertion, lookup, membership testing, and removal; surviving writers/live dependencies are `E0535` |
| Member modes | Immutable reception suppresses declared write/observation modes |
| Storage | Store immutable key values |
| Equality | Built-in same-type structural equality; allocation identity, sharing count, and map/set insertion order are irrelevant |
| Cycles | Finite cyclic graphs use the greatest structural relation above |
| Hashing | Finite, pure built-in computation; equal keys have equal hashes; resolve collisions by structural equality; work may cover entire reachable graphs |
| Stored graphs | Keys and set elements are immutable snapshots, including in [`derive` drafts](#normative-rules-for-functional-updates) |
| Equal-key update / reinsertion | Keep the first stored key/element and position |
| Static arguments | Use their separate [static equivalence rules](#generic-parameters-defaults-and-value-sorts) |

```ril
type Ring(.{ var value: int, var next: ?Ring })
-- Fixture inputs: left and right are deeply immutable Ring graphs.
-- Every value is zero and every next is Some: left has one self-looping node;
-- right has two nodes pointing to each other. Their allocation shapes differ.
assert(left == right)
let cyclic = [left: "found"]
assert(cyclic?[right] == Some("found")) -- OK: equality-consistent cyclic hashing
```

```ril
type Key = .{ var id: int }
let key = Key.{ id: 1 }
let base = .{ key: key, table: [key: "old"] }
let revised = base |> derive \mut draft -> { draft.key.id = 2 }
assert(revised.key.id == 2 && revised.table?[key] == Some("old"))
let mut live = Key.{ id: 2 }
live.id = 3
-- let invalid_key = [live: 0]         -- Error [E0535]: surviving writable origin
```

| Collection operation | Order |
| :--- | :--- |
| Array iteration | Increasing index |
| Map/set iteration; `Map::keys`/`values` | First insertion |
| Replace map value / reinsert present set member | Keep position |
| Remove, then insert | Append |
| Duplicate map literal key | Last value, first stored key and position; operands still evaluate left-to-right |

#### Value Tests with is

`is` evaluates non-binding pattern conformity: testing tags, shapes, ranges, or structural record subsets. While `==` enforces symmetric same-type structural equality ($T \times T \to \text{bool}$), `is` performs asymmetric pattern testing with structural short-circuiting, driving flow-sensitive type narrowing.

```ril
fn expected() -> int { 40 + 2 }
let answer: Result<int, str> = Ok(42)
assert(answer is Ok)                  -- Tag only
assert(answer is Ok(_))               -- Tag only; no payload equality required
assert(answer is Ok(expected()))      -- Compare payload with the call's result
let wanted = 42
assert(answer is Ok(wanted))          -- Read wanted; never bind a new variable

let nested: Result<?int, str> = Ok(Some(42))
assert(nested is Ok(Some(wanted + 0))) -- Nested constructor tests
let array: Result<[]int, str> = Ok([1, 2])
assert(array is Ok([1, 1 + 1]))        -- Array expression, then whole-array equality
assert((1, 2) is (wanted - 41, _))
assert((.{ id: 1, name: "Ada" }) is .{ id: wanted - 41 })
```

```ril
use ril/os
let result: Result<?Os::NativeString, str> = Ok(Some(Os::from_string("")))
assert(result is Ok(Some(Os::from_string("")))) -- Ordinary call at the value leaf

-- No trailing guard or implicit binding:
-- let bad = result is Ok(Some(text)) -- Error [E0204]: no existing text binding
-- let bad = result is Ok(_) if true -- Error [E0120]: is has no trailing guard
let empty = match result {
    Ok(Some(text)) -> text == Os::from_string(""), -- match still binds text
    _ -> false,
}
assert(empty)
```

```ril
type Pair { Item(int, int) }
let mut trace: []int = []
let mut mark = \n -> { trace |> mut Array::push(n); n }
let value = Pair::Item(1, 2)
assert(value is Item(mark(1), mark(2)))
assert(trace == [1, 2])
assert(!(value is Item(mark(0), mark(99))))
assert(trace == [1, 2, 0])             -- First mismatch skips the remaining test
let failed: Result<int, str> = Err("failed")
assert(!(failed is Ok(panic("skipped")))) -- Tag mismatch skips expected-value evaluation
```

```ebnf
IsExpr          ::= Expression "is" IsTest
IsTest          ::= IsAlternative { "|" IsAlternative }
IsAlternative   ::= "_" | IsConstructor | IsTuple | IsRecord | IsBytes | IsStr | RangePattern | IsValueExpr
IsConstructor   ::= QualifiedName [ "(" [ IsTestList ] ")" ]
IsTestList      ::= IsTest { "," IsTest } [ "," ]
IsTuple         ::= "(" ")" | "(" IsTest "," IsTest { "," IsTest } [ "," ] ")"
IsRecord        ::= [ TypeReference ] ".{" [ IsField { "," IsField } [ "," ] ] "}"
IsField         ::= FieldLabel [ ":" IsTest ]
IsBytes         ::= "bytes" "[" [ IsBytesItem { "," IsBytesItem } [ "," ] ] "]"
IsBytesItem     ::= "_" | ".." | RangePattern | IsValueExpr
IsStr           ::= "str" "[" [ IsStrItem { "," IsStrItem } [ "," ] ] "]"
IsStrItem       ::= ".." | IsValueExpr
IsValueExpr     ::= Expression
```

| Form / boundary | Meaning |
| :--- | :--- |
| Resolved constructor head | Structural test; tag first, then payload. Ordinary callable heads are value expressions. Constructor arity, tuple equivalence and opacity rules apply |
| Existing name / other expression | Evaluate and compare with `==`; `E0301`/`E0305` for incompatible types, `E0327` for unsupported equality. No binders or binding modifiers |
| Tuple / record test | Test components / listed known fields in written order; omitted record fields are unconstrained. Shorthand `.{ field }` means `.{ field: field }`, reading the outer name |
| `bytes[...]` (`IsBytes`) | Subject must be `bytes` (`E0301` otherwise); items test `u8` values/ranges/`_` or `bytes`-typed chunk expressions in order, with at most one `..` matching zero or more middle bytes (`E0347` if repeated) |
| `str[...]` (`IsStr`) | Subject must be `str` (`E0301` otherwise); items test `str`-typed prefix chunk expressions in order, with optional single `..` followed by at most one trailing `str` suffix expression (`E0347` if `..` repeated; `E0349` if more than one item follows `..`) |
| Arrays / maps | Ordinary value expressions with their normal syntax and evaluation order |
| `_` / literal range / `\|` | Ignore constituent / existing integer range-pattern rules / try alternatives left-to-right until one succeeds |
| Parse boundary | Structural test forms take precedence over value expressions. A parenthesized single expression selects whole-value equality; tuples keep their structural form. At test level `\|` separates alternatives; use `(a \| b)` for bitwise OR |
| Outer operators | Undelimited value expressions bind more tightly than `is`; `&&`, `\|\|`, and lower-precedence operators follow the completed test. Parentheses or argument/field delimiters admit a full value expression |
| Execution | Evaluate subject once. At each reached leaf, obtain that constituent, evaluate the expected expression once, then compare. Shape/tag mismatch or an earlier failed component skips later tests; no snapshot or rollback |
| Static checks | Check every test's names, types, modes and ordinary effects/state, including potentially skipped expressions. Expressions inherit ordinary phase, provenance and exclusivity rules |
| Syntax restrictions | A trailing `if` or a binding modifier in a test is `E0120`. Binding patterns and guards use `match` |
| Flow / Results | Preserve only refinements still valid after expected-expression evaluation. Constructor tests inspect the reached Result tags; wildcard and value-equality tests alone do not discharge an outstanding Result |

```ril
let number = 3
assert(number is 1 + 2)
assert(number is 1 | 3)               -- Alternatives
assert(number is (1 | 2))             -- One expected value: bitwise OR
assert(number is 3 && number > 0)     -- Logical continuation outside the test

let magic = bytes"PNG"
let packet = bytes"\x89PNG\r\n\x1a\n\x00"
assert(packet is bytes[0x89u8, magic, .., 0x00u8])

let dir = "src/"
let path = "src/parser/lexer.ril"
assert(path is str[dir, .., ".ril"])

fn check(value: Result<int, str>) -> bool {
    match value {
        -- Ok(expected()) -> true,   -- Error [E0349]: match retains literal/binding patterns
        Ok(n) if n == expected() -> true,
        _ -> false,
    }
}
```

### Logical Operators

`&&` and `||` exhibit strict short-circuiting: the right operand is evaluated only when the left operand does not determine the result.

```ril
-- let bad = 1 && true                -- Error [E0350]: logical operand must be bool
let valid = (1 != 0) && true           -- OK
```

Conditions of `if`, `while`, and pattern guards, and operands of `!`, `&&`, and `||`, must be `bool` (`E0350`). Ril has no implicit truth-value conversion.

```ril
let valid_and = (p != None) && (p.x > 0) -- Right side not evaluated if p == None
let valid_or  = (len(items) == 0) || (items[0] > 0) -- Right side not evaluated if items is empty
let negated   = !valid_and             -- Unary logical NOT
```

### Range and Sequence Indexing Expressions

Only sequence range indexing permits omitted range endpoints.

```ebnf
RangeExpr       ::= Expression ( ".." | "..=" ) Expression
SliceRangeExpr  ::= [ Expression ] ( ".." | "..=" ) [ Expression ]
```

```ril
let r1 = 0..5                          -- Half-open range [0, 5)
let r2 = 0..=5                         -- Closed range [0, 5]

type IntRange = typeof (0..0)
let reversed: IntRange = 5..1
var visited = 0
for reversed as _ { visited += 1 }
assert(visited == 0)                  -- Reversed ranges are empty
for 254u8..=255u8 as value {
    assert(value >= 254u8)
    visited += 1
}
assert(visited == 2)                  -- No increment beyond u8's maximum

let arr = [10, 20, 30, 40, 50]
let slice: []int = arr[1..4]          -- New ordinary array containing [20, 30, 40]
let prefix = arr[..3]                 -- [10, 20, 30]
let suffix = arr[2..]                 -- [30, 40, 50]
let empty = arr[len(arr)..len(arr)]   -- OK: empty array at the end
-- arr[2..1]                          -- Panics: reversed half-open bounds
-- arr[-1..2]                         -- Panics: negative lower bound
-- arr[0..=len(arr)]                  -- Panics: a written inclusive upper bound must index an element
```

| Standalone range | Rule |
| :--- | :--- |
| Endpoints | Same integer type (`int`, `i8..i64`, `u8..u64`); ordinary contextual literal typing applies |
| Non-integer / mismatched endpoint types | `E0327` / `E0301` |
| Evaluation | Evaluate lower then upper once; retain both values and the inclusive/exclusive flag |
| Value type | Immutable, copy-by-value integer range of the endpoint type; both spellings have the same type |
| Public shape | Nameable via `typeof`; no product projections, mutable authority, or additional prelude name |
| `lower > upper` | Empty for either spelling |
| Equal endpoints | Half-open: empty; inclusive: one element |
| Iteration | Ascending by one; stop after the last included value without an overflowing extra increment |
| Other operations | Equality and map-key eligibility as specified above; no ordering, indexing, or `len` |

Ranges are finite even when their integer cardinality exceeds `int`. A range denotes its bounds and step; forming one does not enumerate its members. Range indexing instead uses `int` endpoints (`E0301` for another type) and the bounds below; reversed bounds panic.

```ril
-- 1. Value elements are copied by value:
let mut source: []int = [1, 2, 3]
let slice: []int = source[0..2]       -- New ordinary array containing [1, 2]
source |> mut Array::push(4)          -- Modifying source length does not affect slice
source[0] = 99
assert(slice[0] == 1)                 -- Independent value copy; slice is unaffected
assert(len(ref source) == 4 && len(slice) == 2)

-- 2. Shared object elements preserve object identity:
type Cell = .{ var count: int }
let mut first = Cell.{ count: 1 }
let mut second = Cell.{ count: 2 }
let mut cells: [^mut]Cell = [^mut first, ^mut second]
cells[1].count += 1
let ^mut sub_cells: [^mut]Cell = cells[0..1] -- Acknowledge duplicated writable paths
sub_cells[0].count = 42
assert(cells[0].count == 42)          -- Same Cell object; no graph clone
sub_cells[0] = Cell.{ count: 9 }
let mut extra = Cell.{ count: 10 }
sub_cells |> mut Array::push(^mut extra)
assert(cells[0].count == 42 && len(ref cells) == 2) -- Slots and length are independent
-- let mut bad = cells[0..1]          -- Error [E0510]: new local writable alias needs '^mut'

-- 3. Whole-array observation vs new array:
let ref observer = source            -- Read-only ref directly over pinned mutable array
-- source |> mut Array::push(5)       -- Error [E0537]: observer is used below
assert(observer[0] == 99)
-- observer[0] = 9                    -- Error [E0520]: a ref grants no write authority
-- let ref bad_new = source[0..2]    -- Error [E0543]: new array cannot bind to ref
-- let ref bad_all = source[..]      -- Error [E0543]: new array cannot bind to ref
source |> mut Array::push(5)          -- OK: observer's last use has ended
let snapshot = source[0..2]          -- Publishes an independent immutable array
let ref snapshot_ref = snapshot
assert(snapshot_ref[0] == 99)
let mut copied = source[0..2]
let ref copy_ref = copied
copied[0] = 7
assert(copy_ref[0] == 7 && source[0] == 99) -- Observes the new ordinary array

-- 4. Primitive sub-sequences:
let s = "hello, 世界"
let s_sub: str = s[0..5]              -- "hello" (Unicode scalar coordinates)
assert(s[0..len(s)] == s)             -- Coordinate alignment ensures safe full range indexing

let b: bytes = bytes"RIFF\x00\x01"
let b_sub: bytes = b[0..4]            -- bytes"RIFF" (byte sub-sequence)
-- let ref b_ref = b                -- Error [E0402]: bytes is an immutable value type
let mut byte_array: []u8 = Bytes::to_array(b)
byte_array[0] = 0u8
assert(Bytes::at(b, 0) == Some(82u8)) -- The original bytes still start with 'R'
```

- **Array Result**. Allocate an ordinary array with independent slots and length. Copy value elements and preserve shared-object identities, aliases, and effective access modes. Immutable elements use `[]T`, duplicated writable references use `[^mut]T`, and live read-only observations use `[ref]T`. Root freshness alone gives no proof of element isolation.
- **Writable Sharing (`E0510`)**: Mark reception of duplicated writable reference paths with `^mut`.
- **`ref` Target (`E0543`)**: A fresh range result cannot bind directly to a persistent `ref`. Publish it immutable through `let` or an ordinary parameter, or receive it with a lawful `let mut` binding; a later `ref` observes that established origin. Forwarding preserves whether publication actually occurred.
- **Bounds**: For length N, a half-open range requires `0 <= lower <= upper <= N`; equal bounds produce an empty array, including at N. Omitted lower bounds mean zero; an omitted upper bound denotes the exclusive end N. A written inclusive upper bound h requires `0 <= lower <= h < N` and selects through h. Negative, reversed, or out-of-range bounds panic; bounds are never clamped. Safe range lookup (`arr?[a..b]`) returns an Option of the corresponding array result (`None` when out of bounds).
- **Primitive Sub-Sequences**:
  - `str[a..b]` and `str[a..=b]` evaluate to an independent `str` based on Unicode scalar indices. For a string of length $N$, half-open bounds require $0 \le a \le b \le N$; inclusive bounds require $0 \le a \le b < N$. Range indexing and string length share the same Unicode scalar coordinate system; `s[0..len(s)]` safely selects the entire text.
  - `bytes[a..b]` and `bytes[a..=b]` evaluate to an independent `bytes` byte sub-sequence. For a byte sequence of length $N$, half-open bounds require $0 \le a \le b \le N$; inclusive bounds require $0 \le a \le b < N$.
  - Safe primitive range lookup returns `?str` or `?bytes`, with `None` for invalid bounds.
- **Array Stability**: Structural mutation is `E0526` during iteration or `E0537` before the last possible use of any derived `ref`/observer environment. Nonoverlapping element writes remain allowed.

### Text and Byte Operations

The prelude modules `String` and `Bytes` provide pure, finite, dual-phase operations. Scalar interfaces use `u32`.

| Operation | Result / contract | Complexity |
| :--- | :--- | :--- |
| `String::scalars(text: str) -> new []u32` | New ordinary array of the text's valid scalars, in order | $O(n)$ work and output space |
| `String::at(text: str, index: int) -> ?u32` | Scalar at a scalar-coordinate index; `None` outside bounds | $O(n)$ worst case |
| `String::from_scalars(via values: []u32) -> ?str` | Exact scalar sequence; `None` if any input is not a scalar | $O(n)$ |
| `String::encode_utf8(text: str) -> bytes` | Exact UTF-8 bytes of the scalar sequence | $O(n)$ upper bound |
| `String::decode_utf8(data: bytes) -> ?str` | Exact decoded sequence; `None` for ill-formed UTF-8 | $O(n)$ |
| `Bytes::at(data: bytes, index: int) -> ?u8` | Byte at a byte-coordinate index; `None` outside bounds | $O(1)$ |
| `Bytes::to_array(data: bytes) -> new []u8` | New ordinary array containing the same bytes | $O(n)$ work and output space |
| `Bytes::from_array(via values: []u8) -> bytes` | Independent byte value with the same byte sequence | $O(n)$ upper bound |

Here n counts input array entries for array conversions, scalars for `String::scalars`, and bytes for UTF-8 traversal.

| Text / byte rule | Contract |
| :--- | :--- |
| Unicode scalar | `u32` in `0..=0x10FFFF`, excluding `0xD800..=0xDFFF`; NUL, unassigned code points, and noncharacters are valid |
| Text identity | Exact scalar sequence, including a leading U+FEFF |
| UTF-8 | [Unicode encoding](https://www.unicode.org/versions/Unicode17.0.0/core-spec/chapter-3/); encode/decode preserves valid bytes and scalar sequences |
| Invalid UTF-8 | Malformed/truncated sequences, overlong encodings, surrogates, and values above `0x10FFFF` yield `None` |
| `at` bounds | Negative or out-of-range index yields `None` |
| Array reception | `via` admits immutable reception or explicit `ref` observation; resulting text/bytes are independent value snapshots |
| Array results | Construction reception determines immutable or writable access |
| Text construction | Validate scalars, then apply the [collection extent limit](#collection-extents-and-index-types) |

```ril
let text = "é🙂"
let scalars = String::scalars(text)
assert(scalars == [0xE9u32, 0x1F642u32])
assert(String::at(text, 1) == Some(0x1F642u32))
assert(String::at(text, -1) == None)
assert(String::from_scalars(scalars) == Some(text))
assert(String::from_scalars([0xD800u32]) == None)
let encoded = String::encode_utf8(text)
assert(encoded == bytes"\xC3\xA9\xF0\x9F\x99\x82")
assert(String::decode_utf8(encoded) == Some(text))
assert(String::decode_utf8(bytes"\xC0\xAF") == None) -- Overlong UTF-8
assert(String::decode_utf8(bytes"\xED\xA0\x80") == None) -- Encoded surrogate
assert(String::decode_utf8(bytes"\xEF\xBB\xBF") == Some("\u{FEFF}"))
assert(len("é") == 1 && len("e\u{301}") == 2)
assert("é" != "e\u{301}")             -- Exact scalar equality
assert(text?[1..2] == Some("🙂") && encoded?[0..2] == Some(bytes"\xC3\xA9"))
let mut array = Bytes::to_array(bytes"AB")
array[0] = 0u8
let copied = Bytes::from_array(ref array)
array[0] = 1u8
assert(copied == bytes"\x00B" && Bytes::at(copied, 2) == None)
for String::scalars(text) as scalar { assert(scalar <= 0x10FFFFu32) }
```

### Pipeline Operators

```ril
let doubled = [1, 2, 3]
    |> Array::map(\x -> x * 2)
    |> Array::filter(\x -> x > 2)      -- [4, 6]

let mut raw = Bytes::to_array(bytes"AB")
raw |> mut Array::push(67u8)           -- Array::push(mut raw, 67u8)
assert(raw |> ref Bytes::from_array == bytes"ABC")

let decoded = raw
    |> ref Bytes::from_array           -- Bytes::from_array(ref raw)
    |> String::decode_utf8             -- Some("ABC")
assert(decoded is Some(str["AB", ..]) && raw |> mut Array::pop == Some(67u8))

let last_byte = raw
    |> mut Array::pop
    ?? 0u8                             -- '|>' (Level 10) binds before '??' (Level 14)
assert(last_byte == 66u8)

fn decode_header(ref buf: []u8) -> ?str {
    let text = (buf |> ref Bytes::from_array |> String::decode_utf8)? -- Level-1 '?' wraps pipeline
    Some(text)
}
assert(decode_header(ref raw) == Some("A"))

type Cell = .{ var count: int }
fn step_cell(new c: Cell, delta: int) &mut -> new Cell {
    c.count += delta
    c
}
fn retain_cell(^mut c: Cell) -> ^mut(c) Cell { c }

let mut built = Cell.{ count: 1 }
    |> new step_cell(2)                -- step_cell(new Cell.{ count: 1 }, 2)
    |> new step_cell(3)                -- Chained construction handoff; built.count == 6
let ^mut shared = built |> ^mut retain_cell
shared.count += 1
assert(built.count == 7)

-- 42 |> ref inspect                   -- Error [E0401]: value type cannot pass by 'ref'
-- raw |> Bytes::from_array            -- Error [E0405]: missing 'ref' marker for live buffer
-- clone(raw) |> mut Array::push(1u8)  -- Error [E0410]: 'mut' / '^mut' requires an AssignTarget
-- raw |> mut Array::push(1u8)
--     |> mut Array::push(2u8)         -- Error [E0410]: prior step returns '()', not an AssignTarget
```

| Pipeline form | Desugaring | First-argument requirement & reception |
| :--- | :--- | :--- |
| `x \|> f` / `x \|> f(a)` | `f(x)` / `f(x, a)` | `Expression`: ordinary immutable / value reception (or lexical `via` elaboration) |
| `x \|> ref f` / `x \|> ref f(a)` | `f(ref x)` / `f(ref x, a)` | `Expression`: call-time read-only `ref` observation |
| `x \|> mut f` / `x \|> mut f(a)` | `f(mut x)` / `f(mut x, a)` | `AssignTarget` (`E0410` otherwise): temporary exclusive write |
| `x \|> ^mut f` / `x \|> ^mut f(a)` | `f(^mut x)` / `f(^mut x, a)` | `AssignTarget` (`E0410` otherwise): retained shared write |
| `x \|> new f` / `x \|> new f(a)` | `f(new x)` / `f(new x, a)` | `Expression`: unpublished construction handoff |

| Rule | Semantics |
| :--- | :--- |
| Precedence | Level 10 (left-associative): tighter than `==`/`<`/`is` (Level 11), `&&`/`\|\|` (Levels 12–13), and `??` (Level 14); looser than arithmetic, bitwise, ranges (Levels 3–9), and postfix `.`/`[]`/`?` (Level 1) |
| Mode token | `ref`, `mut`, `^mut`, or `new` immediately following `\|>` always binds as the pipeline `ArgumentMode` |
| Evaluation order | Left operand, right callee, then written right arguments once left-to-right; abrupt exit skips remaining expressions and the call. In `x \|> new f(a)`, preparing `x` ends `x` and derived paths before evaluating `f` or `a` (`E0549` if reused) |
| Trailing closure | Supplies the final argument (`x \|> ref f(a) \y -> e` means `f(ref x, a) \y -> e`) |

### Error and Fallback Operators

```ril
fn find_record(id: int) -> Result<str, str> {
    let user = fetch_user(id)?         -- Early return Err if fetch_user fails
    Ok(user.name)
}
-- let bad_top_record = find_record(1)? -- Error [E0205]: postfix '?' operator used outside function or closure body; no enclosing activation frame to receive early return

let opt: ?int = None
let v1 = opt ?? 100                    -- 100 (Option fallback with default value)
let v2 = opt ?? compute_default()       -- Evaluates compute_default only when opt is None
let optional_action: ?(fn() -> int) = None
let action = optional_action ?? (\-> 7) -- The fallback is a function value, not an invocation
assert(action() == 7)

let res: Result<int, str> = Err("unavailable")
let recovered = res ?? \err -> 0       -- 0: Result fallback must consume the error
-- let bad = res ?? 0                  -- Error [E0711]: Result fallback requires closure '\err -> ...'
-- let illegal = opt ?? return 0       -- Error [E0710]: illegal control transfer inside fallback operator '??'

-- Safe navigation operators '?.' and '?[':
let profile: ?UserProfile = None
let city = profile?.address?.city      -- Evaluates to None (?str) without panicking
let table: ?[]int = None
let first_elem = table?[0]             -- Evaluates to None (?int) without panicking
let arr = [10, 20, 30]
let out_of_bounds = arr?[99]           -- Evaluates to None (?int) (safe array index)
```

| Operator | Success | Failure / constraint |
| :--- | :--- | :--- |
| `Option<T>?` | Unwrap T | Return `None`; enclosing callable must return `Option<U>` (`E0713`) |
| `Result<T, E>?` | Unwrap T | Return `Err(e)`; enclosing result must accept E (`E0713`) |
| `Option<T> ?? rhs` | Unwrap T; skip rhs | Evaluate rhs as T; never implicitly invoke a supplier |
| `Result<T, E> ?? handler` | Unwrap T; skip handler | Evaluate and invoke `fn(E) @& -> T` once, preserving actual obligations and handle modes; raw T is `E0711` |

`?` outside a function/closure is `E0205`, including module initializers. It performs no Option/Result or error conversion; payload provenance, access modes, and nested inspection duties survive.

```ril
fn invalid_operand() -> ?int {
    -- let number = 42?               -- Error [E0712]: operand is neither Option nor Result
    Some(42)
}
fn invalid_target(value: ?int) -> int {
    -- let number = value?            -- Error [E0713]: enclosing callable cannot return None
    value ?? 0
}
fn incompatible_error(value: Result<int, str>) -> Result<int, int> {
    -- let number = value?            -- Error [E0713]: str failure cannot become int
    match value { Ok(number) -> Ok(number), Err(_error) -> Err(0) } -- OK: explicit mapping
}
-- let fallback = 42 ?? 0             -- Error [E0714]: no fallback operation for int
let record = .{ name: "Ada" }
-- let safe_name = record?.name       -- Error [E0715]: '?.' requires an optional receiver
let optional_record: ?.{ name: str } = Some(record)
let safe_name = optional_record?.name -- OK
```

Inside a callable, a postfix `?` operand other than `Option` or `Result` is `E0712`. A valid operand whose failure cannot be returned by the enclosing callable is `E0713`, including an incompatible Result error type. A `??` left operand outside those two families is `E0714`; a raw-value Result fallback retains `E0711`, and incompatible fallback value/callable types use `E0301`. Safe field access on a non-optional receiver is `E0715`; safe element lookup also admits ordinary collections as specified below, and unsupported lookup receivers use `E0352`.

`??` evaluates its left operand once. Callback effects and access modes remain checked. Direct outward `return`/`last`/`next` is `E0710`; a return inside a nested callable stays local to it.

| Safe access | Rule |
| :--- | :--- |
| `?.` | Field projection from an optional receiver |
| `?[` | Array/map element lookup or array/str/bytes range lookup, also through an optional receiver |
| `None` receiver | Return `None`; skip access and index evaluation |
| Missing key / out-of-bounds element | Return `None` |
| Selected U / selected `Option<U>` | `Some(value)` / unchanged Option; no further flattening |
| Range index on a sequence receiver | Use ordinary range indexing syntax and bounds rules; a range-typed map key remains a key |

### Record Construction and Spread Update

```ebnf
RecordExpr      ::= [ TypeReference ] ".{" [ RecordValueField { "," RecordValueField } [ "," ] ] "}"
RecordValueField ::= [ MemberMode ] FieldLabel [ ":" Expression ] | ".." Expression
```

An optional preceding `TypeReference` selects the constructed declaration (`Point.{...}`).

Explicit fields override equally named fields from a value spread, independent of written position. Multiple explicit definitions are `E0210`; conflicting spreads without an override are `E0211`. Spreads preserve member schemas, references, and actual access modes. A typed constructor inherits omitted modes; an untyped explicit field defaults to immutable. Neither spreading nor a written mode upgrades a stored source.

A declared `via` member resolves through the typed receiver's context and canonical reception rules. Untyped fields use their concrete declared modes. An explicit construction operand or its dependent template elaboration may initialize a compatible typed slot after its complete receiving proof, consuming the old path. A `new expression` outside a supported receiving position is `E0548`.

```ril
let left = .{ id: 1 }
let right = .{ id: 2 }
-- let duplicate = .{ id: 1, id: 2 }  -- Error [E0210]: two explicit definitions
-- let conflict = .{ ..left, ..right } -- Error [E0211]: both spreads supply id
let chosen = .{ ..left, ..right, id: 3 } -- OK: explicit override resolves the conflict
let mapping = ["id": 1, "id": 2]     -- OK: duplicate map keys retain the last value
```

```ril
type Point = .{ x: int, y: int, z: int }

let p1 = Point.{ x: 1, y: 2, z: 3 }
let p2 = Point.{ z: 10, ..p1 }         -- Record spread update: .{ x: 1, y: 2, z: 10 }
```

```ril
-- Record field defaults on declared record types:
let DEFAULT_HOST = "127.0.0.1"

type ServerConfig(.{
    host: str = DEFAULT_HOST,
    port: int = 8080,
    var max_conns: int = port * 2,     -- Earlier field 'port' is in scope
})

type RawConfig = .{ timeout_ms: int = 1000, retries: int = 3 }
type Id<T> = T

fn make_server() &up(sub){DEFAULT_HOST} -> ServerConfig {
    ServerConfig.{ port: 9000 }        -- Evaluates omitted 'host' and 'max_conns' (18000)
}
let raw = RawConfig.{}                 -- Direct alias preserves declared defaults
-- let stripped = Id<RawConfig>.{}     -- Error [E0307]: type function yields structural shape without defaults
let kept = Id<ServerConfig>.{ host: "0.0.0.0" } -- OK: nominal identity retains defaults

-- type BadMut = .{ mut items: []int = [] }         -- Error [E0404]: mutable/ref/via field defaults prohibited
-- type BadOrder = .{ a: int = b, b: int = 1 }      -- Error [E0408]: forward reference in field default
-- type BadNested = .{ inner: .{ x: int = 1 } }     -- Error [E0359]: defaults require a root record declaration
```

| Field default rule | Requirement |
| :--- | :--- |
| Placement | Admitted only on plain (`let`) or `var` fields of the root record in a `.ril` `TypeDecl`, `OpaqueTypeDecl`, or `NominalDecl` (`E0404` on `mut`/`^mut`/`ref`/`via`; `E0359` on nested/anonymous records; `E0901` in `.d.ril`) |
| Evaluation & scope | Evaluated left-to-right in field declaration order after explicit and spread fields when omitted at `TypeRef.{...}`; may reference earlier fields of the same record (`E0408` on self/later fields) |
| Purity & state | No outward operational effects or mutable/live state (`E0409`); read-only deeply immutable `.ril` `&up(sub)` / `&up` dependencies propagate to callers that omit the field |
| Type identity | `<RawConfig> == <.{ timeout_ms: int, retries: int }>`; direct lexical alias references in `TypeRef.{...}` preserve defaults, while type tokens (`Type<T>`) and computed type functions carry pure structural shapes without transparent-alias defaults; `NominalDecl` and `OpaqueTypeDecl` retain defaults through their declaration identity |

### Assignments and Compound Assignments

```ebnf
AssignmentExpr  ::= AssignTarget AssignmentOperator Expression
AssignTarget    ::= QualifiedName | Expression "." ( FieldLabel | TupleIndex | "(" Expression ")" )
                  | Expression "[" Expression "]"
AssignmentOperator ::= "=" | "+=" | "-=" | "*=" | "/=" | "%="
                     | "&=" | "|=" | "^=" | "<<=" | ">>="
```

Assignments require an assignable location with the slot-replacement or interior-write authority required by that target. They evaluate to `()`.

```ril
-- (1 + 2) = 3                       -- Error [E0503]: expression is not an assignable location
let fixed = 1
-- fixed = 2                         -- Error [E0501]: location exists but binding is immutable
var changing = 1
changing = 2                         -- OK
```

A non-addressable assignment target is `E0503`. Insufficient reassignment or interior authority uses `E0501`, `E0502`, or `E0520`; missing members and invalid indexing use their specific diagnostics. Chained assignment is `E0701`.

Qualified names and static computed fields keep ordinary lvalue access modes. Compound assignment evaluates the location once, then reads, evaluates the RHS, and writes.

```ril
var x = 10
x = 20                                 -- Simple assignment
x += 5                                 -- Compound addition (25)
x -= 2                                 -- Compound subtraction (23)
x *= 2                                 -- Compound multiplication (46)
x /= 2                                 -- Compound division (23)
x %= 5                                 -- Compound remainder (3)

-- Fixed-width modular compound arithmetic:
var byte_val: u8 = 250u8
byte_val += 10u8                       -- 4u8 (two's-complement wrap)
byte_val -= 10u8                       -- 250u8
byte_val *= 2u8                        -- 244u8

-- Compound bitwise assignments:
var flags = 0b0011
flags |= 0b1100                        -- 0b1111
flags &= 0b1010                        -- 0b1010
flags ^= 0b0011                        -- 0b1001
flags <<= 1u32                         -- 0b10010
flags >>= 2u32                         -- 0b00100

-- Pinned handles (let mut) permit field assignment but reject handle reassignment:
type Buffer = .{ var capacity: int }
let mut pinned_buf = Buffer.{ capacity: 16 }
pinned_buf.capacity = 32               -- OK: field assignment through pinned handle
pinned_buf.("capacity") += 1           -- OK: same field access mode
-- pinned_buf = Buffer.{ capacity: 64 } -- Error [E0502]: use 'var mut' when reassignment and interior writes are both needed

-- Chained assignment is prohibited:
-- x = y = 10                          -- Error [E0701]: assignment chaining is prohibited
```

---

## Control Flow and Pattern Matching

### Block Expressions, Tail Values, and Hoisted Declarations

A block `{ ... }` evaluates to its tail expression. A block may conclude with a trailing `where` clause (`BlockWhereClause`) declaring mutually recursive helper functions (`fn`), local types (`type`), and local algebraic effects (`eff`). All items in `BlockWhereClause` are visible throughout the enclosing block scope.

```ebnf
Block               ::= "{" [ StatementSequence ] [ BlockWhereClause ] "}"
StatementSequence   ::= Statement { Separator Statement } [ Separator ]
Statement           ::= LetDecl
                      | LetMutDecl
                      | SharedMutDecl
                      | VarDecl
                      | VarMutDecl
                      | VarRefDecl
                      | ScopedDecl
                      | LetRefDecl
                      | WithStatement
                      | UseDecl
                      | MetaLetDecl
                      | ControlTransfer
                      | AssignmentExpr
                      | Expression
BlockWhereClause    ::= "where" BlockWhereItem { Separator BlockWhereItem } [ Separator ]
BlockWhereItem      ::= FunctionDecl | LocalTypeDecl | EffectDecl | MetaFnDecl
Separator       ::= ";" | Newline
```

#### Block Expressions and Scope Invariants

- **Declarative Partitioning (`E0703`, `E0702`)**:
   - Declarations (`fn`, `type`, `eff`) must not appear in `StatementSequence` (`E0703`).
   - Variable bindings (`let`, `let mut`, `var`) must not appear in `where` clauses (`E0702`).
- **Local Effect Discharge (`E0618`)**:
   - Any local `eff` declared in `BlockWhereClause` must be completely discharged via an in-scope `with` handler within the enclosing block frame.
   - Local effects must not appear in outer `@Effect` annotations or escape into unhandled closures.
- **Local Nominal Confinement (`E0315`)**:
   - Returned value/callable types cannot contain function-local nominal, opaque, or sum identities, including signature-`where` identities. Expand structural aliases first. Signature references to block-`where` types fail scope checking (`E0706`) before this check.

```ril
fn read_after_init() -> int {
    -- read_value()                    -- Error [E0207]: value is not initialized
    let value = 1
    read_value()                       -- OK
where
    fn read_value() &up{value} -> int { value }
}
```

Local bindings become available after initialization. Hoisted helpers may capture later bindings, but invocation, publication, and passing to another call require every capture initialized (`E0207`). Hoisting executes neither initializers nor helpers.

```ril
-- Mutually recursive functions and types hoisted in block 'where':
let total = {
    let base = compute_base()
    let parity = is_even(base)
    base
where
    fn compute_base() -> int { 100 }
    fn is_even(n: int) -> bool { if n <= 0 { true } else { is_odd(n - 1) } }
    fn is_odd(n: int) -> bool { if n <= 0 { false } else { is_even(n - 1) } }
}

-- Local algebraic effect declared in 'where' and fully discharged locally:
fn search_matrix(grid: [][]int) -> ?int {
    var found: ?int = None
    with Search::hit(val) -> {
        found = Some(val)
        return found                   -- Delimited early return; discharges Search
    }

    walk_grid(grid)
    found                              -- Pure signature: @Search completely discharged
where
    eff Search { hit(int) -> () }
    fn walk_grid(g: [][]int) @Search -> () {
        for g as row {
            for row as item {
                if item > 0 { Search::hit(item) }
            }
        }
    }
}

-- Prohibited: Declarations inside sequential statement stream (E0703):
-- let bad_statement = {
--     let x = 10
--     type Step = int                 -- Error [E0703]: declarations of 'type' are prohibited in sequential statement stream; place in 'where' clause
--     eff Bail { exit() -> never }    -- Error [E0703]: declarations of 'eff' are prohibited in sequential statement stream; place in 'where' clause
--     x + 1
-- }

-- Prohibited: Variable bindings declared in 'where' (E0702):
-- let bad_where = {
--     base + 1
-- where
--     let base = 10                   -- Error [E0702]: variable bindings cannot be declared in 'where' clause
-- }

-- Prohibited: Undischarged local effect escaping block boundary (E0618):
-- fn bad_effect_leak() @LocalStep -> int { -- Error [E0618]: local effect 'LocalStep' cannot escape enclosing block to function signature
--     LocalStep::tick()
--     1
-- where
--     eff LocalStep { tick() -> () }
-- }

-- Prohibited: Local nominal type escaping function boundary (E0315):
-- fn bad_nominal_leak() -> Token
-- where
--     type Token(int)
-- { Token(42) }                       -- Error [E0315]: signature-local nominal identity escapes
```

### Conditional Expressions

```ebnf
IfExpr          ::= "if" ( Expression | "let" Pattern "=" Expression ) Block [ "else" ( Block | IfExpr ) ]
```

`if` evaluates a single boolean condition or a single refutable `if let` pattern binding (`E0350`). Pattern binders are scoped strictly to the then block (`E0204` outside). Branches must have compatible types (`E0351`); a `never` branch imposes no returned-value constraint. An `if` without an `else` evaluates to `()` and requires its then branch to have type `()` or `never` (`E0301` otherwise).

```ril
-- let value = if 1 { 10 } else { 20 } -- Error [E0350]: condition must be bool
let value = if true { 10 } else { panic("stopped") } -- OK: never does not conflict with int
```

```ril
let max = if a > b { a } else { b }

if logging_enabled {
    println("log message")             -- Evaluates to ()
}

let user_opt: ?User = Some(User.{ id: 1, name: "Ada" })
let display = if let Some(u) = user_opt {
    u.name                             -- OK: 'u' bound within then block
} else {
    "Anonymous"                        -- 'u' is not bound here
}
assert(display == "Ada")
-- let outside = u                     -- Error [E0204]: unresolved identifier 'u'

let avatar = if let Some(u) = fetch_cached_user(1)? {
    u.name                             -- OK: propagates error via '?' or falls back on None
} else {
    "Anonymous"
}

-- Incompatible branch types are statically rejected:
-- let bad = if true { 10 } else { "error" } -- Error [E0351]: if-else branches have incompatible types: expected 'int', found 'str'
```

### Loop Expressions

```ebnf
LoopExpr  ::= "loop" Block
WhileExpr ::= "while" ( Expression | "let" Pattern "=" Expression ) Block
ForExpr   ::= "for" Expression "as" Pattern Block
```

`while` evaluates a single boolean condition or a single refutable `while let` pattern binding (`E0350`). Failure terminates the loop.

```ril
-- 'loop' with 'last' yielding a value:
var i = 0
let found = loop {
    i += 1
    if i == 5 { next }                 -- OK: skips to next iteration via 'next'
    if i == 10 { last i * 2 }          -- Loop evaluates to 20 via 'last'
}

-- 'while' loop with boolean condition:
while i > 0 {
    i -= 1
}

-- 'while let' matching refutable patterns:
let mut queue: []int = [1, 2, 3]
var total = 0
while let Some(item) = Array::pop(mut queue) {
    total += item                      -- OK: 'item' bound in body
}
assert(total == 6)

while let Some(work) = active(runtime)? {
    process(work)                      -- OK: propagates error via '?' or terminates on None
}

-- 'for' loop over ranges and collections:
var sum = 0
for 1..=5 as x {
    if x % 2 == 0 { next }             -- 'next' skips even numbers
    sum += x
}
assert(sum == 9)                       -- 1 + 3 + 5
```

| Loop | Type / constraint |
| :--- | :--- |
| `while` | Boolean condition (`E0350`) or `while let` pattern binding; result and `last` values are unit (`E0301`) |
| `for` | Result and `last` values are unit (`E0301`); element pattern irrefutable (`E0345`), never an implicit filter |
| `loop` | Common type of reachable `last` values, or `never` if none |

Body tails are discarded subject to Result inspection duties.

```ril
var total = 0
for ["b": 2, "a": 1] as (key, value) {
    assert(key == "b" || key == "a")
    total += value
}
assert(total == 3)
-- for "ab" as scalar {}               -- Error [E0355]: use String::scalars explicitly
```

| Built-in / generator source | Element and traversal order |
| :--- | :--- |
| `[]T` | T, increasing element index |
| `[K: V]` | (K, V), first-insertion order |
| `Set<T>` | T, first-insertion order |
| Integer range | Endpoint type, ascending bounds as specified for ranges |
| `()` or `never` expression with residual `@Yield<T>` | T, delimited generator stream handled locally per iteration |
| Other values, including strings, bytes, and iterator Source records | No implicit iteration (`E0355`); use explicit conversion or operations |

Evaluate a collection or range source once and read each entry when visited; later element replacement may be observed. Structural mutation during traversal is `E0526`. Under [pattern reception](#pattern-reception-and-decomposition), value elements copy and shared-object elements receive bounded access from the source/member schema. Borrowed writes are temporary; retention requires source authority and lifetime proofs. Explicit `ref` requests permitted observation. Missing write authority is `E0521`; independent value-type `var` copies are permitted. Construction handoff is separate from traversal.

```ril
fn evens_up_to(limit: int) @Yield<int> -> () {
    for 0..=limit as n {
        if n % 2 == 0 { Yield::emit(n) }
    }
}

var total = 0
for evens_up_to(8) as n {
    if n > 6 { last }                      -- Aborts stream without resuming; unwinds producer scoped bindings
    total += n
}
assert(total == 12)                        -- 0 + 2 + 4 + 6
```

| Generator `for` rule | Behavior |
| :--- | :--- |
| Activation | Source of type `()` or `never` with a unique concrete residual `@Yield<T>` installs an implicit inner delimited `Yield<T>::emit` handler |
| Iteration & early exit | Each `emit(v)` binds `Pattern`, runs the body, and closes body-local `scoped` bindings before `resume ()`; `last`, `return`, or `?` drops the continuation without resuming and unwinds active producer `scoped` bindings (`E0623` on outer `resume` across the loop) |
| `diverge_budget` charge | `1` unit on implicit `Yield::emit` entry + `1` unit on `resume ()` (normal step completion or `next`); early exit or unwinding skips `resume` and its charge |

### Control Transfers

Control transfers alter sequential evaluation order. Ril supports lexical control transfers (`last`, `next`, `return`) strictly scoped to the innermost enclosing loop or function. Loop labels are not part of the language.

```ebnf
ControlTransfer ::= ( "last" [ Expression ] )
                  | "next"
                  | ( "return" [ Expression ] )
```

```ril
-- 'last' terminates innermost loop (bare 'last' or 'last expr'):
var total = 0
for 1..=100 as n {
    if n > 10 { last }                 -- Bare 'last': terminates loop without value
    total += n
}
assert(total == 55)

var counter = 0
let reached = loop {
    counter += 1
    if counter == 5 { last counter * 10 } -- 'last expr': loop evaluates to 50
}
assert(reached == 50)

-- 'next' advances innermost loop to next iteration:
var odd_sum = 0
for 1..=6 as n {
    if n % 2 == 0 { next }             -- Skips even iterations
    odd_sum += n
}
assert(odd_sum == 9)

-- Function early return (bare 'return' or 'return expr'):
fn log_positive(val: int) @Fiber -> () {
    if val <= 0 { return }             -- Bare 'return': early exit from unit function
    println("positive: {val}")
}

fn search(matrix: [][]int, target: int) -> bool {
    for matrix as row {
        for row as cell {
            if cell == target { return true } -- 'return expr': early return with value
        }
    }
    false
}

-- Rejection of Invalid Control Transfer (E0707):
-- last 42                                  -- Error [E0707]: 'last' statement used outside loop body
-- next                                     -- Error [E0707]: 'next' statement used outside loop body
```

### Guarded Bindings and Non-Vacuous Invariant

`let Pattern = expr else { Block }` continues with the pattern bindings on success and evaluates the `else` block on failure. The failure block cannot complete normally.

```ril
fn unwrap_or_zero(value: ?int) -> int {
    -- let Some(x) = value             -- Error [E0345]: refutable binding needs else
    let Some(x) = value else { return 0 }
    x
}
```

Without `else`, patterns must be irrefutable under the initializer's static type/refinement (`E0345`), including mutable/destructuring bindings. A single-variant constructor may qualify. Guarded names exist after success, not in the failure block.

- **Non-Completing Failure Branch (`E0321`)**: The `else` block must have type `never`. It may transfer control, panic, or run indefinitely; `never` alone establishes no termination judgment.
- **Non-Vacuous Binding (`E0309`)**: Every ordinary or guarded `let` must bind a variable, except unguarded `let _ = expr`. Nullary patterns, unit patterns, and guarded wildcard discards are rejected. Binding-free tests use `?`, `is`, or `match`.

```ril
fn process_account(data: [str: str]) -> Result<str, str> {
    -- The pattern must bind at least one variable; the else block must have type never:
    let Some(id) = data?["account_id"] else {
        return Err("missing account_id") -- OK: returns from the function; id is bound only on success
    }
    let Some(user) = fetch_user(id)? else {
        return Err("missing user")     -- OK: '?' propagates fetch errors; None takes the explicit return
    }

    -- An else branch that completes normally is statically rejected:
    -- let Some(name) = data?["name"] else {
    --     println("name missing")     -- Error [E0321]: else branch of let ... else must have type never
    -- }

    -- Prohibited: Vacuous guarded binding without variable bindings:
    -- let Ok() = save_profile(id) else {
    --     return Err("save failed")   -- Error [E0309]: 'let ... else' pattern must bind at least one variable; use postfix '?' or 'if expr is ...' instead
    -- }

    -- Compliant Alternative 1: Postfix '?'
    save_profile(id)?

    -- Compliant Alternative 2: Boolean pattern test 'is'
    -- if !(save_profile(id) is Ok()) { return Err("save failed") }

    Ok(id)
}

-- Failure branches transferring control with next and last:
for records as entry {
    let Ok(val) = parse_entry(entry) else {
        next                           -- OK: starts the next iteration; val is bound only on success
    }
    process(val)
}

loop {
    let Some(work) = active(runtime)? else {
        last                           -- OK: '?' propagates errors; None exits the loop with last
    }
    process(work)
}

-- Guarded binding with tuple destructuring (Constructor-Tuple Equivalence):
fn verify_session(cookie: str) -> Result<str, str> {
    let Ok(user_id, token) = authenticate(cookie) else {
        return Err("unauthorized")     -- OK: positional tuple unwrap (n = 2), binds 'user_id' and 'token'
    }
    Ok(user_id)
}
```

### Pattern Matching

```ebnf
MatchExpr     ::= "match" Expression "{" [ MatchArm { "," MatchArm } [ "," ] ] "}"
MatchArm      ::= Pattern [ "if" Expression ] "->" Expression
Pattern       ::= OrPattern
OrPattern     ::= SinglePattern { "|" SinglePattern }
SinglePattern      ::= LiteralPattern | VariablePattern | WildcardPattern
                     | TuplePattern | ArrayPattern | BytesPattern | StrPattern
                     | RecordPattern | ConstructorPattern | RangePattern | TypePattern
BindingModifier    ::= MemberMode
VariablePattern    ::= [ BindingModifier ] Identifier
ConstructorPattern ::= QualifiedName [ "(" [ PatternList ] ")" ]
PatternList        ::= Pattern { "," Pattern } [ "," ]
TuplePattern       ::= "(" [ TuplePatternElement { "," TuplePatternElement } [ "," ] ] ")"
TuplePatternElement ::= Pattern | ".."
ArrayPattern       ::= "[" [ ArrayPatternElement { "," ArrayPatternElement } [ "," ] ] "]"
ArrayPatternElement ::= Pattern | ".." [ Identifier ]
BytesPattern       ::= "bytes" "[" [ BytesPatternElement { "," BytesPatternElement } [ "," ] ] "]"
BytesPatternElement ::= ByteStringLiteral | RangePattern | NumericPattern | WildcardPattern | Identifier | ".." [ Identifier ]
StrPattern         ::= "str" "[" [ StrPatternElement { "," StrPatternElement } [ "," ] ] "]"
StrPatternElement  ::= StringLiteral | RawStringLiteral | ".." [ Identifier ]
RecordPattern      ::= [ TypeReference ] ".{" [ RecordPatternField { "," RecordPatternField } [ "," ] ] "}"
RecordPatternField ::= [ BindingModifier ] FieldLabel [ ":" Pattern ] | ".." [ Identifier ]
NumericPattern  ::= [ "-" ] ( IntLiteral | FloatLiteral )
LiteralPattern  ::= Literal | NumericPattern
WildcardPattern ::= "_"
RangePattern    ::= NumericPattern ( ".." | "..=" ) NumericPattern
```

Matches are evaluated top-to-bottom and must be exhaustive (`E0303`). A trailing guard belongs to the whole or-pattern, not just its last alternative. Every alternative binds the same identifiers with compatible committed receiver types and modes (`E0346`), not merely compatible read-only previews; within one alternative each identifier is bound at most once (`E0347`). Each tuple, array or record pattern permits at most one immediate rest (`E0347`); nested patterns count their rests independently. Thus `([a, ..xs], [b, ..ys])` is valid. A guard cannot establish exhaustiveness. Pattern/subject incompatibility uses `E0301`; incompatible result types across otherwise valid reachable arms use `E0351`.

These binding patterns govern `match`, bindings, `if let` / `while let`, iteration, and handler parameters. The enclosing operation supplies each unmodified receiver's slot and access modes under [pattern reception](#pattern-reception-and-decomposition). Ordinary `let`/`var` receivers default to immutable access. The nonbinding [`is` value tests](#value-tests-with-is) have their own grammar and admit expected-value expressions.

`TypePattern` is admitted only in static `match` arms against token subjects/constituents (`E0306` for another pattern context). Run-time token subjects are `E0816`.

A tuple or array pattern without a rest requires exactly its written number of elements. With a rest, its subject must contain at least the number of non-rest elements; prefix and suffix patterns select from their corresponding ends, and the rest may be empty. Tuple rests are anonymous. Named array rests use the range-indexing copy rules and ordinary array extent, access-mode, publication, and sharing checks.

| Sequence pattern | Rule |
| :--- | :--- |
| `bytes[...]` | Subject must be `bytes` (`E0301` otherwise). Elements match single `u8` literals/ranges/`_`/`u8` value bindings or `ByteStringLiteral` chunks; at most one `..` / `..rest` (`E0347` if repeated) binds the remaining slice as `bytes` (`E0402` if a reference/mutable modifier is written) |
| `str[...]` | Subject must be `str` (`E0301` otherwise). Elements match non-interpolated `StringLiteral` / `RawStringLiteral` UTF-8 prefix chunks plus at most one trailing `..` / `..rest` binding `str` (`E0349` for interpolated chunks or non-trailing `..`; `E0347` if `..` repeated) |

```ril
let mut values = [1, 2, 3]
let ref observed = values
let [_, ..tail] = observed             -- New ordinary array; value elements copied
values[1] = 9
values |> mut Array::push(4)
assert(tail == [2, 3])                 -- Independent slots and length
-- let ref [_, ..bad] = values       -- Error [E0543]: the named rest allocates a new array
```

```ril
type Choice { Left(int), Right(int) }
fn invalid_alternative(value: Choice) -> int {
    -- match value { Left(x) | Right(y) -> 0 } -- Error [E0346]: different binding names
    match value { Left(x) | Right(x) -> x }    -- OK: same binding type and mode
}
-- let (same, same) = (1, 2)          -- Error [E0347]: duplicate binder in one pattern
let (first, second) = (1, 2)           -- OK

-- Tuple pattern with ellipsis ('..'):
let tuple_val = (10, 20, 30, 40, 50)
let (first, .., final) = tuple_val             -- OK: first = 10, final = 50
let (head, ..) = tuple_val                     -- OK: head = 10; trailing elements discarded
-- let (a, .., b, ..) = tuple_val             -- Error [E0347]: at most one '..' permitted in a tuple pattern

-- Array pattern matching:
let numbers: []int = [1, 2, 3, 4, 5]
let [x, y, z] = numbers[0..3]                  -- OK: matching 3-element new array
let desc = match numbers {
    [] -> "empty",
    [single] -> "one element",
    [first, ..rest] -> "head and tail",        -- 'first' = 1, 'rest' = [2, 3, 4, 5]
}
if let [prefix, .., suffix] = numbers {
    assert(prefix == 1 && suffix == 5)         -- OK: front and back extraction with middle discarded
}

-- Byte-sequence and string-prefix destructuring:
let frame = bytes"\x89PNG\r\n\x1a\n\x01payload"
let (ver, body) = match frame {
    bytes[0x89u8, bytes"PNG\r\n\x1a\n", v, ..rest] -> (v, rest),
    bytes[0x41u8..=0x5Au8, ..] -> (0u8, bytes""),
    _ -> (0u8, bytes""),
}
assert(ver == 1u8 && body == bytes"payload")
-- match frame { bytes[..a, ..b] -> () }       -- Error [E0347]: at most one '..' permitted

let url = "https://ril.dev/spec"
let route = match url {
    str["https://", ..rest] | str["http://", ..rest] -> rest,
    str[`\\?\`, ..win_path] -> win_path,
    _ -> url,
}
assert(route == "ril.dev/spec")
-- match url { str["{url}", ..rest] -> rest }  -- Error [E0349]: interpolation prohibited in pattern
-- match url { str[..stem, ".ril"] -> stem }   -- Error [E0349]: 'str[...]' rest must be trailing
fn invalid_range(value: int) -> int {
    match value {
        -- 5..=1 -> 1,               -- Error [E0348]: reversed pattern bounds
        -- (1 + 2) -> 1,             -- Error [E0349]: computed expression is not a literal pattern
        _ -> 0,
    }
}
fn incompatible_arms(value: bool) -> int {
    -- match value { true -> 1, false -> "no" } -- Error [E0351]: arm result types disagree
    match value { true -> 1, false -> 0 }       -- OK
}
```

`E0345` applies when a binding, `for` element pattern, or handler parameter requires an irrefutable pattern but the pattern may fail. A nonexhaustive `match` uses `E0303`. Identifier uniqueness is checked within each or-pattern alternative.

```ril
type Shape {
    Circle(f64),
    Rect(f64, f64),
    Point,
}

fn area(s: Shape) -> f64 {
    match s {
        Circle(r) -> 3.14159 * r * r,
        Rect(w, h) -> w * h,
        Point -> 0.0,
    }
}

-- Non-exhaustive match is statically rejected:
-- fn bad_area(s: Shape) -> f64 {
--     match s {
--         Circle(r) -> 3.14159 * r * r,
--         Rect(w, h) -> w * h,
--     }                               -- Error [E0303]: non-exhaustive match expression, missing variant 'Point'
-- }
```

Numeric patterns use the scrutinee's numeric type and the same representability rules as numeric expressions. Range patterns require integer endpoints of that type with `lower <= upper`; an equal-bound closed range matches one value and an equal-bound half-open range matches none. Empty ranges follow ordinary coverage/reachability rules. Arbitrary computed expressions are not literal patterns (`E0349`); a non-integer or reversed range pattern is `E0348`.

### Pattern Syntax, Or-Patterns, and Exhaustiveness

```ril
-- Or-patterns ('|') and pattern guards:
match status_code {
    200 | 201 | 204 -> "Success",
    400 | 401 | 404 -> "Client Error",
    500 | 502 | 503 -> "Server Error",
    _ -> "Unknown Code",
}

-- Or-patterns with variable bindings:
fn get_size(s: Shape) -> f64 {
    match s {
        Circle(sz) | Rect(sz, _) if sz > 0.0 -> sz,
        _ -> 0.0,
    }
}

-- Guards cannot prove exhaustiveness; fallback required:
-- fn bad_guard(n: int) -> str {
--     match n {
--         x if x >= 0 -> "positive",
--         x if x < 0  -> "negative",
--     }                               -- Error [E0303]: non-exhaustive match: pattern guards do not prove coverage of all inputs
-- }

-- Nonbinding value tests and short-circuit narrowing:
let is_origin = s is Shape::Point
let is_large_circle = s is Shape::Circle && s.0 > 100.0

-- Constructor and tuple pattern destructuring (Constructor-Tuple Equivalence):
let result_pair: Result<(int, str), str> = Ok(200, "OK")
match result_pair {
    Ok(code, msg) -> println(msg),       -- OK: positional tuple unpack (n = 2)
    -- Ok(p) -> println(p.1),            -- Error [E0304]: preceding arm covers every Ok
    -- Ok((code, msg)) -> println(msg),  -- Error [E0304]: equivalent pattern is unreachable here
    -- Ok(a, b, c) -> println(a),        -- Error [E0314]: arity mismatch: variant 'Ok' payload expects 2 elements of type (int, str), found 3
    Err(err) -> println(err),
}

-- Unit payload constructor pattern (Result<(), str>):
let unit_res: Result<(), str> = Ok()
match unit_res {
    Ok() -> println("success"),          -- OK: matches () unit payload
    Err(e) -> println(e),
}
```

### Pattern Reception and Decomposition

```ril
fn transfer_all<T>(via src: [via]T, mut dst: [via]T) &mut -> () {
    while let Some(item) = Array::pop(src) {
        dst |> mut Array::push(item)
    }
}
fn push_option<T>(mut dst: [via]T, via pending: ?T) &mut -> () {
    match pending {
        Some(item) -> dst |> mut Array::push(item),
        None -> (),
    }
}
fn each_read<T>(ref xs: [via]T, via action: fn(via T) @& -> ()) -> () {
    for xs as item { action(item) }
}
```

```ril
type Cell = .{ var count: int }
let mut src: [mut]Cell = [Cell.{ count: 1 }]
let mut dst: [mut]Cell = []
let mut pending = Array::pop(mut src)

{
    let ref observed = pending              -- Observe through an ordinary ref binding
    match observed {
        Some(item) -> assert(item.count == 1),
        None -> (),
    }
}                                           -- Observation ends; pending stays active
match pending {                             -- Consume this qualified construction source
    Some(item) if item.count > 0 -> dst |> mut Array::push(new item),
    _ -> (),                                -- None/wildcard consumes the carrier too
}
-- match pending { ... }                    -- Error [E0549]

fn inspect(ref pending: ?Cell) -> int {
    match pending { Some(item) -> item.count, None -> 0 } -- Borrow; no new path
}
```

Choose the subject decomposition mode statically from current access and established qualification before checking arms. It must hold for every retained alternative; preserve variant-guarded payload relations.

| Input | Subject decomposition |
| :--- | :--- |
| Active qualified construction temporary/formal/local | Consume after arm selection; prove root privacy and [`Movable`](#task-handles-movable-guard-and-combinators) graph eligibility |
| Immutable shared object / value type | Share immutable data / copy values |
| Borrowed `ref`/`mut` / retained writer | Bounded observation/temporary write/shared access; no new construction path |

A direct construction/`new` result requires a consuming-reception proof. For observation, match an ordinary `ref` binding or parameter under its origin and lifetime rules. An independent construction result first needs a lawful concrete receiver with its required acknowledgment; derived observations must end before a later construction handoff.

| Pattern context | Unmodified receiver |
| :--- | :--- |
| `let`/`var`, including `let`-`else`/destructuring | Declared access; plain receivers stay immutable/value. Copy selected value-type constituents and rest results without publishing an unbound parent |
| `match` / `if let` / `while let` | Selected subject decomposition |
| `for` | Borrow/project the visited element; a fresh container or `mut` element never implies detach |
| Handler | Declared operation mode and required binder spelling; only ordinary, `ref`, `mut`, and `^mut` inputs |
| Static `TypePattern` | Static-token and placement rules |

Matching/traversal sub-bindings are fixed by default; declarations retain their slot syntax. Access is bounded by parents, member schemas, origins, and lifetimes. Explicit access requests only permitted reception/degradation; `var` controls rebinding alone and cannot rebind construction paths. Borrowed `mut` never becomes retained sharing/`new`. Shared acknowledgment and ordinary type/use checks remain; inherited access supplies no writable-use evidence or independent written mutable declaration.

Implicit later argument markers require lexically bound mode/callback dependencies. Concrete callers spell `ref`/`^mut`/`new` under the [template forwarding rules](#preserving-reception-and-forwarding).

```ril
-- Given a separate active private pending from a checked pop:
-- match pending {
--     Some(item) if { dst |> mut Array::push(new item); false } -> (),
--     _ -> (),
-- } -- Error [E0551]: guard cannot transfer the prospective payload

-- match 1 {
--     var n if { n = 2; true } -> { n += 1; n },
--     _ -> 0,
-- } -- Rejected: even var has a fixed preview; rebinding starts in the body
```

Run-time match/conditional matching uses these stages; static token matches and handler binders retain their own rules:

1. Evaluate the subject once; test candidates top-to-bottom. Prepare required selections and real rest copies once per attempt, in ordinary pattern order. Reuse successful prepared values; no repeated allocation/evaluation or hidden run-time views.
2. Give the pattern/guard fixed observation views and independent value copies. `var`/`mut`/`^mut` applies only after selection. Keep observation constraints through guard cleanup: no write, consumption/publication of prospective writable paths, or escaping live preview, including through the original subject, captures, module bindings, or handlers. Prove unrelated writes independent; proven immutable sharing and value copies remain lawful.
3. After successful selection and cleanup, end preview views; statically recheck qualification/privacy/partition, then commit. For construction input, end the whole carrier and derived accesses before establishing real receivers from the prepared values; `None`/wildcard arms consume that carrier too.
4. False guards, failed conditional patterns, or abrupt preview do not commit the subject. Unrelated effects, transfers, allocations, and charges are not rolled back. `if let`/`while let` commits only on success; failure leaves a named subject active, while discarded temporaries follow ordinary completion. Track joins and loop backedges (`E0549`); failure after commit never restores paths.

Every `new` payload region separately needs complete eligibility and separation from surviving siblings/external observers, writers, environments, and dependencies. Immutable/`ref`/shared payloads keep their access modes and origins without `new`-input isolation. Preserve legal aliases/cycles and immutable sharing; distinct names/roots prove no partition. Array/row rests keep their copy rules and count as surviving receivers.

`E0551` covers invalid construction decomposition and provisional-path consumption/escape; specific type/authority/exclusivity conditions use their own diagnostics. Matching follows structural/tag/literal selection, exhaustiveness, live refinement, `Result` inspection, and resource/task/cleanup rules. Path consumption ends static access; tags, copies, and other specified data operations execute normally. `is` performs observation only.

### Flow-Sensitive Type Narrowing

Flow-sensitive type narrowing refines the static type of existing bindings in-place across conditional branches, guard clauses, and loops without introducing new variable bindings.

```ebnf
NarrowingTarget    ::= Identifier | NarrowingFieldPath
NarrowingFieldPath ::= Identifier { "." FieldLabel }
NarrowingOp        ::= "is" | "==" | "!="
NarrowingPredicate ::= NarrowingTarget "is" IsTest
                     | NarrowingTarget "!=" "None"
                     | NarrowingTarget "==" "None"
                     | NarrowingTarget "==" Literal
                     | NarrowingTarget "!=" Literal
NarrowingExpr      ::= NarrowingPredicate
                     | "!" NarrowingExpr
                     | NarrowingExpr "&&" Expression
                     | NarrowingExpr "||" Expression
```

#### Flow-Sensitive Type Narrowing Rules and Invariants

- **Environment Splitting**: Predicate $P$ splits context $\Gamma$ into true/false environments: $\Gamma \vdash P \rightsquigarrow (\Gamma_t, \Gamma_f)$.
- **Zero-Binding Refinement**: Narrowing refines existing bindings in-place across conditional branches.
- **Non-Binding Predicates**: `x is Variant(expected)` reads an existing expected value; an unresolved name is `E0204`. Use `match` or guarded bindings to introduce payload variables. `is` has no trailing guard.
- **Value-Test Refinement**: A successful constructor test refines the tested stable path to that variant. Failure excludes the variant only when the payload test covers every payload (for example, a bare tag or all wildcards); a failed value comparison alone excludes no variant. Alternatives join their proven facts. Expected-expression writes invalidate affected facts (`E0310`, or `E0533` for unproved independence); completing the test does not restore them.
- **Payload Projection ($S|_V$)**: Testing `x is V` refines sum type $S$ to variant $S|_V$ ([Sum Types and GADTs](#sum-types-and-gadts)):
   - Payload-free tag. Value projection raises `E0337`.
   - Zero-element positional payload. Unit `()` has no positional components.
   - Single declared payload member. Project via `.0` (`p.0`). `?T != None` directly unboxes to `T`.
   - $n \ge 2$: Projected via positional tuple indices `.0`, `.1`, ..., `.(n-1)`.
   - Record: Projected via declared field names (`x.field`).
- **Stability & Invalidation**:
   - `let`: Permanently narrowed across dominance region.
   - `var` / `var mut`: Slot assignment, including compound assignment, invalidates that slot's narrowing (`E0310`). Interior writes through `var mut`, including `mut` argument calls (`f(mut x)` / `x |> mut f`), invalidate overlapping facts according to their actual write origins without reassigning the slot.
   - `let mut`: Tag identity is pinned (`E0502`); writes through `var` or writable members invalidate overlapping facts.
- **Transitive Latent Havoc**: Invoking a callable whose effective writes reach `v`, through a module or captured group, a named-function state reference, a callback, or an active handler, resets the affected refinement to $T_{\text{root}}$. Group spelling does not change the actual write origin.
- **Anti-Aliasing (`E0533`)**: Preserving a live-origin refinement across a call requires proof that the call's possible writes are independent of that origin. Unknown overlap uses `E0533`; a known write invalidating an established refinement uses `E0310`. A `ref` does not supply independence. The examples below contrast both failures with an immutable snapshot.
- **Generic Confinement**:
   - Testing bare type parameters (`x is T`) is rejected (`E0301`).
   - GADT matching introduces [arm-local equality evidence](#pattern-evidence-and-gadt-branches). That evidence may check any value or expected type involving the same rigid parameter within the current arm; it does not rebind the parameter declaration or become an assumption outside that arm. Path/tag narrowing still applies only to the tested path.
   - Mutable fields preserve container invariance ([Type Identity and Subtyping](#type-identity-and-subtyping)).
- **Dead Paths & Phase Ordering**:
   - A `never` branch contributes no normal-successor environment ($\Gamma \sqcup \bot = \Gamma$); effects, state access, and authority uses already executed before its termination remain in the invocation summary.
   - A narrowing predicate contradictory to an already active refinement is `E0311`. An ordinary constant-false condition is instead an inactive branch; it does not by itself produce this diagnostic.
   - Static dead-path pruning precedes [reachable authority-use analysis](#reachable-authority-use) (`E0527`); excluded operations and statements after an unconditional transfer do not count. Reaching panic or abort does not erase an earlier operation.
- **Path Sensitivity and Stability**:
    - **Stable Paths**: Field paths originating from immutable `let` bindings and immutable record fields are tracked across conditional dominance regions without depth limits. Overlapping slot assignment or mutable write invalidates affected facts (`E0310`).
    - **Nonzero Integer Refinement**: Predicates proving an integer path nonzero (`d != 0`, `0 != d`, `d > 0`, `d < 0`, `assert(d != 0)`, or `match` arms excluding `0`) discharge division and remainder `@Panic` (`a / d`, `a % d`) across their dominance region, subject to the same write-invalidation rules.
    - **Loop Convergence**: Variant elimination and optional unwrapping form a finite-height lattice; loop flow analysis converges in finite steps.

```ril
type Cell = .{ var value: ?int }

-- E0533: the callback's possible writes are not known to be independent.
-- An explicitly open state/provenance row preserves actual obligations; a bare fn() -> () is closed and pure.
fn unknown_writer(mut cell: Cell, action: fn() & -> ()) &mut -> () {
    if cell.value != None {
        let before = cell.value + 1           -- OK: narrowed to int
        action()                              -- Cannot prove that cell.value stays unchanged
        -- let after = cell.value + 1         -- Error [E0533]: unknown overlap with the live origin
    }
    cell.value = None
}

-- E0310: this callee is known to write the very field that was narrowed.
fn clear(mut cell: Cell) &mut -> () { cell.value = None }
fn known_writer(mut cell: Cell) &mut -> () {
    if cell.value != None {
        clear(mut cell)                       -- Known write invalidates cell.value's refinement
        -- let after = cell.value + 1         -- Error [E0310]: the earlier narrowing no longer applies
    }
}

-- OK: the same unknown callback cannot change an independent immutable snapshot.
fn snapshot_before_callback(mut cell: Cell, action: fn() & -> ()) &mut -> () {
    let snapshot = clone(ref cell)
    if snapshot.value != None {
        action()
        let after = snapshot.value + 1        -- OK: snapshot.value remains narrowed to int
    }
    cell.value = None
}
```

```ril
-- In-place optional unwrapping (?T -> T):
type User = .{ id: int, name: str }

fn process_user(u: ?User) -> str {
    if u != None {
        u.name                                 -- OK: 'u' narrowed to User; direct field access
    } else {
        "Anonymous"
    }
}

-- Guard clause with early return:
fn fetch_id(u: ?User) -> int {
    if u == None {
        return -1                              -- Type never; contributes no normal successor to the join
    }
    u.id                                       -- OK: sequential flow inherits User
}

-- Nonzero integer narrowing discharges division @Panic:
fn safe_step(total: int, step: int) -> int {
    if step == 0 { return 0 }
    total / step                               -- OK: 'step' proven nonzero; 0 @Panic
}

-- Sum type variant discrimination via 'is' and payload projection:
type Geometry {
    Circle(f64),
    Rect(f64, f64),
    Point,
}

fn compute_area(g: Geometry) -> f64 {
    if g is Geometry::Circle {
        3.14159 * g.0 * g.0                    -- OK: n = 1 scalar payload projected via .0
    } else if g is Geometry::Rect {
        g.0 * g.1                              -- OK: n = 2 tuple payload projected via .0, .1
    } else {
        0.0                                    -- OK: Point (n = 0) has no payload
    }
}

-- Short-circuit conjunction with immutable path chaining (depth <= 3):
type Account = .{ id: int, details: ?.{ balance: int } }

fn check_solvent(acc: Account) -> bool {
    (acc.details != None) && (acc.details.balance > 0) -- OK: acc.details narrowed in right operand
}

-- Loop body narrowing and post-loop refinement:
fn drain_cursor(initial: ?int) -> int {
    var cursor = initial
    var total = 0
    while cursor != None {
        total += cursor                        -- OK: cursor narrowed to int in loop body
        cursor = None                          -- Invalidation: reset to ?int
    }
    assert(cursor == None)                     -- OK: post-loop inherits cond == false (None)
    total
}

-- Reassignment invalidation (E0310):
fn test_invalidation() -> () {
    var opt: ?int = Some(42)
    if opt != None {
        let _ = opt + 1                        -- OK: opt is int
        opt = None                             -- Reassignment: refinement invalidated
        -- let bad = opt + 2                   -- Error [E0310]: variable 'opt' was narrowed to 'int', but refinement was invalidated by reassignment; current flow type is '?int'
    }
}

-- Contradictory narrowing rejection (E0311):
fn test_contradiction(g: Geometry) -> () {
    if g is Geometry::Circle {
        -- if g is Geometry::Rect {            -- Error [E0311]: condition 'g is Geometry::Rect' is statically unsatisfiable; target is already narrowed to 'Geometry::Circle'
        --     println("unreachable")
        -- }
    }
}

-- A ref retains the selected immutable object, not the reassignable slot:
fn test_aliased_hazard() -> () {
    var raw: ?int = Some(10)
    let ref selected = raw
    raw = None
    assert(selected is Some(10) && raw is None)
}

-- is reads existing names and narrows the subject without binding payload names:
fn test_non_binding_predicate(g: Geometry) -> () {
    if g is Geometry::Circle && g.0 > 5.0 {
        let radius = g.0                       -- OK: payload access via .0
        -- let escaped = r                     -- Error [E0204]: is introduced no r
    }
}

-- Transitive Latent Havoc via mutating call:
fn test_latent_havoc() -> () {
    var count: ?int = Some(10)
    if count != None {
        let mut step = \&up{mut count} -> { count = None }
        step()                                 -- Mutating call invalidates 'count'
        -- let bad_use = count + 1             -- Error [E0310]: variable 'count' was narrowed to 'int', but refinement was invalidated by mutating call 'step()'; current flow type is '?int'
    }
}

-- Generic confinement: bare type parameter rejected:
fn test_generic_confinement<T>(x: Geometry) -> () {
    -- if x is T {                             -- Error [E0301]: cannot test unconstrained generic type parameter 'T' in narrowing predicate
    --     println("invalid")
    -- }
}

-- Dead-path mutation phase ordering:
fn test_dead_write_phase_ordering() -> () {
    -- var unused: ?int = Some(10)            -- Error [E0527]: variable 'unused' declared 'var' is never modified along reachable paths
    -- if false {
    --     unused = Some(20)                  -- Write in statically unreachable branch does not satisfy Reachable Authority-Use Requirement
    -- }
}

-- Stable path narrowing across deep field paths:
fn test_deep_path_narrowing(root: .{ a: ?.{ b: ?.{ c: ?.{ d: int } } } }) -> () {
    if (root.a != None) && (root.a.b != None) && (root.a.b.c != None) {
        let d_val: int = root.a.b.c.d          -- OK: deep stable path tracked directly
    }
}
```

---

## Functions, Closures, and Callables

### Named Function Declarations and Contrast Matrix

Named functions are declared at module scope or in a block's `where` clause. Their declarations are in scope throughout the enclosing declaration scope, allowing mutual recursion without forward declarations. Captured bindings must still be initialized before use.

```ebnf
FunctionDecl         ::= { MetaAttr } [ "pub" ] [ "halt" ] "fn" ValueName [ GenericParams ]
                         "(" [ ParameterList ] ")" [ EffectAnnot ] [ StateAnnot ] [ ReturnSpec ]
                         [ SignatureWhereClause ] [ Block ]
SignatureWhereClause ::= "where" SignatureWhereItem { Separator SignatureWhereItem } [ Separator ]
SignatureWhereItem   ::= LocalTypeDecl | FunctionDecl | MetaFnDecl
ParameterList        ::= Parameter { "," Parameter } [ "," ]
Parameter            ::= RegularParam | MetaParam
RegularParam         ::= [ ParameterMode ] ValueName [ ":" TypeExpression ] { ContractGuard } [ "=" Expression ]
MetaParam            ::= "meta" ValueName [ ":" ValueType ] { "|>" PipelineConstraint } [ "=" Expression ]
ReturnSpec           ::= ReturnType { ContractGuard }
ContractGuard        ::= "|>" [ "ref" ] QualifiedName [ GenericArgs ] [ "(" [ ContractArgList ] ")" ]
ContractArgList      ::= ContractArg { "," ContractArg } [ "," ]
ContractArg          ::= [ ValueName ":" ] ( "ref" QualifiedName | QualifiedName | [ "-" ] Literal )

Argument             ::= [ ValueName ":" ] ( MutableArgumentMode AssignTarget | "ref" Expression | "new" Expression | Expression )
MutableArgumentMode  ::= "mut" | "^mut"
ArgumentList         ::= Argument { "," Argument } [ "," ]
CallExpr             ::= Expression "(" [ ArgumentList ] ")" [ TrailingClosure ] | Expression TrailingClosure
TrailingClosure      ::= AnonFnExpr
CallableType     ::= "fn" "(" [ ParameterTypeList ] ")" [ CallableAnnot ] [ ReturnType ]
CallableAnnot    ::= "@&" [ StateAnnot ]
                   | CallableEffectAnnot [ CallableStateAnnot ]
                   | CallableStateAnnot
CallableEffectAnnot ::= EffectAnnot | "@"
CallableStateAnnot  ::= StateAnnot [ "&" ] | "&"
ParameterTypeList ::= ParameterTypeItem { "," ParameterTypeItem } [ "," ]
ParameterTypeItem ::= [ ParameterMode ] [ ValueName ":" ] TypeExpression
```

Leading `mut`/`^mut` arguments require assignable targets (`E0410` for `f(^mut clone(x))`); `ref` observes an expression. A parenthesized sharing expression cannot replace an ordinary argument-mode marker (`E0405`). Dependent lexical template operands elaborate their verified mode. [Fresh storage inputs](#homogeneous-storage-authority) receive construction authority before publication; plain unqualified parameters require immutable data. Constructors follow their product member and payload modes. A `meta` parameter receives a compile-time static argument (`E0814`); parameter modes do not apply (`E0403`). Unspecialized `meta` callables are rejected as runtime `CallableType` values (`E0816`).

```ril
type DeferredFactory = fn() -> fn() @Io -> int -- Io belongs to the returned callable
type EffectfulFactory = fn() @Io -> fn() -> int -- Io belongs to the factory
type CapturingFactory = fn() &capture -> new (fn() &up -> int)
```

Arrows associate right. Each effect/state clause belongs to the callable whose parameter list it follows, before its return arrow. Results follow [return access modes and sources](#return-construction-access-modes-and-sources). Executable named definitions require result annotations, including `-> ()`, under [mandatory contract completion](#mandatory-contract-inference-and-completion). Callable types and bodyless effect operations may abbreviate unit results. Anonymous definitions use lambda syntax with optional source annotations and complete inferred contracts.

#### Dual-Tier Where Invariants

- **Signature `where` Scope (`SignatureWhereClause`, `E0704`)**:
   - `SignatureWhereClause` admits `LocalTypeDecl` (`type`), `FunctionDecl` (`fn`), and `MetaFnDecl` (`meta fn`). Declaring `eff` or `sub` is statically rejected (`E0704`).
   - Items declared in `SignatureWhereClause` are in scope across the function signature (including `ContractGuard`s and `PipelineConstraint`s) and the function body block.
- **Signature Reference Confinement (`E0706`)**:
   - Any type or guard callable referenced in a function signature must be declared in `SignatureWhereClause` or an outer scope. Referencing items declared in `BlockWhereClause` is statically rejected (`E0706`).
- **Downward Isolation (`E0705`)**:
   - Items in `SignatureWhereClause` must not reference items declared in `BlockWhereClause` (`E0705`). Items in `BlockWhereClause` may reference items from `SignatureWhereClause`.
- **Collision Prohibition (`E0203`)**:
   - Declaring an identical identifier in both `SignatureWhereClause` and `BlockWhereClause` of the same function is statically rejected (`E0203`).
- **Exported Type Meaning**:
   - For `pub fn`, structural aliases in `SignatureWhereClause` have the same meaning for importers as their expanded structural types; private helper names are not required at call sites.
- **Generic Constraints and Value Contract Guards in `SignatureWhereClause`**:
   - Pure `type` functions declared in `SignatureWhereClause` may be referenced as generic/meta pipeline constraints (`<T |> Guard>`) or computed return types; pure fallible `fn` and `meta fn` helpers declared in `SignatureWhereClause` may be referenced by signature [`ContractGuard`s](#signature-value-contracts).

```ril
-- Signature-level where for complex higher-order pipeline:
-- audit_log is a mutable module binding supplied by this fixture.
pub fn process_stream<T, R, E>(
    stream: []T,
    transform: TransformFn<T, R, E>,
    mut sink: AuditSink<R>,
) @Async &mut &up(sub){mut audit_log} -> Result<[]R, E>
where
    type TransformFn<In, Out, Err> = fn(In) @Async -> Result<Out, Err>
    type AuditSink<Item>           = fn(Item) &up(sub){mut audit_log} &up -> ()
{
    let mut out: []R = []
    for stream as item {
        let res = transform(item)?
        sink(res)
        out |> mut Array::push(res)
    }
    Ok(out)
}

-- Prohibited: Declaring 'eff' in SignatureWhereClause (E0704):
-- fn bad_sig_eff(x: int) -> int
-- where
--     eff Yield { emit(int) -> () }         -- Error [E0704]: 'eff' cannot be declared in signature 'where' clause; place in block 'where' clause
-- {
--     x
-- }

-- Prohibited: Downward reference from signature to block where (E0705):
-- fn bad_downward<T>(item: T) -> Wrapper
-- where
--     type Wrapper = .{ state: InternalState } -- Error [E0705]: signature 'where' clause cannot reference 'InternalState' declared in inner block 'where' clause
-- {
--     Wrapper.{ state: .{ code: 0 } }
-- where
--     type InternalState = .{ code: int }
-- }

-- Prohibited: Signature referencing type defined in block where (E0706):
-- fn bad_sig_target(cb: Callback) -> ()      -- Error [E0706]: type 'Callback' used in function signature must be declared in signature 'where' clause, not block 'where' clause
-- {
--     cb()
-- where
--     type Callback = fn() -> ()
-- }

-- Prohibited: Duplicate declaration across signature and block tiers (E0203):
-- fn bad_duplicate(h: Handler) -> ()
-- where
--     type Handler = fn() -> ()
-- {
--     ()
-- where
--     type Handler = fn(int) -> ()           -- Error [E0203]: type 'Handler' is already declared in signature 'where' clause
-- }
```

#### Signature Value Contracts

```ril
pub type Span = .{ lo: int, hi: int }
pub type RangeErr { Inverted, EmptySpan }

-- Type of 'lo' inferred from valid_range's 1st parameter (int); 'hi' in scope for 'lo' guard:
pub halt fn make_span(
    lo |> valid_range(hi),
    hi: int,
) -> Result<Span, RangeErr> |> non_empty_span
where
    halt fn valid_range(lo: int, hi: int) -> Result<(), RangeErr> {
        if lo <= hi { Ok() } else { Err(RangeErr::Inverted) }
    }
    halt fn non_empty_span(s: Span) -> Result<(), RangeErr> {
        if s.hi > s.lo { Ok() } else { Err(RangeErr::EmptySpan) }
    }
{
    Ok(Span.{ lo, hi })
}

assert(make_span(2, 5) == Ok(Span.{ lo: 2, hi: 5 }))
assert(make_span(5, 2) == Err(RangeErr::Inverted))
assert(make_span(3, 3) == Err(RangeErr::EmptySpan))
```

```ril
-- Observing mutable/construction parameters and construction returns via '|> ref':
type Buffer = .{ var len: int, cap: int }

fn reserve_exact(
    mut buf |> ref has_headroom(extra),
    extra: int,
) &mut -> ?int
where
    fn has_headroom(ref b: Buffer, need: int) -> ?() {
        if need >= 0 && b.len + need <= b.cap { Some() } else { None }
    }
{
    buf.len += extra
    Some(buf.len)
}

fn alloc_non_empty(cap: int) -> new Result<Buffer, str> |> ref non_zero_cap
where
    fn non_zero_cap(ref b: Buffer) -> Result<(), str> {
        if b.cap > 0 { Ok() } else { Err("zero capacity") }
    }
{
    Ok(Buffer.{ len: 0, cap })
}

-- Compile-time execution uses the identical '?' contract rules in 'meta fn':
meta fn checked_ratio(num: int, den |> non_zero) -> Result<int, str>
where
    meta fn non_zero(d: int) -> Result<(), str> {
        if d != 0 { Ok() } else { Err("division by zero") }
    }
{
    Ok(num / den)
}
meta let RATIO = checked_ratio(20, 4)        -- Evaluates statically to Ok(5)

-- Rejections:
-- fn bool_guard(x: int |> is_pos) -> Result<int, str>
-- where fn is_pos(n: int) -> bool { n > 0 } { Ok(x) }       -- Error [E0712]: guard must return Result<(), E> or ?()
-- fn unfallible_ret(x: int |> non_zero) -> int { x }        -- Error [E0713]: enclosing return type cannot propagate guard failure via '?'
-- fn missing_type(x) -> Result<int, str> { Ok(x) }          -- Error [E0544]: parameter without ContractGuard requires ': Type'
-- fn consumed_in_ret(new b: Buffer) -> Result<int, str> |> check_with(ref b)
-- where fn check_with(n: int, ref b: Buffer) -> Result<(), str> { Ok() }
-- { let _ = forward_buf(new b); Ok(1) }                     -- Error [E0549]: construction parameter 'b' cannot be read in return guard
```

| Contract rule | Requirement |
| :--- | :--- |
| Placement & syntax | `ContractGuard` (`\|> [ref] f(args)`) attaches to `RegularParam` and declaration `ReturnSpec` (`FunctionDecl`, `MetaFnDecl`, `DeclFunction`). Only read-only `\|>` and `\|> ref` are admitted (`mut`/`^mut`/`new` are excluded by guard purity `E0409` and non-consumption `E0549`); inline lambdas and arbitrary expressions are prohibited, and `CallableType` / `EffectOpDecl` carry no guards |
| Omitted parameter type | A `RegularParam` with at least one `ContractGuard` may omit `: TypeExpression`, inferring its type from the first guard's leading parameter (`E0544` if both `: TypeExpression` and guards are omitted; `E0344` if undetermined). `[ParameterMode]` remains explicit |
| Fallible propagation (`E0712`, `E0713`) | Every guard callable must return `Result<(), E>` or `?()` (`E0712`), compatible under postfix `?` with the enclosing function's `Result<T, E_out>` or `?T` return type (`E0713`); contract failure never panics |
| Scope & entry order | Explicit arguments and omitted defaults bind left-to-right first (`E0408` unchanged on defaults). Parameter guards then run in declaration order with all parameters in scope via `(p \|> [ref] guard(args))?` |
| Return guard order | On normal or early `return`, `Err` / `None` returns immediately; `Ok(v)` / `Some(v)` runs each return guard via `(v \|> [ref] guard(args))?` before returning `Ok(v)` / `Some(v)`. `\|> ref` preserves `new` qualification on `v`; referencing a `new` parameter in a return guard is `E0549` |
| Purity & first-class values | Guards admit no outward operational effects or mutable/capturing state (`E0409`); read-only immutable `.ril` `&up`/`&up(sub)` joins the enclosing contract, and `halt` requires `Diverge`-free guards (`E0820`). `meta fn` executes the same `?` semantics at compile time. Coercing a guarded `fn` to a `CallableType` retains its entry and exit guards |

```ril
-- Implementation Bodies and Built-in Declarations:
pub halt fn len<T |> LenTarget>(via item: T) -> int -- Registered built-in declaration (bodyless)
fn sys_alloc(size: int) -> []u8                    -- Private registered built-in declaration (bodyless)
pub fn double(x: int) -> int { x * 2 }             -- Standard Ril function with implementation body

-- Rejections:
-- fn custom_bodyless() -> ()           -- Error [E0902]: unregistered bodyless function requires an implementation
-- halt fn len(item: int) -> str        -- Error [E0909]: signature does not match registered built-in contract

-- Hoisted Named Function:
pub fn calculate_tax(amount: int) -> int {
    amount * 20 / 100
}
let r1 = calculate_tax(100)            -- OK: direct call
```

- **Implementation Bodies and Built-in Declarations (`E0902`, `E0909`)**: A function with a body `{ ... }` uses its Ril implementation; a bodyless `fn` in `.ril` declares a built-in primitive bound by its registered declaration identity (module path and identifier). Unregistered declarations or signature mismatches trigger `E0902` / `E0909`; identical names in other scopes do not acquire built-in identity. `pub` independently controls visibility; both public and private built-ins may omit bodies. Effects, modes, phase, and termination follow the primitive contract. External `.d.ril` rules remain unchanged.

| Aspect | Named Function (`fn`) | Environment-Free Anonymous Function (`\x -> ...`) | Capturing Anonymous Function (`\x -> ...`) |
| :--- | :--- | :--- | :--- |
| **Declaration availability** | Throughout the enclosing module or block declaration scope; captures obey initialization rules | No declaration hoisting; evaluate the function expression at its source position | No declaration hoisting; evaluate the function expression at its source position |
| **Environment Capture** | Explicit named origins; block-local values can retain an environment | None (no captured state) | Actual lexical environment, abbreviated in types by `&up` |
| **Type Representation** | Item identity / `fn(P) -> R` | `fn(P) -> R` | `fn(P) &up -> R` |
| **Handle Requirement** | Direct declaration call; stored values follow actual environment modes | Callable via `let` handle | `let` (immutable), `let ref` (live observer), or writable handle (mutable environment) |

### Callable Contracts

```ril
fn next_value(n: int) -> int {
    var result = n
    result += 1
    result
}
var global_count = 0
fn tick() &up(sub){mut global_count} -> () { global_count += 1 }
fn visible() &up(sub){mut global_count} -> () { tick() }
-- fn hidden() -> () { tick() }             -- Error [E0510]: the ordinary wrapper has undeclared concrete state

eff Log { write(str) -> () }
fn logged() @Log -> () { Log::write("event") }
-- fn hidden_effect() -> () { logged() }    -- Error [E0612]: concrete residual effects require declaration
```

- **Definitions**: Infer complete contracts after handling and local discharge under [mandatory contract completion](#mandatory-contract-inference-and-completion). Named definitions spell concrete state and residual operational effects, including obligations inherited from calls (`E0510` / `E0612` when missing). Inferred `Diverge`, `Panic`, and `Fatal` are retained automatically in semantic interfaces without source annotations (`E0620` if written explicitly). Anonymous source annotations are optional.
- **Local Purity**: Mutation of confined local storage, immutable publication of eligible construction results, and call-local environments do not by themselves create outward state obligations. Creating a surviving environment or an additional surviving writer retains the applicable `&capture`, `&^mut`, or named-source obligation. Named definitions spell those obligations; anonymous functions may retain them entirely in their inferred contracts.
- **Callback Dependence**: Infer and forward symbolically the obligations dependent on callable parameter values, including constituents reached through fields, elements, projections or preserved aliases. The dependency is tied to the actual parameter value. Once a caller supplies a known callable, directly or inside an aggregate, its resulting concrete obligations join the caller's contract after handling and local discharge. Named definitions spell concrete obligations.
- **Anonymous Definitions**: Infer the complete contract, including captures and concrete lexical sources. Type, result, effect, state, capture and returned-source annotations are optional; written annotations and contextual callable types constrain inference. Body operations belong to later invocation.

```ril
fn invoke(action: fn() @& -> ()) -> () { action() }
fn declared_state() &up(sub){mut global_count} -> () { invoke(tick) }
fn declared_effect() @Log -> () { invoke(logged) }
-- fn hidden_through_callback() -> () { invoke(tick) } -- Error [E0510]: this caller's dependency is concrete
-- fn hidden_through_alias() -> () { let action = tick; action() } -- Error [E0510]
-- fn fixed_conflict(action: fn() -> ()) &{} -> () { tick(); action() }
-- Error [E0534]: a closed definition already contains concrete state
fn invoke_pure(action: fn() -> ()) @{} &{} -> () { action() }
fn nothing() -> () {}
invoke_pure(nothing)                  -- OK
-- invoke_pure(tick)                 -- Error [E0534]: total state is not empty
-- invoke_pure(logged)               -- Error [E0534]: total effect row is not empty

type Actions = .{ run: fn() @& -> () }
fn invoke_field(actions: Actions) -> () { actions.run() }
fn declared_field() &up(sub){mut global_count} -> () { invoke_field(.{ run: tick }) }
-- fn hidden_field() -> () { invoke_field(.{ run: tick }) } -- Error [E0510]: wrapping the known callback does not erase state
```

#### Mandatory Contract Inference and Completion

The compiler must infer the full checked contract of every public, private, local, anonymous and test function. Named definitions spell prescribed concrete annotations; [`via` templates and `infer` results](#inference-domains-and-contract-completion) retain genuine mode dependencies and requested result details in metadata. Anonymous source annotations are optional. Complete contracts are available to checking, tooling, callers and module summaries.

| Semantic stage | Requirement |
| :--- | :--- |
| Infer | Derive all possible origins, reachable uses, and normalized obligations from the body, context, and verified dependencies; source annotations cannot justify themselves |
| Complete | Expose the full inferred contract and the source annotations required for named definitions; preserve the specified anonymous-function source omissions |
| Validate | Check missing annotations, idle modes/markers, excess state/provenance annotations, and exact closed contracts against the inferred program behavior and source authority |

| Inference / completion | Requirement |
| :--- | :--- |
| Inference scope | The same complete analysis for public, private, local, anonymous, and test functions |
| Facts | Types, access modes/history, root and contained origins, aliases, writes, retention, captures, effects, escape/ownership, and callback dependencies |
| Required named source | Data types, concrete parameter/result modes and dependencies, and concrete operational-effect/state/capture annotations; inferred `Diverge`, `Panic`, and `Fatal` use no source annotation (`E0620`); `via` modes and dependent clauses, and `infer` results, use their specified metadata-only completion |
| Anonymous source | Type, result, effect, state, capture, and returned-source annotations are optional; absence alone is never `E0544`, `E0510`, or `E0612` |
| Anonymous constraints | Written annotations and contextual callable types constrain the inferred contract; incompatible constraints are rejected by the applicable typing, access-mode, or callable-matching diagnostic |
| Authority syntax | Concrete modes, ordinary argument/sharing markers, and resource operations remain required; lexical templates elaborate only verified dependent receptions and transfers |
| Shared-reception completion | Follow the [shared-site spelling](#shared-writable-authority); inference cannot substitute an exclusive declaration for shared authority |
| Root-return normalization | `^mut(x)` covers only root-return retention; actual writes and extra escape paths remain distinct obligations |
| Context and generality | Use body and contextual constraints to infer complete callable contracts, including generic/structural constraints and symbolic callback dependencies; lack of a unique monomorphic signature is not by itself a missing-annotation error |
| Missing-annotation diagnostics | Named parameter or return annotation: `E0544`; named state or an independently required reception marker: `E0510`; named operational-effect declaration or an actually unhandled operation boundary: `E0612`; inferred `Diverge`/`Panic`/`Fatal` are implicit; argument marker: `E0405` |
| Inconsistent-annotation diagnostics | Absent required authority use or redundant executable sharing marker: `E0527`; excess concrete state/provenance annotation: `E0529`; incompatible callable contract: `E0534` (parameter modes: `E0407`); unresolved required type/static instantiation: `E0344`; invalid return sources: `E0545` |
| Explanations | Expose complete inferred classifications and origin/propagation chains, including possible sharing, actual anonymous captures, and unproved overlap |
| Interfaces | Preserve fine paths, mode history, store/return relations, and output correlations in semantic summaries; changes invalidate dependent proofs |
| Proof limits | Unknown facts never prove access authority, immutability, freshness, separation, or escape. Bodyless foreign declarations remain trusted explicit contracts |

Missing required annotations reject a named definition. Explicit and template-elaborated transfers consume construction paths at their defined point. Inference follows [complete provenance](#complete-provenance-and-required-annotations); symbolic mode/callback facts, full effect rows including implicitly inferred `Diverge`, `Panic`, and `Fatal`, and budget/panic-boundary eligibility requirements remain in interfaces where source spelling is optional.

`E0344` applies where a construct requires a determined type or static argument. An anonymous function may retain generic or structural constraints in its complete inferred contract; validate them at required instantiations and against explicit constraints.

```ril
type Cell = .{ var count: int }

-- Named-source completion remains mandatory:
-- fn make() { Cell.{ count: 0 } }      -- Error [E0544]: complete as fn make() -> new Cell
-- fn id(x) { x }                      -- Error [E0544]: spell the inferred generic parameter and return annotations
fn make() -> new Cell { Cell.{ count: 0 } }
fn inspect(cell: Cell) -> int { cell.count }

-- Anonymous functions need no complete contextual type or source annotations:
let identity = \value -> value        -- OK: infer its generic identity contract
let inferred_read = \cell -> cell.count -- OK: retain the inferred structural parameter constraint
let inferred_write = \mut cell: Cell -> { cell.count += 1 } -- OK: infer the actual write and &mut; validate mut against its use

-- Explicit contextual types remain available:
let read: fn(cell: Cell) -> int = \cell -> cell.count

eff Log { write(str) -> () }
let logged = \-> Log::write("event") -- OK: infer and preserve Log without a source effect annotation
-- let invalid: fn() -> () = logged  -- Error [E0534]: the explicit closed callable type cannot erase Log
```

#### Closed and Open Callable Rows

Callable types are closed by default at every arrow for operational effects and state/provenance, independently of whether that arrow receives or returns another callable. `@` annotations on `CallableType` and `FunctionDecl` govern operational effects only; `Diverge`, `Panic`, and `Fatal` are never written in `@` clauses (`E0620`) and are tracked automatically in semantic metadata.

The annotations belong to the callable whose parameter list immediately precedes them, before that callable's result arrow:

```ril
type PureAction = fn() -> ()
type ExplicitPureAction = fn() @{} &{} -> ()
type EffectOpenAction = fn() @ -> ()
type StateOpenAction = fn() & -> ()
type OpenAction = fn() @& -> ()
type LoggedAction = fn() @Log -> ()
type LoggedWithOpenState = fn() @Log & -> ()
type EffectOpenMutator = fn(mut Cell) @ &mut -> ()
type MutatorWithOpenState = fn(mut Cell) &mut & -> ()
```

| Row form on a callable type | Matching requirement |
| :--- | :--- |
| Omitted effects / `@{}` | Closed empty operational effect row (implicit `Diverge`, `Panic`, and `Fatal` remain permitted) |
| Explicit nonempty effects | Closed exact normalized operational effect row |
| Standalone `@` | Open operational effect dimension; preserve all actual residual effects |
| Omitted state/provenance clauses | Closed normalized state and provenance obligations supplied by the written clauses and the return annotation's implicit baseline |
| Explicit `&{}` | Closed empty total state/provenance row, including the return annotation's baseline; incompatible return retention cannot be hidden |
| Explicit nonempty state/provenance clauses | Closed exact normalized total state/provenance row, including the return baseline |
| Standalone `&` | Open state/provenance dimension; written state/provenance clauses remain requirements and additional actual obligations are preserved |
| `@&` | The combined spelling of open effects and open state/provenance |

An open effect marker opens the whole effect dimension. State/provenance openness may accompany concrete requirements such as `&mut`, `&up(sub){...}`, `&up{...}`, or `&return{...}`. Opening one dimension leaves the other closed; source authority, invocation access modes and retention are checked independently. Combining open state/provenance (`&` or `@&`) with the closed-total assertion `&{}` is `E0547`; use effect-only `@` for open effects with empty state/provenance obligations.

Explicit empty rows are admitted on first-order and higher-order callable types and definitions when their complete contracts satisfy them; incompatible contracts use the applicable diagnostic. Named source completion and symbolic callback obligations follow [mandatory contract completion](#mandatory-contract-inference-and-completion).

Open markers belong only to `CallableType` arrows. A standalone `@`, `&`, or `@&` directly annotating a named or anonymous definition, an effect-operation declaration, or a bodyless foreign declaration is `E0547: InvalidOpenRowPlacementError`; so is placing an open state/provenance marker on the same arrow as `&{}`. An open callable type nested in a definition's parameter, result, or data schema remains valid; it is that nested type's arrow which is open. A bodyless foreign declaration provides a trusted explicit contract and has no implementation from which to infer an open invocation row.

```ril
fn plain() -> () {}
fn logged() @Log -> () { Log::write("event") }
let pure: PureAction = plain
-- let closed: PureAction = logged             -- Error [E0534]: Log is additional to the closed empty effect row
-- let overstated: LoggedAction = plain        -- Error [E0534]: the exact Log row is absent
let effect_open: EffectOpenAction = logged     -- OK: its actual Log obligation remains
let fully_open: OpenAction = logged            -- OK: no obligation is erased

fn closed_invoke(action: OpenAction) @{} &{} -> () { action() }
closed_invoke(plain)                            -- OK
-- closed_invoke(effect_open)                  -- Error [E0534]: this actual invocation has Log
-- fn incomplete_escape() @& -> () {}          -- Error [E0547]: open markers are not definition annotations
-- let invalid = \ @ -> ()                     -- Error [E0547]: a lambda infers its actual effect row
-- type ConflictingRows = fn() @& &{} -> ()    -- Error [E0547]: the state/provenance dimension cannot be both open and explicitly closed
```

An explicit `&{}` constrains total state and provenance obligations, including root-return retention, capture, inherited access and contained dependencies. Omitted state/provenance clauses include the return annotation's implicit baseline:

```ril
type Cell = .{ var count: int }
fn retain(^mut cell: Cell) -> ^mut(cell) Cell { cell }
type RootRetainer = fn(^mut value: Cell) -> ^mut(value) Cell
let renamed: RootRetainer = retain              -- OK: source labels are bound by parameter position
-- let erased: fn(^mut x: Cell) &{} -> ^mut(x) Cell = retain
-- Error [E0534]: explicit empty total state/provenance obligations conflict with root-return retention
-- let wrong_result: fn(^mut x: Cell) & -> Cell = retain
-- Error [E0534]: an open state/provenance row cannot replace a writable root return with an immutable result
```

Each nested arrow is checked separately. Creating or returning an existing callable does not execute its body; the returned callable's later invocation retains its own closed or open contract:

```ril
type ReturnsPure = fn() -> fn() -> ()
type ReturnsOpen = fn() -> fn() @& -> ()
type OpenFactory = fn() @& -> fn() -> ()
fn give_logged() -> EffectOpenAction { logged }
-- fn hidden_later_effect() -> () { give_logged()() }
-- Error [E0612]: the later invocation still requires Log
```

#### Callable Contract Matching

Match a callable's complete normalized contract at every assignment, argument, aggregate member, return and module/type boundary. Closed effect and state/provenance rows require exact equality. Open rows admit additional actual entries only in their selected dimension; every explicitly written entry must be satisfied.

Normalization expands effect-set and transparent aliases, compares effect instances using static-argument identity, canonicalizes source and provider identities, combines equivalent access entries, and includes access modes implied by a return annotation. Duplicate spellings do not create different contracts. Preserve [verified operation footprints, conditions and callable alternatives](#authority-calls-and-contract-operations); a displayed effect row does not erase them. Formal parameter labels and their bound return-source references are alpha-renamed by parameter position before comparison; external and captured sources retain their resolved declaration and activation identities.

Parameter data shapes are contravariant and result data shapes covariant. Concrete parameter modes match; explicit `via` mode patterns check the actual family and its acceptance conditions. Root and contained guarantees, source authority, construction qualification and resource/scoped lifetimes are independent checks. For a family, every retained alternative must satisfy closed-row matching.

Named definition annotations validate the required concrete projection plus preserved symbolic dependencies. Later closed callable-type ascriptions check the full inferred contract, including metadata-only mode-dependent clauses.

The `&up` callable-type abstraction admits an environment-free callable or the checked abstract environment shape. Normalize it for matching and preserve private captured origins, modes, lifetimes, and correlations in verified metadata. Additional effects, named module access, independent retained publication, and the invocation's `&capture` obligation require separate annotations.

| Callable contract component | Rule |
| :--- | :--- |
| Closed operational effect row | Exact normalized actual operational effects |
| Implicit execution effects | `Diverge`, `Panic`, and `Fatal` are tracked in verified semantic summaries across aliases and ascriptions, distinguishing direct `fatal` from cleanup double faults for [parallel callbacks](#parallel-faults-fatal-visibility-and-budgets) |
| Closed state/provenance row | Exact normalized actual obligations after the written environment abstraction and implicit return baseline |
| Open effects / state-provenance | Preserve the actual complete row; permit additional entries only in the opened dimension |
| Parameter/handle access modes | Unchanged by openness, aliases, or ascription |
| Root returns | Construction, access mode, and source guarantees remain independently checked |
| Contained return dependencies | Explicit dependencies must match; open `&` may admit additional actual `&return` facts, all of which continue to propagate |
| Symbolic callback dependencies | Preserve their complete conditions and instantiate them at calls; closure of a destination row checks those conditions rather than erasing them |
| Alternatives | Preserve every possible obligation and only common guarantees under [provenance](#complete-provenance-and-required-annotations). Every retained callable-contract alternative must satisfy a closed equality or an open required entry; a union cannot invent a required entry missing from one alternative |
| Named definitions | Complete concrete source annotations; symbolic parameter-dependent obligations remain in the full verified contract |
| Anonymous definitions | Full inference; no requirement to spell inferred annotations in source |
| Incompatible callable value | `E0534`; parameter-mode mismatches retain `E0407` and other dedicated conditions retain their codes |
| Bodyless foreign declarations | Trusted explicit operational-effect/state rows plus automatic `Diverge`, `Panic`, and `Fatal`; no absence-of-`Diverge` or coverage guarantee follows |

Verified semantic summaries retain fine paths, mode history, input/output relations and output correlations. Every actual observed/retained constituent of a returned graph, including one admitted by an open state/provenance row, is checked before immutable publication, task crossing, further retention or exclusivity-sensitive access.

```ril
eff Log { write(str) -> () }
var global_count = 0
fn plain() -> () {}
fn logged() @Log -> () { Log::write("event") }
fn tick() &up(sub){mut global_count} -> () { global_count += 1 }
type Action = fn() @& -> ()
type PureAction = fn() -> ()
type ExactLog = fn() @Log -> ()
type ExactTick = fn() &tick -> ()

fn invoke(action: Action) -> () { action() }
fn closed(action: Action) @{} &{} -> () { action() }
let action: Action = logged
let exact_log: ExactLog = logged
let exact_tick: ExactTick = tick
-- let loses_state: fn() @ -> () = tick          -- Error [E0534]: state/provenance remains closed
-- let loses_effect: fn() & -> () = logged       -- Error [E0534]: effects remain closed
-- let fewer_effects: ExactLog = plain           -- Error [E0534]: exact matching rejects missing Log too
let selected: Action = if choose_log { plain } else { logged }
-- let not_exact: ExactLog = selected           -- Error [E0534]: the plain alternative lacks the required exact Log row
closed(plain)                                   -- OK
-- closed(selected)                            -- Error [E0534]: the possible Log obligation remains
fn call_plain() -> () { invoke(plain) }
fn call_logged() @Log -> () { invoke(logged) }
fn call_tick() &tick -> () { invoke(tick) }
-- fn missing_log() -> () { invoke(logged) }     -- Error [E0612]: named callers complete concrete obligations
-- fn missing_state() -> () { invoke(tick) }     -- Error [E0510]
```

Later closed matching of a callable passed through an open type uses its preserved actual contract. Named-function state references resolve to the provider's verified named projection with its original source identities; other contract components are matched separately.

Invoking already shared storage does not itself publish another writer. Actual environment mode determines whether invocation needs a writable or observation handle. Implicit `Diverge`, `Panic`, and `Fatal` survive every ascription in semantic metadata. Budget coverage and panic-boundary unwind safety remain independently checked, including when operational requests have been handled.

```ril
fn repeat(n: int, action: Action) -> () {
    if n > 0 { action(); repeat(n - 1, action) }
}
fn repeat_plain() -> () { repeat(2, plain) }
fn repeat_logged() @Log -> () { repeat(2, logged) }
-- fn erase_recursive() -> () { repeat(2, logged) } -- Error [E0612]

type StashingWorker = fn(^mut Entry) &up &^mut -> ()
type TemporaryWorker = fn(mut Entry) &up &mut -> ()
-- Open rows cannot make these parameter modes interchangeable.
```

#### Higher-Order Calls

```ril
fn apply<T, R>(value: T, f: fn(T) @& -> R) -> R { f(value) }
eff Logger { log(str) -> () }
fn logged_square(n: int) @Logger -> int {
    Logger::log("calculating")
    n * n
}
fn call_square() @Logger -> int { apply(5, logged_square) }
-- fn hidden_square() -> int { apply(5, logged_square) } -- Error [E0612]

let mut messages: []str = []
with Logger::log(message) -> {
    messages |> mut Array::push(message)
    resume ()
}
assert(call_square() == 25)
assert(messages == ["calculating"])
```

```ril
fn invoke_mut(mut f: fn() &up -> int) &mut -> int { f() }
let mut counter = create_counter(0)
let first = invoke_mut(mut counter)

fn apply_to_cell(mut cell: Cell, f: fn(mut Cell) &mut -> ()) &mut -> () {
    f(mut cell)
}
let mut cell = Cell.{ count: 0 }
apply_to_cell(mut cell, bump)
-- apply_to_cell(mut cell, \target -> ()) -- Error [E0407]: callback data mode differs
```

Forwarding preserves the contract above. Callback-handle authority and callback data-parameter modes remain distinct: an ordinary callback argument cannot invoke a mutable environment; that handle needs explicit `mut`.

### Return Construction, Access Modes, and Sources

A value-type result needs only `-> T`. Shared-object results distinguish the root from its contained references; all reception checks use the complete graph.

```ril
type Cell = .{ var count: int }
fn forward(new cell: Cell) -> new Cell { cell }
fn choose(flag: bool, new a: Cell, new b: Cell) -> new Cell {
    if flag { a } else { b }            -- Only the selected active path is returned
}
-- fn invalid(mut cell: Cell) &mut -> new Cell {
--     cell.count += 1
--     cell                           -- Error [E0546]: mut input has no construction qualification
-- }
```

```ebnf
ReturnType       ::= "->" [ ReturnMode ] TypeExpression
ReturnMode       ::= "infer" | "new" | ( "ref" | "^mut" ) "(" ReturnSources ")"
ReturnSources    ::= ValueName { "|" ValueName }
```

Root source names denote formal parameters. Metadata retains field and index paths. `|` lists possible entry sources. A `new expression` hands off construction authority at the [permitted receiving positions](#fresh-construction-parameters), preserving object identity and ending the old path. A lexical mode template may elaborate the handoff under [access-mode inference](#preserving-reception-and-forwarding). `-> infer T` requires [explicit `via` inputs](#access-mode-inference-with-via-and-infer) and retains the entire inferred result access modes, origins, and payload modes under the result rules below.

A declared `-> new T` supplies the return expression's construction context: a bare qualified source needs no repeated `new` marker. Check every normal result path, including tail blocks and result-producing `if`/`match` arms. Evaluate the selected operand once; after reception succeeds, prepare the return value and end each transferred active source and its derived accesses before cleanup. Failure never revives them (`E0549`). Locally created roots keep their construction-return rules, including any separately required retention and sharing annotations.

The construction context applies only to the current callable's return operands. Source authority, construction qualification, root privacy and graph isolation require their own proofs; unqualified borrowed/observed inputs fail with `E0546`. A compatible return also permits explicit `new x` for the same single handoff.

| Return form | Required guarantee / rejection |
| :--- | :--- |
| Value type `T` | Copy the value; no return-reference dependency. Actual writes/effects retain their obligations and required named annotations |
| Plain shared object `T` | Deeply immutable graph; immutable storage may be shared or eligible private construction published. Surviving writers fail with `E0535` |
| `new T` | Root constructed in this invocation, including verified factories, or lawfully handed onward from an active construction formal/local or verified storage extraction; preserve root write authority, actual allocation identity/history, and graph qualifications (`E0546`) |
| `ref(x) T` | Read-only root from formal `x`'s graph at call entry; a projected child still names only `x` (`E0545`) |
| `^mut(x) T` | Same entry-origin relation, with writable retention; require `^mut` parameter/argument (`E0528` for escaping ordinary `mut`). Root retention needs no duplicate `&^mut`; actual writes still require `&mut` |
| `ref(a \| b) T` / `^mut(a \| b) T` | Each root has one of the listed entry origins; contained dependencies and disjointness are checked separately |
| `&return{ref x, ^mut y}` | Possible contained dependencies, independent of root mode; scalar copies and unchanged contents inherited from the root add no item. Extra writable retention requires its `&^mut` annotation |

| Independent check | Requirement |
| :--- | :--- |
| Construction semantics | A nominal wrapper creates no root; `clone` supplies isolated construction. Forwarded construction consumes the old formal/local path under the [handoff rules](#fresh-construction-parameters); a declared `-> new T` supplies that return's handoff context |
| Complete graph | Independently prove publication or initial-storage eligibility using actual aliases and current source authority, including for locally constructed roots |
| Retention and state | Root return, actual writes, contained retention, other storage, and environment creation remain separate facts; named definitions spell their required annotations |
| Boundaries | Preserve observation stability, member modes, scoped/task lifetimes, and exclusivity; annotations extend none of them |

Result reception uses the [common prohibited exchanges](#binding-modes-and-storage-matrix), [shared-site markers](#shared-writable-authority), and [context-specific diagnostics](#monotonic-mode-degradation-and-anti-laundering-matrix). A fresh-storage input must independently prove its complete unpublished initial-reception eligibility. Entry-origin relations use actual call-entry graphs, never reachability introduced by later writes or a fabricated allocation inside the call.

```ril
type Cell = .{ var count: int }
type Box = .{ mut cell: Cell }

fn make() -> new Cell { Cell.{ count: 0 } }
fn same(cell: Cell) -> Cell { cell }
fn value(ref cell: Cell) -> int { cell.count }
fn take_and_zero(mut cell: Cell) &mut -> int {
    let count = cell.count
    cell.count = 0
    count
}
fn observe(ref box: Box) -> ref(box) Cell { box.cell }
fn share(^mut box: Box) -> ^mut(box) Cell { box.cell }
fn bump_alias(^mut cell: Cell) &mut -> ^mut(cell) Cell {
    cell.count += 1
    cell
}
let update: fn(^mut c: Cell) &mut -> ^mut(c) Cell = bump_alias -- Return retention + invocation writes
fn pick(flag: bool, ^mut a: Cell, ^mut b: Cell) -> ^mut(a | b) Cell {
    if flag { a } else { b }
}
-- fn duplicate(^mut x: Cell) &^mut -> ^mut(x) Cell { x }
-- Error [E0529]: root-return retention already has its required spelling
let getter: fn(ref box: Box) -> ref(box) Cell = observe
-- let erased: fn(ref box: Box) -> Cell = observe -- Error [E0534]: the live return relation cannot be erased

let immutable = make()                 -- Immutable publication at reception
let mut writable = make()              -- Initial writable reception
writable.count += 1
let same_immutable = same(immutable)    -- Tracked immutable sharing
-- let mut thawed = same(immutable)    -- Error [E0528]: an immutable return grants no writer

let mut box = Box.{ cell: Cell.{ count: 0 } }
let ref reader = observe(ref box)
let ^mut writer = share(^mut box)      -- Explicit shared reception
writer.count += 1
assert(reader.count == 1 && box.cell.count == 1)
-- let hidden = observe(ref box)       -- Error [E0535]: a live observer cannot become immutable
-- let mut stolen = observe(ref box)   -- Error [E0528]: a read-only return cannot grant writes
-- let mut hidden_writer = share(^mut box) -- Error [E0510]: missing shared-reception marker
```

A reception marker acknowledges the returned authority. Compare callable state/provenance obligations and check purity using the combined return-retention and invocation obligations. An explicit `&{}` requires that total to be empty.

| Branches | Return form |
| :--- | :--- |
| All roots constructed here or lawfully handed onward from active construction paths / verified storage handoffs, and writable | `new T`; the declared return context checks each branch's construction/transfer without repeated `new` operands; retain true origins, allocation history, and dependencies |
| All roots from non-construction entry parameters | `ref(a \| b) T`, or `^mut(a \| b) T` when every alternative permits writes |
| New root and existing immutable data | Plain `T` after lawful publication |
| New root and entry live reference | No bare mixed-root return; construct an explicit wrapper or result variant |
| Locally created root published elsewhere, returned writable | `new T` plus the required independent retention/state annotation |
| Locally created root published elsewhere, returned only through `ref` | Requires an explicit observer wrapper |
| Existing live root supplied only by a module binding/capture | Requires a wrapper or an explicit formal parameter. Immutable descriptors/data use plain `T` |

```ril
fn with_cell<R>(
    mut slot: .{ var mut cell: Cell }, create: bool,
    via action: fn(mut Cell) @& -> R,
) &mut -> R {
    if create { slot.cell = Cell.{ count: 0 } }
    action(mut slot.cell)
}
```

```ril
-- Call-site counterexamples; slot/create are caller values:
-- with_cell(mut slot, create, \ref cell -> cell.count)
-- Error [E0407]: this interface requires mut data; reading needs a ref-data interface
-- with_cell(mut slot, create, \mut cell -> { cell.count += 1; cell })
-- Rejected: ordinary R cannot export the live input or freeze its surviving writer

-- fn mixed(flag: bool, ref old: Cell) -> ref(old) Cell {
--     if flag { old } else { Cell.{ count: 0 } }
-- } -- Error [E0545]: mixed constructed/entry-live bare roots
```

| API shape | Static boundary |
| :--- | :--- |
| Temporary callback returning ordinary `R` | Same access and result guarantees on every retained path; callback, alias, escape, and effect checks remain |
| Construction result `new T` | Construction or lawful handoff, including verified owned-storage detachment; preserve sharing/history, without assuming privacy or isolation |
| Public ensure/add, then independent getter | Creation returns ordinary business data; the getter's result belongs to its own entry graph |
| Outer wrapper around those phases | Substitute all store/return history; insertion cannot make a fresh root part of the outer entry graph |

Run-time business choices operate under statically proved access modes and origins, including the distinction between construction and entry-live roots.

Verified interfaces retain root modes/history, contained origins, store/return relations and output correlations for checking and dependency invalidation. Higher-order/dynamic joins preserve only common guarantees; separation requires a verified relation. Opaque interfaces retain hidden-source facts in metadata. Return-mode/source erasure is `E0534`; parameter-label renaming also renames bound source names by position.

A generic signature must hold for every admitted instantiation under [definition checking](#generic-evidence-and-definition-checking); unresolved ordinary typing obligations cannot be deferred to a first successful call. Use a uniformly valid plain result, sufficient constraints, or a qualified construction or `via` family. Forwarding construction requires eligible ordinary shared-object instantiations and a lawful handoff through a declared construction return context, explicit construction operand or checked template dependency. `-> infer T` infers and retains the result qualifications; handoff context follows those separate rules. Foreign exchange and resource authority follow their declared contracts.

```ril
-- Cell and Box have the preceding declarations.
fn wrap(ref box: Box) &return{ref box} -> new .{ ref item: Cell } {
    .{ ref item: box.cell }
}
let mut source = Box.{ cell: Cell.{ count: 0 } }
let ref packet = wrap(ref source)
source.cell.count += 1
assert(packet.item.count == 1)
-- let hidden = wrap(ref source)       -- Error [E0535]: the new wrapper still contains a live reference

-- fn false_new(cell: Cell) -> new Cell { cell }
-- Error [E0546]: an immutable parameter is neither a new root nor a writable return path
-- fn false_copy(ref cell: Cell) -> new Cell { cell }
-- Error [E0546]: the result aliases its observed input
-- fn mixed(flag: bool, cell: Cell) -> new Cell {
--     if flag { Cell.{ count: 0 } } else { cell }
-- }
-- Error [E0546]: the existing immutable alternative is not a writable new root
-- fn temporary_writer(mut cell: Cell) &^mut -> ^mut(cell) Cell { cell }
-- Error [E0528]: call-scoped mut authority cannot survive the call
-- fn wrong_source(ref a: Cell, ref b: Cell) -> ref(a) Cell { b }
-- Error [E0545]: the return's b origin is absent from the declared relation
```

```ril
-- Cell has the preceding schema.
type Holder = .{ mut item: Cell }
type Slot = .{ var mut child: Cell }

fn pack(^mut x: Cell) &^mut &return{^mut x} -> new Holder {
    Holder.{ item: ^mut x }
}
fn return_and_store(mut dst: Slot, ^mut x: Cell) &^mut -> ^mut(x) Cell {
    dst.child = ^mut x                 -- Extra path beyond the root return
    x
}
fn install(mut dst: Slot) &^mut -> new Cell {
    let mut child = Cell.{ count: 0 }
    dst.child = ^mut child
    child                             -- Still writable; already shared outside
}

let mut source = Cell.{ count: 0 }
let ^mut packed = pack(^mut source)
packed.item.count += 1
-- let hidden = pack(^mut source)      -- Error [E0535]: live contents forbid immutable publication

let mut slot = Slot.{ child: Cell.{ count: 0 } }
let ^mut installed = install(mut slot)
installed.count += 1
assert(slot.child.count == 1)
-- let hidden = install(mut slot)      -- Error [E0535]: a surviving writer prevents publication
-- let mut hidden = install(mut slot)  -- Error [E0510]: shared result needs explicit reception
let mut exclusive_cells: [mut]Cell = []
exclusive_cells |> mut Array::push(new Cell.{ count: 0 })
-- exclusive_cells |> mut Array::push(install(mut slot)) -- Error [E0535]: new root is not an unpublished storage input
let mut cells: [^mut]Cell = []
cells |> mut Array::push(^mut installed)
cells[0].count += 1

fn frozen() -> Cell { let cell = Cell.{ count: 0 }; cell }
-- fn false_frozen() -> new Cell { let cell = Cell.{ count: 0 }; cell }
-- Error [E0546]: publication ended root write authority
-- fn false_entry(mut dst: Slot) &^mut -> ^mut(dst) Cell {
--     let mut child = Cell.{ count: 0 }
--     dst.child = ^mut child
--     child
-- }
-- Error [E0545]: writing a new object into dst does not make it an entry-provided root
```

```ril
-- Cell and Slot have the preceding schemas.
fn install_observer(mut dst: Slot) &^mut -> new .{ ref item: Cell } {
    let mut child = Cell.{ count: 0 }
    dst.child = ^mut child
    .{ ref item: child }               -- Explicit observer wrapper, not a bare read-only new root
}
let mut slot = Slot.{ child: Cell.{ count: 0 } }
let ref observed = install_observer(mut slot)
slot.child.count += 1
assert(observed.item.count == 1)

type Step = fn() &up -> int
-- fn erase_return(^mut f: Step) &{} -> ^mut(f) Step { f }
-- Error [E0534]: the closed state/provenance row cannot erase root-return retention
```

### Termination and halt Contracts

```ril
fn countdown(n: int) -> int {
    if n <= 0 { 0 } else { countdown(n - 1) }
}                                               -- Inferred @Diverge, including decreasing recursion
fn spin() -> int { loop {} }                     -- Pure, inferred @Diverge; legal
fn forward_spin() -> int { spin() }              -- Inferred @Diverge propagates without source annotation
fn done() -> int { 7 }                           -- No Diverge; halt is optional
halt fn checked() -> int { done() }              -- Unmarked helpers are admissible
-- halt fn unchecked() -> int { countdown(5) }   -- Error [E0820]: residual Diverge
```

`Diverge` is a prelude-provided, compiler-owned implicit effect label for possible infinite computation, including cases where finiteness is unknown. It has no operations, cannot be written in source `@` or `eff` annotations (`E0620`), and cannot be targeted by an operation arm (`E0621`). It participates in semantic interfaces (`@[OpEffects] + Diverge + Panic + Fatal`); there is no separate `Finite` / `MayDiverge` callable judgment. Budget exhaustion is ordinary result data, not `Diverge`.

| Construct / contract | Diverge rule |
| :--- | :--- |
| General recursion, including mutual and indirect invocation cycles | Introduce `Diverge` on potentially repeating invocations and propagate it, subject only to a covering budget boundary; decreasing arguments alone do not exempt recursion |
| `while` / `loop` | Introduce `Diverge`; counter progression, a finite-looking condition, or modular wrap supplies no exemption |
| `for`, finite mapped comprehensions, sequential finite collection combinators | No intrinsic `Diverge`; propagate iterator, body, and callback obligations |
| Calls, defaults, branches, handlers, resumption, cleanup, required child completion | Propagate the obligations of the computation actually required, under the existing static branch-pruning rules |
| Unknown callback through `fn(...)` | Preserve its symbolic effect dependency, including possible `Diverge`; satisfying a `halt` declaration requires concrete `Diverge`-free instantiation or a covering `diverge_budget` |
| Callable creation or return | Check current capture/publication separately; the body's `Diverge` remains latent until invocation |
| Finite language primitive | Omit `Diverge` only under its specified finite contract and callback dependencies |
| `diverge_budget` | The only primitive that removes `Diverge` from a covered invocation; see [finite evaluation](#finite-evaluation-with-diverge) |

Invocation-cycle analysis includes callable-valued members, recursive types, mutable/live storage, captured environments, and handler re-entry. A cycle cannot establish its own absence of Diverge from its written signatures. Use verified contracts and established acyclic invocation dependencies; unresolved potentially cyclic dependencies introduce Diverge. Reading inert cyclic data alone introduces none. A verified budget can discharge a cyclic invocation within its protected action; the containing function need not retain that Diverge. Analyze definitions and their dependencies conservatively; neither evaluation on sample inputs nor arithmetic/structural descent removes an inferred Diverge. An unreachable static branch contributes no obligation.

Purity requires absence of outward operational effects and mutable, live, capturing, or foreign state/provenance obligations after lawful handling and local discharge; read-only `&up(sub){...}` and `&up{...}` items resolved to verified deeply immutable `.ril` bindings (`meta let`, immutable `.ril` module `let`, and immutable enclosing `let` / plain parameters) are permitted when explicitly annotated (`E0510` if omitted), and the non-operational Diverge label may remain. Thus a pure function may diverge. `halt` additionally requires absence of Diverge for every admitted invocation, including all admitted parameter-default and signature-guard evaluations. Residual Diverge is `E0820`; operational effects or mutable, live (`ref` / `&mut` / `&^mut`), capturing (`&capture`), or `.d.ril` `pub let` external state obligations are `E0821`. Local mutation, temporary environments, and completely handled finite local effects remain allowed. Explicit caller-supplied arguments retain their separate caller obligations.

`halt` is an optional developer assertion on `fn`, `meta fn`, or type functions; callers and helpers need not carry the marker. Ordinary functions, type functions, and compile-time roots may retain Diverge. Static evaluation still has its [compiler budget](#pure-type-functions-and-result-restrictions). The marker neither installs a budget nor changes the declaration's call family, and cannot silently narrow explicitly promised inputs. Higher-order requirements use ordinary effect/state row constraints; no additional hidden termination contract is introduced.

Finite completion includes normal/early return, panic, and terminating delimited abort. It guarantees neither a successful result nor a wall-clock bound or external scheduling progress. `never` means no normal continuation: panic can be finite while `loop {}` carries Diverge.

```ril
halt fn local_sum(values: []int) -> int {
    var sum = 0
    for values as value { sum += value }
    sum
}                                               -- Local writes discharge; unbounded int addition is exact

eff ReadValue { get() -> int }
halt fn local_read() -> int {
    with ReadValue::get() -> resume 7
    ReadValue::get()
}                                               -- Internal handling remains pure and finite
-- halt fn bad_io() @Fiber -> () { Fiber::yield() }     -- Error [E0821]: outward effect

meta let MAX_RETRIES = 3
let ALLOWED_MODES = ["fast", "safe"]
halt fn max_attempts() &up(sub){MAX_RETRIES, ALLOWED_MODES} -> int {
    MAX_RETRIES + len(ALLOWED_MODES)                    -- OK: read-only deeply immutable .ril bindings
}

var outside_count = 0
-- halt fn bad_read() &up(sub){outside_count} -> int { outside_count } -- Error [E0821]: mutable origin
-- halt fn bad_state() &up(sub){mut outside_count} -> () { outside_count += 1 }
-- Error [E0821]: outward state/provenance obligation

fn invoke(action: fn() -> ()) -> () { action() }
fn done() -> () {}
fn forever() -> () { loop {} }
invoke(done)                                    -- Symbolic callback instantiated with finite 'done'
invoke(forever)                                 -- OK: fn() -> () permits Diverge
halt fn call_known() -> () { invoke(done) }     -- OK: compiler summary resolves 'done' as Diverge-free
-- halt fn call_spin() -> () { invoke(forever) } -- Error [E0820]: instantiated callback has Diverge
-- halt fn call_unknown(cb: fn() -> ()) -> () { cb() } -- Error [E0820]: arbitrary fn() -> () may diverge
halt fn call_bounded(cb: fn() -> ()) -> Result<(), BudgetError> {
    with diverge_budget(1_000)
    cb()                                        -- OK: explicit budget discharges callback Diverge
}

halt fn make_later() -> (fn() -> int) { spin }  -- Only the later invocation has Diverge
-- halt fn run_later() -> int { make_later()() } -- Error [E0820]: its later invocation still diverges
-- halt fn bad_default(value: int = spin()) -> int { value } -- Error [E0820]: default may diverge
```

```ril
fn spin() -> int { loop {} }
let actual: fn() -> int = spin                  -- fn(...) permits Diverge; semantic summary retains it
-- halt fn bad_alias() -> int { let f: fn() -> int = spin; f() } -- Error [E0820]: semantic summary retains Diverge
-- type BadHaltArrow = halt fn() -> ()          -- Error [E0120]: 'halt' is a declaration modifier, not a type
-- fn explicit_div() @Diverge -> int { spin() } -- Error [E0620]: Diverge cannot be written in source
-- with Diverge() -> 0                          -- Error [E0621]: Diverge has no operation to handle
```

Declaration `halt` (`halt fn`, `halt meta fn`, `halt type`) requires outward purity (`E0821`) and absence of `Diverge` (`E0820`). Named definitions and `fn(...)` callable types retain or permit inferred `Diverge` in semantic metadata while `@` governs operational effects (`@{}` closes operational effects only). Ordinary handler installation, source annotations, ascription, and compiler resource limits cannot remove `Diverge`.

### Parameter Modes, Caller Obligations, and Defaults

```ril
type Cell = .{ var count: int }
fn inspect(cell: Cell) -> int { cell.count }
fn observe(ref cell: Cell) -> int { cell.count }
fn bump(mut cell: Cell) &mut -> () { cell.count += 1 }
fn retain(^mut cell: Cell) -> ^mut(cell) Cell { cell }

let immutable = Cell.{ count: 0 }
assert(inspect(immutable) == 0)
let mut cell = Cell.{ count: 0 }
bump(mut cell)
cell |> mut bump()                     -- Supplies mut, not ^mut
assert(cell |> ref observe() == 2)     -- Supplies call-time ref observation
let ^mut alias = cell |> ^mut retain()
alias.count += 1
assert(cell.count == 3)                -- Retained alias survives the call

-- inspect(cell)                      -- Error [E0535]: surviving writer
-- observe(cell)                      -- Error [E0405]: missing ref marker
-- inspect(mut cell)                  -- Error [E0406]: wrong mode
let ref observed = cell
-- bump(mut observed)                 -- Error [E0520]: no write authority
-- let bad: fn(Cell) &mut -> () = bump -- Error [E0407]: parameter modes differ
```

| Parameter / caller form | Boundary rule |
| :--- | :--- |
| `p: T` / `expression` or `\|>` | Ordinary immutable reception, including publishable fresh data |
| `ref p: T` / `ref expression` or `\|> ref` | Observe shared-object data or a callable environment for the call; preserve immutable/live origins |
| `mut p: T` / `mut target` or `\|> mut` | Pinned writable shared-object/environment access; ends at return |
| `^mut p: T` / `^mut target` or `\|> ^mut` | Pinned writable shared-object/environment access; may retain a writer |
| `new p: T` / `new expression` or `\|> new` | Unpublished ordinary construction authority; explicit handoff ends the old construction paths |

The ordinary `ref`/`mut`/`^mut` modes cover named/anonymous functions, callable types, effect operations/handlers, and generic/built-in instantiations. Fresh construction parameters add the verified `new` path for ordinary Ril callables and recognized storage inputs; effect and foreign restrictions remain explicit. [Fresh storage inputs](#homogeneous-storage-authority) receive construction authority before ordinary immutable publication. A wrapper must declare `new` or an admitted preserving `via` input to retain that path; an ordinary immutable wrapper still publishes data. `via` is not admitted on effect/handler or foreign boundary parameters (`E0412`).

| Invalid use | Diagnostic |
| :--- | :--- |
| Value-type `ref` / `mut` / `^mut` parameter or argument | `E0401` |
| Rebind a mutable parameter | `E0502` |
| `var` parameter | `E0403` |
| Missing / wrong explicit argument mode | `E0405` / `E0406` |
| Non-addressable `mut` / `^mut` argument | `E0410` |
| Ineligible `new` parameter type, context, or generic instantiation | `E0411` |
| Ineligible construction expression or misplaced `new` handoff | `E0548` |
| Use of an ended construction path or its derived reference path | `E0549` |
| Callable parameter modes differ | `E0407` |
| Omit a required retained-writer annotation on a named definition, or omit an independently required sharing marker | `E0510`; anonymous inference never supplies absent authority |

Concrete modes match exactly through forwarding and subtyping. A lexically bound `via` parameter or checked dependent mode permits template operand elaboration; ordinary callers supply the concrete marker. Access follows the [access-mode tables](#binding-modes-and-storage-matrix), [exclusivity](#law-of-exclusivity-and-cross-argument-disjointness) and source lifetime rules.

```ril
-- Cell and observe have the preceding declarations.
var mut selected = Cell.{ count: 0 }
selected.count += 1
assert(observe(ref selected) == 1)    -- Call-time observation of the current object
selected = Cell.{ count: 2 }
-- let ref bad = selected            -- Error [E0531]: no persistent pinned origin
```

Call-time `ref` parameters may observe reference expressions, including current objects reached through reassignable paths. They preserve existing immutable or pinned live origins, but cannot establish a pinned mutable root for persistent `ref` handles.

| Callback declaration | Handle authority |
| :--- | :--- |
| `f: fn(mut T) -> R` | Immutable handle; `mut` describes its data parameter |
| `ref f: F` | Observe a live environment |
| `mut f: F` | Write the environment; bind mutable inline closures to writable handles before passing them |

```ebnf
ParameterMode    ::= "ref" | "mut" | "^mut" | "new" | "via"
```

Mutable modes do not apply to static key arguments.

#### Fresh Construction Parameters

A `new value: T` parameter receives unpublished construction authority for ordinary shared-object data or movable endpoint carriers admitted by [`Movable`](#task-handles-movable-guard-and-combinators) through an explicit `new expression` handoff. The mode is available to verified named and anonymous Ril functions, their callable types, and the storage inputs below. Handoffs preserve object identity and consume the qualified source path.

```ril
type Cell = .{ var count: int }
fn append_cell(mut target: [mut]Cell, new cell: Cell) &mut -> () {
    target |> mut Array::push(new cell)
    -- target |> mut Array::push(new cell) -- Error [E0549]: the old construction path has ended
    -- let count = cell.count         -- Error [E0549]: reads through that path have ended too
}
fn forward_cell(new cell: Cell) -> new Cell {
    cell                              -- Return annotation supplies handoff; no allocation occurs here
}
fn normalize_cell(new cell: Cell) &mut -> new Cell {
    cell.count += 1                   -- Writes before handoff retain parameter-write obligations
    cell
}
let mut cells: [mut]Cell = []
let mut prepared = Cell.{ count: 0 }
    |> new normalize_cell
    |> new forward_cell
append_cell(mut cells, new prepared)
cells[0].count += 1
```

| Construction parameter concern | Normative rule |
| :--- | :--- |
| Eligible type (`E0411`) | Types admitted by [`Movable`](#task-handles-movable-guard-and-combinators): ordinary shared-object data, single-owner channel endpoints, and fixed-`mut` endpoint carriers. Value types, task/scope authority, non-movable resources, callable roots, and any graph containing retained callable environments or non-movable authority are excluded; wrapping, opacity, or an outer fresh root cannot hide them |
| Eligible expression (`E0548`) | Prove complete initial-reception eligibility: eligible constructed writable regions are isolated from pre-existing writable regions and have no surviving outside writer, observer, or active environment. Preserve immutable constituent sharing, aliases, cycles, and member schemas |
| Existing bindings (`E0548`) | Handoff requires a fixed writable local with active qualification from [checked initial reception](#construction-qualified-locals-and-mode-preserving-reception). Immutable/observed, borrowed, published, reassignable or otherwise unqualified bindings are ineligible |
| Forwarding source | An active construction formal/local, verified eligible construction expression, or checked storage handoff may be handed onward. Projection does not split construction authority; only a verified consuming decomposition establishes separately eligible payload paths |
| Use before handoff | Construction formals and qualified locals are fixed: no rebinding (`E0502`). Reads, temporary `ref` observations, and schema-authorized writes are allowed while active; actual parameter-derived writes require `&mut`. Observation aliases remain tied to the same construction authority |
| Handoff | Evaluate each explicit `new` argument operand once in ordinary argument order. When that operand passes reception checks, transfer authority to its prepared argument and end all accesses through the old formal/local and its derived reference paths before evaluating later arguments or defaults. The callee receives that one active construction path; copied scalar values remain usable. A later argument failure discards the prepared transfer without reviving the old path. A construction initializer/return transfers to its prepared receiver/value before subsequent cleanup |
| Ended use (`E0549`) | Reject any possible read, write, forwarding, alias use, or capture access through an ended construction path. Branches and loops must establish that the path is active at each use; a path consumed on a possible branch is not proved active after the join |
| Outside aliases | An outstanding derived reference or environment cannot remain independently usable across a handoff. Alias, lifetime, exclusivity, and task-boundary checks remain required; invalidating a source path does not invalidate or grant authority to unrelated established bindings |
| Return | Declared `-> new T` checks and hands onward a bare qualified source. Forwarding an existing path through an inferred construction result requires an explicit construction operand or checked template dependency. Return preparation ends transferred sources and derived accesses before cleanup, including on failure. Locally constructed roots follow their construction-return rules |
| Publication and sharing | Immutable publication or independent escape/sharing of the qualifying path ends initial-forwarding eligibility. Temporary observation/borrowing may preserve it under the alias checks. Deliberate `^mut` sharing still requires its source authority, retention annotations, and markers; it cannot be disguised as another `new` reception. A root `new` handoff alone adds no `&^mut`; already acknowledged shared constituents retain their separate graph obligations |
| Omitted transfer | A construction parameter is affine: it may be discarded on completion only subject to outstanding Result-inspection and other ordinary completion obligations. Failure or abort does not return construction authority to an ended caller path. Any ordinary immutable result still must satisfy the usual whole-graph publication checks |
| Higher-order use | Callable parameter modes must match (`E0407`); aliases, imports, ascriptions, and callback forwarding preserve construction-path consumption and result-source metadata. An ordinary parameter or an open effect or state/provenance row cannot substitute for `new` mode |
| Defaults | A `new` parameter cannot have a default (`E0404`); an actual handoff requires its explicit argument marker |
| Effect/foreign boundary | Construction input is prohibited on effect-operation parameters and handler binders (`E0411`), and bodyless foreign calls (`E0908`). These boundaries use their declared temporary modes |
| Phase | This is a run-time construction mode. Static/meta/type computation has no construction-input mode; a `new` parameter in a static declaration is `E0411`, and run-time construction handoffs are not static computations |

A `new expression` handoff requires a matching construction argument, compatible construction return, qualified fixed writable local initializer, template-dependent receiver, or verified typed-storage reception. Record/tuple/array/map initializers require a receiver proving matching construction eligibility; untyped immutable reception is ineligible. [Fixed writable locals](#construction-qualified-locals-and-mode-preserving-reception) retain eligible construction paths as provenance; `let via` receives access modes dependent on lexically bound mode parameters. Missing and wrong ordinary argument modes are `E0405` and `E0406`; a construction operand outside a receiving position is `E0548`. Ordinary immutable reception publishes data and ends forwarding eligibility. Allocations and handoffs retain their true identities.

In a caller with an active construction formal `cell`, `f(new cell, cell.count)` and `f(new cell, new cell)` both use an ended path in their second argument (`E0549`). Preparing all arguments before invoking `f` does not duplicate construction authority or defer its consumption.

For a generic `new value: T`, admitted instantiations must satisfy [`Movable`](#task-handles-movable-guard-and-combinators); `[mut]T` and `[^mut]T` storage remain restricted to `SharedObject`. An ineligible concrete parameter type or generic instantiation is `E0411`. Structural bounds may establish ordinary shared-object or movable shape. Check the definition for every admitted instantiation and full graph eligibility at each handoff.

```ril
-- Cell, append_cell, and forward_cell have the preceding declarations.
let immutable = Cell.{ count: 0 }
let mut established = Cell.{ count: 0 }
established.count += 1
let mut cells: [mut]Cell = []
append_cell(mut cells, new Cell.{ count: 0 })
append_cell(mut cells, new established)       -- Qualified concrete local; no via needed
-- let count = established.count             -- Error [E0549]
let mut published = Cell.{ count: 0 }
let ^mut alias = published
alias.count += 1
-- append_cell(mut cells, Cell.{ count: 0 }) -- Error [E0405]: missing construction argument marker
-- append_cell(mut cells, new immutable)    -- Error [E0548]: immutable publication cannot be undone
-- append_cell(mut cells, new published)    -- Error [E0548]: independent sharing ended qualification
-- fn scalar(new value: int) -> int { value } -- Error [E0411]: new parameters require ordinary shared-object data
fn forwarding<T>(new value: T) -> new T { value }
let mut cell = forwarding(new Cell.{ count: 0 })
cell.count += 1
-- let value = forwarding<int>(new 1)   -- Error [E0411]: ineligible generic instantiation
```

A `-> new T` result guarantees construction or lawful handoff; its root may have been shared under the required retention annotations. Construction input additionally requires the complete reception proof. Verified summaries distinguish roots allocated in this invocation, received through construction inputs, and detached by checked storage handoff, preserving entry origins, allocation identity, dependencies and mode history. Prove allocation in this invocation, initial eligibility, root privacy and disjointness independently where required.

#### Homogeneous Storage Authority

Storage containers define homogeneous element authority statically (`[]T`, `[mut]T`, `[^mut]T`, `[ref]T`). `[via]T` requests a family of these homogeneous schemas. Ordinary functions express these dependencies through access-mode inference and verified managed-storage primitives with explicit graph and mutation rules:

```ril
type Cell = .{ var count: int }
fn copy_cell(cell: Cell) -> new Cell { clone(cell) }
fn build_cell() -> new Cell {
    let mut cell = Cell.{ count: 0 }
    cell.count += 1
    cell
}

-- 1. Exclusive mutable container: [mut]T
let original = Cell.{ count: 1 }
let mut owned_cells: [mut]Cell = []
owned_cells |> mut Array::push(new clone(original))       -- OK: verified construction handoff
owned_cells |> mut Array::insert(0, new Cell.{ count: 2 }) -- OK: direct construction handoff
owned_cells |> mut Array::push(new copy_cell(original))   -- OK: verified eligible return
owned_cells |> mut Array::push(new build_cell())          -- OK: verified eligible return
owned_cells[0].count += 1                         -- OK: [mut]Cell grants exclusive interior writes
owned_cells[1].count += 1
owned_cells[2].count += 1
owned_cells[3].count += 1
assert(original.count == 1 && owned_cells[0].count == 3 && owned_cells[3].count == 2)

-- Independent immutable snapshot; the original writable graph remains usable:
let snapshot = clone(ref owned_cells)
owned_cells[0].count += 1
assert(snapshot[0].count == 3 && owned_cells[0].count == 4)
-- snapshot[0].count += 1                        -- Error [E0520]: immutable reception removes effective writes
```

```ril
-- 2. Immutable container ([]T) vs Shared container ([^mut]T) vs Observation container ([ref]T)
let mut shared = Cell.{ count: 1 }

-- Immutable container: []Cell holds deeply immutable elements
let mut immut_cells: []Cell = []
immut_cells |> mut Array::push(Cell.{ count: 0 })     -- OK: stores immutable data
-- immut_cells[0].count += 1                      -- Error [E0520]: []Cell elements are immutable
-- immut_cells |> mut Array::push(ref shared)     -- Error [E0406]: immutable container rejects references

-- Shared mutable container: [^mut]Cell holds elements with active or potential outside writing aliases
let mut shared_cells: [^mut]Cell = []
shared_cells |> mut Array::push(^mut shared)          -- OK: explicit ^mut acknowledgment; requires &^mut
shared_cells[0].count += 1
assert(shared.count == 2)

-- Live observation container: [ref]Cell holds read-only observation views
let mut view_cells: [ref]Cell = []
view_cells |> mut Array::push(ref shared)             -- OK: explicit read-only live observation view
-- view_cells[0].count += 1                       -- Error [E0520]: ref view grants no writes
-- view_cells |> mut Array::push(shared)          -- Error [E0405]: missing ref argument marker
```

```ril
-- 3. Observation Subsumption: Read-only observation context statically covers write authorities
fn inspect_all(ref arr: [ref]Cell) -> int {
    var total = 0
    for arr as ref item { total += item.count }
    total
}

-- Calling read-only inspection statically subsumes [mut]Cell and [^mut]Cell without runtime coercion
let mut test_cells: [mut]Cell = []
test_cells |> mut Array::push(new Cell.{ count: 5 })
assert(inspect_all(ref test_cells) == 5)          -- OK: write authority statically inactive during ref call
```

| Container authority | Push input | Pop receiver | Successful `Some` payload |
| :--- | :--- | :--- | :--- |
| **`[]T`** | `item: T` | `mut xs` | Ordinary immutable / copied T |
| **`[mut]T`** | `new item: T` | `mut xs` | Construction handoff of T, only with a verified detach proof |
| **`[^mut]T`** | `^mut item: T` | `^mut xs` | Retained writer with entry origin xs; contained-retention obligation |
| **`[ref]T`** | `ref item: T` | `mut xs` | Observation with entry origin xs and all original lifetime/pinning facts |

Push changes the container through `mut`. Retained input adds its required state/provenance annotation. Pop changes structure, and a shared payload requires `^mut` receiver authorization and `&^mut`. A concrete pop signature declares the newly constructed Option root with `-> new ?T` and spells the required contained-source annotations. A pop template with a `[via]T` receiver type can use `-> infer ?T`. In both forms, the single unnamed payload rule preserves variant-guarded payload modes and provenance. Element access follows the declared storage schema, true source authority and exclusivity checks.

User-defined collections such as `ExclusiveVec<T>` and `SharedRegistry<T>` compose the same verified storage primitives and mode templates.

#### Verified Storage Handoffs

```ril
type Cell = .{ var count: int }
let mut cells: [mut]Cell = []
cells |> mut Array::push(new Cell.{ count: 0 })
let mut pending = Array::pop(mut cells)
match pending {
    Some(cell) -> cells |> mut Array::push(new cell),
    None -> (),
}
-- match pending { ... }                     -- Error [E0549]

let mut shared: [^mut]Cell = []
let mut source = Cell.{ count: 1 }
shared |> mut Array::push(^mut source)
-- Array::pop(mut shared)                    -- Error [E0406]: retention needs ^mut receiver
let ^mut result = Array::pop(^mut shared)
match result { Some(cell) -> { cell.count += 1 }, None -> () }
```

A checked managed-slot extraction establishes one active construction path only when its summary proves an eligible ordinary shared-object region separated from the remaining container and every independently usable outside writer, observer, or environment. Preserve immutable sharing, internal aliases/cycles, schemas, allocation identity, and scope/task restrictions. Distinct indices, `new`, `[mut]T`, or last use alone prove nothing.

Check summary preconditions against actual origins at every call, requiring established static proofs. Shared edges are permitted when the detach proof succeeds. Slot removal and transfer preparation preserve initialized storage and one active path. A detached root retains its allocation identity and requires a complete subsequent reception proof. Later local handoff requires [retained construction qualification](#construction-qualified-locals-and-mode-preserving-reception).

Prepare arguments before the callee body: `new` ends the caller path before resize/allocation, including on later failure. Resize preserves element schemas and graph facts while performing its specified mutation and allocation.

#### Default Parameters and Named Arguments

```ril
fn pair(a: int = 1, b: int = 2) -> (int, int) { (a, b) }
assert(pair(b: 20, 10) == (10, 20))
assert(pair(a: 10, 20) == (10, 20))
-- pair(10, a: 20)                     -- Error [E0325]: a is already bound
```

- Named and anonymous parameters share the same default rules. Defaults permit no residual operational effects and no mutable, live, or `.d.ril` external state obligations (`E0409`); read-only deeply immutable `.ril` `&up(sub){...}` and `&up{...}` origins are permitted and join the caller's contract when evaluated, and implicit Diverge is allowed and propagates when evaluated. A `halt` definition must also exclude Diverge in every admitted default. `mut`/`^mut`/`new`/`via` defaults are forbidden (`E0404`). A `ref` default is received in its declared mode without a caller token; explicit supplied arguments still require `ref`. Earlier `ref` parameters do not exempt a later ordinary default from immutable reception.
- Explicit arguments evaluate in written left-to-right order; omitted defaults follow in parameter order. A default may use earlier parameters, not itself or later parameters.
- Bind arguments in written order: a positional argument selects the first unbound parameter in declaration order; a named argument selects its named parameter. Selecting an already bound parameter is `E0325`. Binding selection does not reorder evaluation.
- Function generic defaults are prohibited (`E0317`).

```ril
type Reader = fn() &up -> int
fn choose(value: int, reader: Reader = \-> value) -> Reader { reader }
let first = choose(7)
let second = choose(9)                 -- Default reevaluated for each omitted argument
assert(first() == 7 && second() == 9)

fn publish(value: int) &capture -> Reader { choose(value) }
-- fn hidden(value: int) -> Reader { choose(value) } -- Error [E0510]: caller publishes the new environment

let pair = \a: int, b: int = a -> (a, b)
let alias = pair
assert(alias(b: 4, 3) == (3, 4))       -- Anonymous defaults and labels survive this alias
```

Defaults run anew in the caller before callee entry, using declaration scope and earlier read-only arguments. New environments/retained handlers belong to that preparation; forwarding them adds no callee `&capture`, but publication beyond the caller does. Check their origins, access modes, lifetimes and [termination/`halt` obligations](#termination-and-halt-contracts). Preparation adds no frame or entry charge; its calls, loops, handler entries and resumptions use all active budgets.

An unknown parameter label is `E0339`; a non-callable callee is `E0338`. Missing or excess ordinary arguments use `E0314` after accounting for names and defaults. Nullary variant parentheses use `E0353`. Positional and named arguments may be interleaved under the binding rules above.

```ril
fn connect(host: str, port: int = 8080) -> str { "{host}:{port}" }
-- connect("localhost", prot: 80)    -- Error [E0339]: unknown parameter label
-- let call = 42()                   -- Error [E0338]: int is not callable
let connected = connect("localhost", port: 80) -- OK

-- fn bad_default(first: int = second, second: int = 1) -> int { first + second }
-- Error [E0408]: default refers to a later parameter
fn good_default(first: int, second: int = first) -> int { first + second } -- OK
eff DefaultSource { read() -> int }
-- fn impure_default(value: int = DefaultSource::read()) @DefaultSource -> int { value }
-- Error [E0409]: default has a residual effect even though the function declares it
```

References from a parameter default to itself or a later parameter are `E0408`. Other unresolved names retain `E0204`; generic-default forward references retain `E0320`. A parameter default with a residual operational effect or a mutable, live, or `.d.ril` external state obligation is `E0409`, even if the enclosing callable declares that obligation. Read-only deeply immutable `.ril` `&up(sub){...}` / `&up{...}` origins and Diverge alone are not impurity errors. Pure defaults referring to earlier parameters remain valid.

```ril
fn create_server(host: str, port: int = 8080, enable_tls: bool = true) -> str {
    "{host}:{port} (tls={enable_tls})"
}
let address = create_server("localhost", enable_tls: false)
-- create_server("localhost", host: "duplicate") -- Error [E0325]: duplicate argument
```

```ril
fn identity(value: int = 1) -> int { value }
let direct_alias = identity
assert(direct_alias() == 1)
let renamed: fn(other: int) -> int = identity
let unnamed: fn(int) -> int = identity
assert(renamed(other: 2) == 2)
-- renamed(value: 2)                   -- Error [E0339]: source label is not the call-site label
-- renamed()                          -- Error [E0314]: callable types carry no default expressions
-- unnamed(value: 2)                   -- Error [E0339]: unnamed parameter has no label
-- unnamed()                          -- Error [E0314]
assert(unnamed(2) == 2)
```

| Callable use | Labels and defaults |
| :--- | :--- |
| Direct named call / anonymous callable / unannotated value alias | Preserve that function's labels, defaults, and lexical default environment |
| Callable-type ascription or typed parameter/field/element/return position | Use the destination signature's labels by position; no source defaults are imported |
| Unnamed type parameter position | Positional calls only; a supplied label is `E0339` |
| Callable alternatives | Retain a label only when every alternative has it at that position; retain a default only when every alternative preserves the same declaration's default and environment |
| Subtyping / type identity | Labels are call-site metadata, not additional type-identity constraints; parameter modes, types, and callable contracts remain checked |

Callable types admit no default-expression syntax. An ascription may rename labels by position, but never changes the called body, parameter order, access modes, effects, or provenance. A call that uses a preserved default retains that default's evaluation, termination, and dependency checks. Duplicate labels in one signature are `E0203`.

### Anonymous Functions, Trailing Closures, and Projection Accessors

```ebnf
AnonFnExpr    ::= "\" [ AnonParams ] [ EffectAnnot ] [ StateAnnot ] "->" ( Expression | Block )
AnonParams    ::= AnonParam { "," AnonParam } [ "," ]
AnonParam     ::= [ ParameterMode ] ValueName [ ":" TypeExpression ] [ "=" Expression ]
AccessorExpr  ::= "\" AccessorNav AccessorField { AccessorNav AccessorField }
AccessorNav   ::= "." | "?."
AccessorField ::= FieldLabel | TupleIndex
```

- **Unary Desugaring Equivalence**: An `AccessorExpr` evaluates to a unary pure function projecting properties from its argument:
   - `\.field` desugars to `\x -> x.field`
   - `\.0` desugars to `\x -> x.0`
   - `\.field?.subfield` desugars to `\x -> x.field?.subfield`
   - `\?.field` desugars to `\x -> x?.field`
- **Product Projection**:
   - `FieldLabel` statically projects named fields from records (`.{...}`), nominal wrappers, or refined named variants. Unknown fields trigger `E0336`.
   - `TupleIndex` statically projects 0-indexed positional components from tuples (`(T0, T1, ...)`) or refined positional variant payloads ($S|_V$). Positional indices are statically checked at compile time against tuple arity $n$ ($0 \le i < n$). Out-of-bounds indices trigger `E0312`.
- **Safe Navigation Propagation**:
   - If any navigation segment uses safe navigation `?.`, evaluation short-circuits to `None` when the intermediate receiver is `None`. The resulting accessor closure return type is automatically lifted into `?T`.
- **Collection Projection Restriction**:
   - Collections (arrays `[]T`, maps `[K: V]`, and prelude `Set<T>`) are not product types and cannot be projected via dot/accessor syntax directly (`E0337`). Element and key extractions require explicit bracket indexing (`\arr -> arr?[i]`) or higher-order combinators (`Array::first`, `Map::get`).

```ril
-- Standard Anonymous Functions:
let double = \x -> x * 2
let sum = [1, 2, 3] |> Array::fold(0, \acc, x -> acc + x)

-- Trailing Closure Syntax:
let doubled = [1, 2, 3] |> Array::map \x -> x * 2

fn run_job(f: fn() -> int) -> int { f() }
let job_res = run_job \-> 42

-- Shorthand Projection Accessors:
type Employee = .{ id: int, name: str, salary: int }
type Department = .{ name: str, leader: ?Employee }
type Company = .{ name: str, dept: ?Department }

let employees = [
    Employee.{ id: 1, name: "Alice", salary: 8000 },
    Employee.{ id: 2, name: "Bob", salary: 6000 },
]

-- 3a. Record field projection (\.field):
let names = employees |> Array::map(\.name)                   -- Evaluates to ["Alice", "Bob"]
let salaries = employees |> Array::map(\.salary)               -- Evaluates to [8000, 6000]

-- 3(b). Tuple positional index projection (\.index):
let pairs: [](int, str) = [(1, "Alice"), (2, "Bob")]
let ids = pairs |> Array::map(\.0)                            -- Evaluates to [1, 2]
let labels = pairs |> Array::map(\.1)                         -- Evaluates to ["Alice", "Bob"]

-- 3(c). Mixed nested projection:
type Team = .{ id: int, leader: (str, int) }
let teams = [Team.{ id: 10, leader: ("Alice", 30) }]
let leader_ages = teams |> Array::map(\.leader.1)             -- Evaluates to [30]

-- 3(d). Safe navigation projection (\.field?.subfield, \?.field):
let companies: []Company = [
    Company.{ name: "CorpA", dept: Some(Department.{ name: "Engineering", leader: Some(employees[0]) }) },
    Company.{ name: "CorpB", dept: None },
]
let leader_names = companies |> Array::map(\.dept?.leader?.name) -- Evaluates to [Some("Alice"), None]
let opt_depts: []?Department = [Some(Department.{ name: "Sales", leader: None }), None]
let dept_names = opt_depts |> Array::map(\?.name)                -- Evaluates to [Some("Sales"), None]

-- Rejections:
-- let bad_idx = pairs |> Array::map(\.2)                     -- Error [E0312]: tuple index 2 out of bounds for (int, str)
-- let bad_field = employees |> Array::map(\.age)             -- Error [E0336]: unknown field 'age' on type 'Employee'
-- let bad_arr = [[1, 2], [3]] |> Array::map(\.0)             -- Error [E0337]: collections do not have named fields or static tuple projections
```

### Closures, Factory Signatures, and Lexical Environments

```ril
type Adder = fn(int) &up -> int
fn make_adder(base: int) &capture -> new Adder { \x -> base + x }
let add5 = make_adder(5)                -- Immutable captured value
assert(add5(10) == 15)

type Step = fn() &up -> int
fn create_counter(start: int) &capture -> new Step {
    var count = start
    \-> { count += 1; count }
}
let mut counter = create_counter(0)
assert(counter() == 1)
-- let immutable_counter = create_counter(0) -- Error [E0535]: persistent mutable environment cannot become immutable
```

```ril
type Cell = .{ var count: int }
type Step = fn() &up -> int
fn make_shared_step(^mut cell: Cell) &capture &^mut &return{^mut cell} -> new Step {
    \-> { cell.count += 1; cell.count }
}

let mut cell = Cell.{ count: 0 }
let ^mut step = make_shared_step(^mut cell)
assert(step() == 1)
cell.count += 1
assert(step() == 3)                   -- Both authorities still reach the same cell
-- let frozen = make_shared_step(^mut cell) -- Error [E0535]: retained mutable environment
```

- **Abstraction**: `&up` follows [callable contract matching](#callable-contract-matching); direct named capture access requires source groups.
- **Definitions (`E0534`)**: A standalone `&up` annotation on a definition cannot replace its concrete source obligations. Parameter/return callable types may use it as an abstraction under callable matching. Named definitions spell the required concrete capture-source annotations; anonymous definitions preserve the same concrete sources in their fully inferred contracts without mandatory source completion.
- **Creation**: New environments surviving the enclosing callable's return contribute `&capture`, including those nested in returned aggregates. Named definitions must spell that obligation; anonymous definitions may retain it entirely in the inferred contract. Forwarding existing environments or using call-local ones adds no environment-creation obligation.
- **Mode Templates**: Closures may use [lexically bound mode parameters](#lexical-mode-templates-and-closures), specialized with the enclosing instance. Infer their effective capture modes and origins independently; using bound modes does not duplicate an active construction path.
- Anonymous functions capture free value bindings, including module bindings. Module-level named functions use declared external access; escaping block-local functions retain their required lexical environments.
- **Binding Choice**: An immutable environment can be bound with `let` or observed with `ref`. Observer environments use `let ref` under the [observation-wrapper rules](#normative-rules-for-read-only-references), preserving immutable and pinned live dependencies. A persistent mutable environment requires a writable handle. Determine the binding from the environment's actual access modes and origins.
- **Sharing**: A private cell exposed only through one new closure requires `&capture`. Exposing another authority to that cell also requires `&^mut`.



## State and Provenance Tracking

### Local Mutation Purity and Local State Discharge

Writes to frame-confined local storage can be discharged without outward state/provenance obligations. This does not discharge unrelated effects, capture, or retention. A function is pure only when all outward operational-effect and state/provenance obligations are empty after handling and local discharge; implicit Diverge may remain. Only a covering budget can remove that Diverge:

```ril
type Buffer = .{ mut items: []int }
fn append_val(mut b: Buffer, v: int) &mut -> () { b.items |> mut Array::push(v) }

-- Pure function with internal primitive mutation:
fn compute_sum(n: int) -> int {
    var total = 0
    var i = 1
    while i <= n {
        total += i
        i += 1
    }
    total                              -- Pure to callers; semantic contract includes implicit Diverge
}

-- Local State Discharge with shared object types and &mut callees:
fn generate_sequence(count: int) -> []int {
    let mut local_buf = Buffer.{ items: [] }
    var i = 0
    while i < count {
        append_val(mut local_buf, i)   -- &mut discharged locally: local_buf does not escape
        i += 1
    }
    local_buf.items                    -- Pure: confined writes require no outward &mut
}

-- Local discharge of scalar insertion (no retained mutable reference):
type NodeHub = .{ mut nodes: []int }
fn link(mut hub: NodeHub, node: int) &mut -> () { hub.nodes |> mut Array::push(node) }

fn test_internal_hub() -> int {
    let mut local_hub = NodeHub.{ nodes: [] }
    let local_node = 42
    link(mut local_hub, local_node)    -- &mut discharged locally: the scalar is copied
    len(ref local_hub.nodes)          -- Pure: local observation adds no external mutation obligation
}
```

### Parameter Mutation

| Mutation context | Required annotation |
| :--- | :--- |
| Parameter writes without independent retention | Infer `&mut`; writes alone do not justify `&^mut` |
| Independent parameter retention beyond the root-return baseline | Infer `&^mut` from the retained writer; normalization includes the prescribed write implication, without an idle or duplicate annotation |
| Writes plus only `^mut(x) T` root-return retention | Infer `&mut`; the root return annotation covers retention only |
| Named external mutation | Keep the named state annotation and concrete origin |
| Named / anonymous definition | Named definitions spell required concrete state and provenance annotations (`E0510` if absent); genuine `via`-mode dependencies and anonymous functions retain their specified inference exemptions |

```ril
fn clear_items(mut list: []int) &mut -> () {
    list |> mut Array::truncate(0)     -- OK: declared &mut
}

-- Missing state annotation is statically rejected:
-- fn bad_clear(mut list: []int) -> () {     -- Error [E0510]: mutating operation requires caller signature to declare '&mut'
--     list |> mut Array::truncate(0)
-- }
```

```ril
type Cell = .{ var count: int }
fn bump_or_abort(flag: bool, mut cell: Cell) &mut -> () {
    if flag { cell.count += 1; panic("stop") }
}                                       -- OK: panic does not erase the reachable write
-- fn dead(mut cell: Cell) -> () { if false { cell.count += 1 } } -- Error [E0527]: excluded write
-- fn after_panic(mut cell: Cell) -> () { panic("stop"); cell.count += 1 } -- Error [E0527]: unreachable write
-- fn excess(ref cell: Cell) &mut -> int { cell.count } -- Error [E0529]: observation supplies no write obligation
```

### Retained Mutable Sharing

`^mut` has unary prefix precedence; it evaluates its operand once and preserves identity and access modes under the rules below.

```ebnf
SharingExpr     ::= "^mut" Expression
```

```ril
type Entry = .{ var id: int }
type Hub = .{ mut entries: [^mut]Entry }
let mut global_hub = Hub.{ entries: [] }

fn register_entry(mut hub: Hub, ^mut entry: Entry) &^mut -> () {
    hub.entries |> mut Array::push(^mut entry)
}
fn publish_entry(^mut entry: Entry) &^mut &up(sub){mut global_hub} -> () {
    global_hub.entries |> mut Array::push(^mut entry)
}
-- The retained origin is entry. Merely inserting it does not create a new authority to global_hub.
```

| Retained authority | Required annotation |
| :--- | :--- |
| New independent surviving writer, including shared newly created state | `&^mut` or its named-source form |
| Retained module / captured source | Group item `^mut source` includes that source's write access; a destination merely receiving data instead uses `mut destination` |
| Retained argument | `^mut` on parameter and argument; ordinary `mut` ends at return, and indirection preserves true origins |
| Environment creation | Separate `&capture` obligation alongside any `&^mut`; both are standalone state/provenance clauses |

```ril
type Cell = .{ var count: int }
type Holder = .{ mut child: Cell }
let mut source = Cell.{ count: 0 }
let ^mut alias = source
let mut holder = Holder.{ child: ^mut source }
alias.count += 1
holder.child.count += 1
source.count += 1
assert(source.count == 3)
-- let mut hidden = source             -- Error [E0510]: new local writable alias needs ^mut
-- let mut hidden_block = { source }   -- Error [E0510]: a plain block cannot hide the local alias creation
-- let mut hidden_box = Holder.{ child: source } -- Error [E0510]: stored writable alias needs ^mut

let immutable = Cell.{ count: 0 }
let ref observed = source
-- let ^mut bad = immutable           -- Error [E0520]: declaration cannot grant write authority
-- let ^mut bad_ref = observed        -- Error [E0520]: declaration cannot upgrade a live ref
```

| Sharing condition | Required check / rejection |
| :--- | :--- |
| New writable path to existing storage/environment, or internal writable aliases in a copy | Use the [shared-site spelling](#shared-writable-authority); missing acknowledgment is `E0510`. A marker may cover one constituent or a whole construction/pattern source; immutable sharing needs none |
| `^mut expression` evaluation | Once, preserving identity and access modes; no cloning, freezing, ownership transfer, resource revival, or extension of temporary authority |
| Missing authority or possible overlap | A marker cannot repair `E0520`–`E0528`; internal aliases need not form one exact known graph but still undergo all overlap checks |
| Checked callable tail / plain block | A declared return mode may forward authority; a plain block cannot conceal local alias creation |
| Frame-confined sharing | Discharge outward obligations only when all origins and authority roots remain confined; keep local markers and provenance facts |
| Captured / returned sharing | Preserve actual authority roots even if source annotations are inferred |

```ril
fn retain(^mut cell: Cell) -> ^mut(cell) Cell { cell }
let mut original = Cell.{ count: 0 }
let ^mut returned = retain(^mut original) -- Explicit reception of the returned writer
returned.count += 1
original.count += 1
type Packet = .{ mut item: Cell }
let mut packet = Packet.{ item: ^mut retain(^mut original) }
packet.item.count += 1
-- let mut hidden_packet = Packet.{ item: retain(^mut original) } -- Error [E0510]: wrapping does not hide shared reception
-- let mut hidden = retain(^mut original) -- Error [E0510]: returned sharing still needs a reception marker
-- let ^mut hidden = retain(original) -- Error [E0405]: ordinary argument lacks the retention marker
-- let ^mut hidden = retain((^mut original)) -- Error [E0405]: sharing expression is not an argument-mode marker
-- let ^mut hidden = retain(^mut clone(original)) -- Error [E0410]: mutable argument must be an assignable target
```

| Surviving references | Sharing obligation |
| :--- | :--- |
| Repeated fields/cycles inside one fresh passive result graph | No additional external authority; still check internal aliasing |
| Entry parameter root retained only through `^mut(x) T` | Root return covers retention; writes still require `&mut` |
| Extra storage/contained/captured writable path, including a closure plus a direct reference or multiple mutable closures over one cell | Independent `&^mut` or its named form, even inside one returned tuple |
| Unchanged returned graph / mutation of already shared storage | No repeated publication or duplicate `&^mut`/`&capture`; existing aliases, cycles, and environments remain provenance facts |
| Concrete definition | Reject excessive state/provenance annotations with `E0529`; actual retention satisfies the common `E0527` requirement for `^mut` |
| Callable type | Use [exact closed or explicitly open matching](#callable-contract-matching), without changing parameter modes |

Count each newly surviving external path, mutable environment, and separately exposed graph. Receiving a returned writer acknowledges its publication. Apply writable sharing markers to actual retained aliases, including in results of `clone`.

```ril
type Step = fn() &up -> int
fn make_private_ticker() &capture -> new Step {
    var count = 0
    \-> { count += 1; count }
}
fn make_shared_ticker(^mut cell: Cell) &capture &^mut &return{^mut cell} -> new Step {
    \-> { cell.count += 1; cell.count }
}
fn make_dual_ticker() &capture &^mut -> new (mut Step, mut Cell) {
    let mut cell = Cell.{ count: 0 }
    let mut step = \-> { cell.count += 1; cell.count }
    (^mut step, ^mut cell)
}
```

```ril
var active_connections = 0
type Ticker = fn() &up -> int
fn share_connections() &capture &up(sub){^mut active_connections} &return{^mut active_connections} -> new Ticker {
    \-> { active_connections += 1; active_connections }
}
```

Container insertion applies the [storage authority rules](#homogeneous-storage-authority) and [anti-laundering diagnostics](#monotonic-mode-degradation-and-anti-laundering-matrix); initial construction authority does not bypass internal-alias checks.

### External State Tracking

```ril
let APP_CONFIG_NAME = "Production"
var transaction_count = 0

-- Read-only external access:
fn get_config_name() &up(sub){APP_CONFIG_NAME} -> str {
    APP_CONFIG_NAME                    -- OK: declared &up(sub){APP_CONFIG_NAME}
}

fn read_transaction_count() &up(sub){transaction_count} -> int {
    transaction_count                 -- Live source; scalar result is an independent value
}

-- Mutable external access:
fn record_transaction() &up(sub){mut transaction_count} -> () {
    transaction_count += 1             -- OK: declared &up(sub){mut transaction_count}
}

-- Static errors on missing annotations:
-- fn bad_read() -> str { APP_CONFIG_NAME }          -- Error [E0510]: accessing external state requires caller signature to declare state annotation '&up(sub){APP_CONFIG_NAME}'
-- fn bad_write() -> () { transaction_count += 1 }        -- Error [E0510]: mutating external state requires caller signature to declare state annotation '&up(sub){mut transaction_count}'

-- Prohibition of Anonymous Concealment:
-- fn conceal_write() &mut -> () { transaction_count += 1 } -- Error [E0510]: cannot use anonymous '&mut' to conceal external state 'transaction_count'
```

```ril
-- Use record_transaction, read_transaction_count, and transaction_count initialized above.
fn direct_call() &up(sub){mut transaction_count} -> () { record_transaction() }
fn alias_call() &up(sub){mut transaction_count} -> () {
    let action = record_transaction  -- Immutable callable descriptor; named state still applies
    action()
}
fn invoke_action(action: fn() @& -> ()) -> () { action() }
fn parameter_call() &up(sub){mut transaction_count} -> () { invoke_action(record_transaction) }

direct_call()
alias_call()
parameter_call()
assert(read_transaction_count() == 3)

-- fn hidden_call() -> () { record_transaction() } -- Error [E0510]
-- fn hidden_alias() -> () { let action = record_transaction; action() } -- Error [E0510]
-- fn hidden_parameter() -> () { invoke_action(record_transaction) } -- Error [E0510]
-- fn falsely_closed(action: fn() @& -> ()) &{} -> () { alias_call(); action() }
-- Error [E0534]: the closed signature cannot admit the concrete callee's state
```

These call forms use the same [callable contracts](#callable-contracts) and concrete origins.

Accessing module-level or captured bindings records concrete named-source obligations. Named definitions spell their source groups and inherited concrete named obligations, directly or through an admissible function state contract reference. Anonymous definitions retain concrete source identities in their inferred contracts. Callable-dependent and varying `via`-mode obligations may be forwarded symbolically alongside concrete named obligations.

This includes reading a module-level `meta let NAME` in a run-time value expression: the inferred contract records that named source, and a named definition declares `&up(sub){NAME}` for a current-module binding or `&up(Module){NAME}` for an external/parent/child module binding. Compile-time evaluation and immutability do not erase the source. Reads performed in the static/type domain are exempt from this run-time state obligation, including type expressions and static arguments.

Within either kind of source group, a bare item permits read-only access, whether its actual data is immutable or live. It does not promise deep immutability or create a `let ref` binding. `mut name` adds writes; `^mut name` additionally permits retained writable sharing. Each mode applies only to its own item.

Direct access includes storage access in a named definition's lexical anonymous functions and handler arms when those operations contribute to the named definition's current invocation, and mutable argument modes it supplies. The named definition must spell those direct source obligations after local discharge; a state reference cannot replace them. The anonymous callable itself retains its complete inferred source obligations without mandatory annotation. Referencing a named function declaration is not itself a read of storage; accessing a stored external callback is. Future operations of a returned callable remain latent, while its creation, capture, and retention obligations are checked separately.

### State Groups and Captured Layers

```ebnf
StateAnnot          ::= StateClause { StateClause }
StateClause         ::= "&mut" | "&^mut" | "&up" | "&capture" | "&" "{" "}"
                      | ModuleStateGroup | CapturedStateGroup
                      | ReturnDependencyGroup | StateContractRef
ModuleStateGroup    ::= "&up" "(" ModuleOwner ")" "{" StateItemList "}"
ModuleOwner         ::= "sub"
                      | "Super" { "::" "Super" } { "::" PascalCase }
                      | PascalCase { "::" PascalCase }
CapturedStateGroup  ::= "&up" [ "(" CaptureOwner ")" ] "{" StateItemList "}"
ReturnDependencyGroup ::= "&return" "{" ReturnDependencyList "}"
ReturnDependencyList ::= ReturnDependency { "," ReturnDependency } [ "," ]
ReturnDependency    ::= ( "ref" | "^mut" ) QualifiedName
CaptureOwner        ::= ValueName
StateItemList       ::= StateItem { "," StateItem } [ "," ]
StateItem           ::= [ StateMode ] Identifier
StateMode           ::= "mut" | "^mut"
StateContractRef    ::= "&" QualifiedName
```

| Form | Meaning | Source resolution |
| :--- | :--- | :--- |
| `&up` | Callable-type environment abstraction | Actual captured origins remain in verified metadata |
| `&up(sub){mut cache, CONFIG}` | Current module's storage access | Top-level bindings of the current `sub` or executable root |
| `&up(Platform){OS}`, `&up(Super){TAU}`, `&up(Geometry::Transform){LIMIT}` | External, parent, or child module storage access | Bindings owned by the named module (`Module::` omitted inside `{...}`) |
| `&up{mut count}` | Current invocation's captured access | Directly enclosing callable layer |
| `&up(outer_layer){mut count}` | Current invocation's farther named capture | Enclosing callable layer `outer_layer` |
| `&return{ref x, ^mut y}` | Possible contained dependencies of the returned graph | Formal parameters or visible external/captured origins |

Return-dependency groups describe contained graph origins. Invocation mutation, retained sharing, environment creation, and named-state access require their own state and provenance annotations. Independent value-type copies add no return dependency; capturing a mutable binding retains its origin. Body-local regions and output correlations are retained in verified metadata.

```ril
use ril/platform                        -- Binds 'Platform' without importing 'OS' directly

var global_count = 0
let GLOBAL_SCALE = 2
fn tick() &up(sub){mut global_count, GLOBAL_SCALE} -> int {
    global_count += GLOBAL_SCALE
    global_count
}

fn current_os() &up(Platform){OS} -> Platform::Os {
    Platform::OS                        -- Item inside {OS} omits 'Platform::'
}
-- fn bad_sub() &up(sub){Platform::OS} -> Platform::Os { Platform::OS }      -- Error [E0538]
-- fn bad_dup() &up(Platform){Platform::OS} -> Platform::Os { Platform::OS } -- Error [E0538]

fn outer() -> int {
    var count = 0
    inner()
where
    fn inner() &up{mut count} -> int {
        count += 1
        count
    }
}
```

- **Module Groups (`E0538`)**: `&up(sub){...}` names storage bindings owned directly by the current `sub` or executable root. Storage bindings from an imported module, enclosing `Super`, or inline child `sub` use `&up(ModuleOwner){item}` where `ModuleOwner` names the visible module (`Platform`, `Super`, `Geometry::Transform`) and `item` is the unqualified binding name inside that module (`E0538` if qualified or placed under `sub`). A named function declaration is not a storage item.
- **Environment Groups (`E0538`)**: `&up{...}` contains captured bindings from one enclosing callable layer. A directly enclosing layer needs no owner. A farther named layer requires its function name in `&up(owner){...}`. A farther anonymous layer uses a separate ownerless `&up{...}` group. An explicit owner verifies the source layer; it cannot select a same-spelled binding hidden by shadowing.
- **Resolution Before Classification**: Resolve each item by ordinary lexical rules, including shadowing, then verify its group and declaration owner. Preserve its actual activation identity in metadata.
- **Layers and Activations**: Named functions and lambdas introduce callable layers. Blocks, loops, and handler arms do not introduce function layers; their binding identities, dynamic activations, lifetimes, and handler contexts remain distinct. An object's possible origin does not change its binding's declaration layer.
- **Grouping**: Invocation-access items from different callable layers require separate groups, even when both use ownerless `&up{...}`. A return group may summarize multiple resolved origins while preserving their identities. Each mode applies only to its own item. Empty or wrongly classified source groups are `E0538`; invalid return dependencies use `E0545`.
- **Definitions and Types**: Named definitions must spell their inferred concrete groups. Anonymous functions infer and retain these groups without a source-completion obligation. An explicitly written anonymous group is checked. In a callable type, names bind at the type's declaration site; [exact and open matching](#callable-contract-matching) cannot rebind them to similarly named captures in an assigned value.

```ril
fn outer_layer() -> int {
    var count = 0
    middle()
where
    fn middle() &up{mut count} -> int {
        inner()
    where
        fn inner() &up(outer_layer){mut count} -> int {
            count += 1
            count
        }
        -- &up{mut count} here is E0538: count belongs to a farther named layer.
    }
}

let run = \-> {
    var x = 0
    let mut nested = \-> {
        var y = 0
        leaf()
    where
        fn leaf() &up{mut x} &up{mut y} -> int {
            x += 1
            y += 1
            x + y
        }
        -- &up{mut x, mut y} is E0538: two source layers cannot share a group.
    }
    nested()
}
assert(run() == 2)
```

Standalone `&capture`, `&mut`, `&^mut` and the callable-type environment abstraction `&up` have their own rules. The open state/provenance marker `&` belongs to callable-type patterns. Source groups describe invocation access; exclusivity, construction consumption and handler selection are checked separately.

In a state annotation, unqualified `&up` takes precedence over state-contract references. A following `{` selects a captured-source group. A following `(` selects a source group: `sub`, `Super` paths, and `PascalCase` module paths select module storage, while a `snake_case` name selects an enclosing callable layer. Every source group requires a nonempty `{...}` list of unqualified binding names; empty parentheses, missing braces after a selector, qualified items inside `{...}`, repeated selectors, and empty groups use `E0538`. Without `{` or `(`, `&up` is the callable-type environment abstraction. Select the form before name resolution. `&return{...}` likewise has group-head priority and requires braces. A same-spelled provider function requires a qualified reference such as `&Helpers::up`. Outside these positions, `up` is an ordinary identifier.

```ril
var env = 0
fn bump_env() &up(sub){mut env} -> () { env += 1 }
var up = 0
fn bump_up() &up(sub){mut up} -> () { up += 1 } -- Group head and storage item have distinct roles
-- fn empty_group() &up{} -> () {} -- Error [E0538]: no captured source item
-- fn wrong_group() &up{mut env} -> () {} -- Error [E0538]: env is module storage
-- fn missing_items() &up(sub) -> () {} -- Error [E0538]: source groups require a nonempty item list
```


### Named Function State Contract References

```ril
-- counter.ril
var private_count = 0
pub fn advance() &up(sub){mut private_count} -> () { private_count += 1 }
fn private_advance() &up(sub){mut private_count} -> () { private_count += 1 }
pub type Step = fn() &up -> int
pub fn make_step() &capture &up(sub){mut private_count} -> new Step {
    private_count += 1
    var local_count = 0
    \-> { local_count += 1; local_count }
}
pub type Cell = .{ var count: int }
pub fn retain(^mut cell: Cell) &up(sub){mut private_count} -> ^mut(cell) Cell {
    private_count += 1
    cell
}

-- client.ril
use counter
fn wrapper() &Counter::advance -> () { Counter::advance() }
fn through_alias() &Counter::advance -> () {
    let action = Counter::advance
    action()
}
fn invoke(action: fn() @& -> ()) -> () { action() }
fn through_callback() &Counter::advance -> () { invoke(Counter::advance) }
fn make_wrapped() &capture &Counter::make_step -> new Counter::Step {
    Counter::make_step()
}
fn retain_wrapped(^mut cell: Counter::Cell) &Counter::retain -> ^mut(cell) Counter::Cell {
    Counter::retain(^mut cell)
}
-- fn missing_state() -> () { Counter::advance() } -- Error [E0510]
-- fn missing_creation() &Counter::make_step -> new Counter::Step { Counter::make_step() }
-- Error [E0510]: the reference does not include the surviving environment's &capture obligation
-- fn read_private() &Counter::advance -> int { Counter::private_count }
-- Error [E0201]: a state reference does not export the private binding
```

- **Provider (`E0539`)**: `&callee` / `&Module::callee` / `&Super::callee` selects a visible ordinary named Ril definition's verified named-state contract. Resolve names first: lexical absence `E0204`, unresolved module/parent scope `E0208`, absent module member `E0209`, private member `E0201`; then reject a wrong provider kind with `E0539`. Value aliases and callable parameters are not providers.
- **Position (`E0539`)**: Allowed on ordinary named function definitions and callable types. Reject it as a direct annotation on anonymous definitions, effect operations, and bodyless foreign declarations. A nested callable type may use a verified provider reference independently of its enclosing construct.
- **Concrete Named Projection**: A reference denotes the provider's concrete module/captured source items and their verified access modes for its current invocation, including concrete named dependencies obtained through other calls. The bindings and lexical owners remain anchored to the provider's scope. It does not include effects, anonymous parameter modes, standalone `&capture`/`&^mut`, symbolic callback dependencies, or a returned callable's future invocation obligations.
- **Coverage**: On a named definition, after local discharge, match inherited concrete named obligations by origin and access mode; the caller need not invoke the provider by name. On a callable type, the verified named projection participates in exact closed matching or in an explicitly open state/provenance row. A reference imports no return relation: declare that separately. Actual parameter writes and extra retention still need `&mut`/`&^mut`; root-return retention follows its own annotation. Unrelated references on a definition leave `E0510`; unnecessary references there remain `E0529`.
- **Propagation**: Calls through aliases and higher-order helpers preserve concrete dependencies under [complete provenance](#complete-provenance-and-required-annotations). An explicit `&{}` constrains total state, including referenced state.
- **Declaration Identity**: Declaration import aliases and re-exports preserve provider identity. References to callable-valued bindings such as `let action = callee` are `E0539`. Built-in state and provenance spellings take precedence; a same-spelled provider function requires a qualified reference. Access to private state follows the provider visibility and source-group rules.

```ril
-- Same-module fixture:
var count = 0
fn advance() &up(sub){mut count} -> () { count += 1 }
fn other_advance() &up(sub){mut count} -> () { count += 1 }
fn equivalent_contract() &advance -> () { other_advance() } -- Same concrete inherited source and mode
fn no_state() -> () {}
-- fn excessive() &no_state -> () { no_state() } -- Error [E0529]: no concrete named state to declare
-- fn hidden_direct() &advance -> () { count += 1; advance() }
-- Error [E0510]: the direct write still requires &up(sub){mut count}

eff Tick { tick() -> () }
-- fn hidden_handler() &advance -> () {
--     with Tick::tick() -> { count += 1; resume () }
--     advance()
--     Tick::tick()
-- }                                  -- Error [E0510]: the direct handler write needs its own source group

let action = advance
-- fn invalid_provider() &action -> () {}  -- Error [E0539]: action is a value binding
type AdvanceContract = fn() &advance -> () -- OK: verified named-state projection is part of the callable contract
-- fn closed(step: fn() @& -> ()) &{} -> () { advance(); step() }
-- Error [E0534]: a closed higher-order definition cannot inherit this state
```

```ril
-- Counter is the ordinary module defined above.
use counter
-- fn private_reference() &Counter::private_advance -> () {} -- Error [E0201]: private provider
-- fn unknown_reference() &Counter::missing -> () {}         -- Error [E0209]: no such module member
-- let invalid = \&Counter::advance -> ()               -- Error [E0539]: anonymous annotation
-- eff Invalid { tick() &Counter::advance }              -- Error [E0539]: effect-operation annotation
-- In a declaration-unit fixture with the same visible Counter namespace:
-- pub fn invalid_foreign() &Counter::advance -> ()             -- Error [E0539]: bodyless declaration
```

```ril
type Cell = .{ var count: int }
fn outer(mut cell: Cell) &mut -> () {
    inner()
where
    fn inner() &up{mut cell} -> () { cell.count += 1 }
}
-- inner's named capture is derived from outer's mutable parameter authority.

let mut global_cell = Cell.{ count: 0 }
fn touch_global() &up(sub){mut global_cell} -> () { global_cell.count += 1 }
fn parameter_and_ambient(mut cell: Cell) &mut &touch_global -> () {
    cell.count += 1
    touch_global()
}
let mut local = Cell.{ count: 0 }
parameter_and_ambient(mut local)     -- OK: the two actual write origins are disjoint
-- parameter_and_ambient(mut global_cell) -- Error [E0523]: the independent ambient path overlaps the mutable parameter authority
```

```ril
-- counter.ril: a separate effect-bearing operation on its private_count.
pub eff Log { write(str) -> () }
pub fn logged_advance() @Log &up(sub){mut private_count} -> () {
    Log::write("advance")
    private_count += 1
}

-- client.ril
use counter
use counter::{Log, advance as bump}
fn imported_alias() &bump -> () { bump() }  -- Declaration alias, not a value alias
fn logged_wrapper() @Log &Counter::logged_advance -> () { Counter::logged_advance() }
-- fn missing_effect() &Counter::logged_advance -> () { Counter::logged_advance() }
-- Error [E0612]: a state reference does not import Log
```

### Closure Environments and Handle Modes

```ril
let mut counter = create_counter(0)
assert(counter() == 1)
-- let immutable = counter                -- Error [E0535]: live mutable environment cannot become immutable
let ref observer = counter
-- observer()                          -- Error [E0520]: observing a mutable callable does not permit invocation
```

Callable handles use the [common mode tables](#binding-modes-and-storage-matrix); the invoked environment adds these requirements:

| Environment / obligation | Invocation requirement |
| :--- | :--- |
| Persistent mutable captures | Writable handle or `mut`/`^mut` parameter |
| Live observer captures | `ref` handle/parameter |
| Plain `let`, plain `var`, or unmodified parameter | Immutable environment |
| Named state / effects | Check independently of handle mode, including transitive handler access; immutable handles erase no obligation |
| Declared external access only | Does not itself create a mutable environment |

These checks use the specialized effective environment modes, including captures dependent on an enclosing mode template. Lexical mode parameters never substitute for a required handle or make an affine construction path reusable.

### Law of Exclusivity and Cross-Argument Disjointness

Check possible storage origins, not distinct field names or indices. Only conflicting cases require rejection:

| Possible overlap / attempted inference | Diagnostic / rule |
| :--- | :--- |
| Writes of distinct mutable participants | `E0523`; unknown overlap is still possible overlap |
| A mutable participant's writes and another participant's reads | `E0524`; read/read overlap needs no exclusion |
| Independent argument, capture, or ambient path treated as part of a `mut` formal | Not the same call authority, even if object identity matches |
| Nested forwarding through a `mut` formal or its call-local closure | Suspend the caller's access until return; derived authority cannot outlive that call |

Inactive aliases permit sequential sharing. Access through the formal and its call-local derived paths belongs to that invocation; independent paths remain separate participants.

```ril
type Cell = .{ var count: int }
fn swap(mut a: Cell, mut b: Cell) &mut -> () {
    let saved = a.count
    a.count = b.count
    b.count = saved
}
let mut cells: [mut]Cell = [Cell.{ count: 1 }, Cell.{ count: 2 }]
swap(mut cells[0], mut cells[1])        -- OK: distinct allocations, not merely distinct indices
-- swap(mut cells[0], mut cells[0])    -- Error [E0523]: same writable origin

let cell = Cell.{ count: 0 }
let mut copied = clone((mut cell, mut cell))
copied.0.count += 1
assert(cell.count == 0 && copied.1.count == 0)
swap(mut copied.0, mut copied.1)
assert(copied.0.count == 0 && copied.1.count == 1)
```

An explicit `^mut` publication permits sequential sharing, not overlapping exclusive writes or races. Mutations through any alias invalidate affected live refinements. Immutable references are exempt from such invalidation because no writable origin remains.

### Monotonic Mode Degradation and Anti-Laundering Matrix

Apply [provenance propagation](#complete-provenance-and-required-annotations) and the [common mode tables](#binding-modes-and-storage-matrix) at every access path. No wrapper, projection, or writable container grants authority absent from the source. Use the specialized diagnostic for the failing context:

| Prohibited operation | Diagnostic |
| :--- | :--- |
| Upgrade immutable/read-only reference access to writable access | `E0520` |
| Gain write authority through destructuring | `E0521` |
| Gain element write authority from a writable container | `E0522` |
| Gain authority through spread | `E0525` |
| Structurally mutate a collection through any alias during iteration | `E0526` |
| Gain write authority through a returned immutable/read-only origin | `E0528` |

Spread/destructuring of value-type constituents produces independent copies, including `var` pattern targets. Immutable reception of live origins is `E0535`; `let snapshot = clone(ref value)` receives an immutable copy.

```ril
type Cell = .{ var count: int }
let mut box = .{ mut child: Cell.{ count: 0 } }
-- var hidden = box                  -- Error [E0535]: plain var requires immutable data
var ref cursor = box
-- let ^mut stolen = cursor.child     -- Error [E0520]: projection cannot escape the read-only path
box.child.count += 1
assert(cursor.child.count == 1)        -- The independent writer remains valid
let mut replacement = .{ mut child: Cell.{ count: 9 } }
replacement.child.count += 1
cursor = replacement

fn project(ref box: .{ mut child: Cell }) -> ref(box) Cell { box.child }
-- let mut stolen = project(ref box) -- Error [E0528]: the observation return has no write authority
```

[Fresh storage reception](#homogeneous-storage-authority) precedes read-only binding or parameter passage; it cannot recover authority after either boundary.

```ril
type Cell = .{ var count: int }
let immutable = Cell.{ count: 0 }
-- let mut upgraded = immutable           -- Error [E0520]: existing immutable reference
let mut cells: []Cell = []
cells |> mut Array::push(immutable)       -- OK: container is writable, inserted element remains immutable
-- cells[0].count += 1                 -- Error [E0522]: container cannot grant its element write authority
let mut copied = clone(immutable)
let mut shared_cells: [^mut]Cell = []
shared_cells |> mut Array::push(^mut copied) -- Explicit retained writable element, locally discharged
copied.count += 1
assert(shared_cells[0].count == copied.count)

fn identity(cell: Cell) -> Cell { cell }
-- let mut stolen = identity(immutable)  -- Error [E0528]: returned origin remains immutable
let same = identity(immutable)

let mut active = create_counter(0)
assert(active() == 1)
-- clone(ref active)                -- Error [E0530]: mutable captured environment cannot be cloned
-- let observed_as_immutable = active   -- Error [E0535]: ordinary let cannot contain this environment
```

```ril
let mut items = [1, 2]
for items as item {
    -- items |> mut Array::push(item)  -- Error [E0526]: invalidates active iteration
}
items |> mut Array::push(3)
```



## Algebraic Effects and Concurrency

### Effect Declarations and Operation Signatures

```ril
eff Console {
    print(str) -> (),
    read_line() -> str,
}

eff BufferIo { read_into(mut buf: []u8) &mut -> int }

eff State<S> {
    get() -> S,
    put(val: S) -> (),
}

eff Context<T> { ask() -> T }

eff AppEffects { ..Console, ..State<int> } -- Combined effect set; every member is expanded with '..'
-- eff Bad { ..Console, extra() -> () }  -- Error [E0120]: cannot mix operation declarations with '..' effect members
```

```ril
-- Context has the preceding declaration.
fn read_context() @Context<int> -> int { Context::ask() }
with Context<int>::ask() -> resume 7
assert(read_context() == 7)            -- Generic instance inferred; no mutable argument is involved
```

```ril
fn two_states() -> (int, str) {
    with {
        State<int>::get() -> resume 7,
        State<int>::put(_value) -> resume (),
        State<str>::get() -> resume "seven",
        State<str>::put(_value) -> resume (),
    }
    (State<int>::get(), State<str>::get())
}
assert(two_states() == (7, "seven"))
```

| Generic effect operation | Identity / selection |
| :--- | :--- |
| `State<int>::get` | Effect declaration, static arguments under static argument equivalence, and operation declaration |
| Distinct instances | Distinct operations, even with the same operation name |
| Effect-set aliases | Each `..Member` expands that instance; aliases do not create new operation identities |
| Operation selected through a set alias | Exactly one member instance must supply it; unresolved selection is `E0344` |
| Omitted effect arguments | Infer from ordinary argument/result, arm, and protected-computation constraints only when one instance is determined (`E0344` otherwise) |
| Generic arguments in source | Appear on the effect name; operations declare no independent generic parameter list |
| Handler arm | Handles one determined instance; never implicitly handles every instantiation |

Repeated arms for the same instantiated operation are `E0622`, including through aliases. A handler discharges only the instances it covers; uncovered instances remain residual. Effect instances containing still-symbolic enclosing static parameters retain those parameter identities until instantiation.

```ebnf
EffectDecl       ::= { MetaAttr } [ "pub" ] "eff" PascalCase [ GenericParams ] "{" EffectMemberList "}"
EffectMemberList ::= EffectOpDecl { "," EffectOpDecl } [ "," ]
                   | EffectSpread { "," EffectSpread } [ "," ]
EffectSpread     ::= ".." EffectIdentifier
EffectOpDecl     ::= { MetaAttr } ValueName "(" [ ParameterTypeList ] ")" [ StateAnnot ] [ ReturnType ]
EffectAnnot      ::= "@" ( EffectRow | "{" "}" )
EffectRow        ::= EffectIdentifier { "+" EffectIdentifier }
EffectIdentifier ::= QualifiedName [ GenericArgs ]
EffectOperationRef ::= EffectIdentifier "::" ValueName
```

An effect-set alias writes every included instance with the record-spread marker `..`: `eff AsyncIo { ..Io, ..Fiber }`. Each `..EffectIdentifier` expands that instance's operation identities; the alias creates no new identity. An effect declaration body is either an operation list or a `..` member list, never a mixture (`E0120`). Effect identifiers resolve to operational `PascalCase` effect declarations. Writing `@Diverge`, `@Panic`, `@Fatal`, `..Diverge`, `..Panic`, `..Fatal`, or declaring `eff Diverge`, `eff Panic`, or `eff Fatal` in source is `E0620`. Operation signatures use ordinary parameter-mode and state/provenance rules for read-only, temporary writable or retained writable access. A `new` operation parameter is `E0411`; a `via` parameter or `infer` result is `E0412`. Operation declarations require concrete signatures.

```ril
-- Console and BufferIo have the declarations above.
-- Effectful computation: invokes print twice and read_line once
fn hello() @Console -> () {
    Console::print("Enter name:")      -- First intercepted operation
    let name = Console::read_line()     -- Second intercepted operation
    Console::print("Hello, {name}")  -- Third intercepted operation (deep handler re-entered)
}

-- Effectful computation invoking state-annotating BufferIo:
fn fill_header(mut target: []u8) @BufferIo &mut -> int {
    BufferIo::read_into(mut target)    -- OK: &mut annotation flows through caller to operation
}
```

### Effect Handlers

```ril
eff Console { print(str) -> (), read_line() -> str }
fn hello() @Console -> () {
    Console::print("Name?")
    let name = Console::read_line()
    Console::print("Hello, {name}")
}
fn run_console() -> () {
    let mut messages: []str = []
    with {
        Console::print(msg) -> { messages |> mut Array::push(msg); resume () },
        Console::read_line() -> resume "Alice",
    }
    hello()
}
```

An operation-arm `with` covers the remaining block. `resume value` supplies the operation result and reinstalls this handler for the continuation; the arm itself uses outer handlers, even for its own family. The separate parameterized application form below passes the remaining computation to a callable.

The operand of `resume` must match the handled operation's result type (`E0624`). For block answer A, the resulting `resume value` expression and every arm's final value must have type A (`E0625` for an incompatible arm answer), including abort values and post-resumption tails. An incompatible retained handler selection still uses its boundary-specific `E0614`.

```ril
eff ReadNumber { get() -> int }
fn ordinary() -> int { 1 }
fn handler_targets() -> int {
    -- with ordinary() -> resume 1   -- Error [E0621]: target is not an effect operation
    -- with { ReadNumber::get() -> resume 1, ReadNumber::get() -> resume 2 }
    -- Error [E0622]: two arms for the same operation in one with
    with ReadNumber::get() -> resume 1
    ReadNumber::get()                 -- OK
}
fn resume_type() -> int {
    -- with ReadNumber::get() -> resume "one" -- Error [E0624]: operation result is int
    with ReadNumber::get() -> resume 1
    ReadNumber::get()
}
fn answer_type() -> int {
    -- with ReadNumber::get() -> "aborted" -- Error [E0625]: arm answer is str, block answer is int
    with ReadNumber::get() -> 0       -- OK: abort answer fits the block
    ReadNumber::get()
}
```

An operation-arm target (the form with `->`) must resolve to an effect operation (`E0621`). Missing names still use name-resolution diagnostics. Repeating an operation in one `with` is `E0622`; a nested handler for the same operation is allowed. Omitted operations forward outward and are not a missing-arm error; residual obligations use `E0612` when not handled or declared. A parameterized application without `->` follows ordinary callable resolution and argument checking.

```ebnf
WithStatement ::= "with" ( HandlerSpec | WithApplication )
HandlerSpec   ::= "{" HandlerArm { "," HandlerArm } [ "," ] "}" | HandlerArm
HandlerArm    ::= ( EffectOperationRef | QualifiedName ) "(" [ HandlerParameterList ] ")" "->" Expression
HandlerParameterList ::= HandlerParameter { "," HandlerParameter } [ "," ]
HandlerParameter ::= [ ParameterMode ] Pattern
WithApplication ::= QualifiedName [ GenericArgs ] "(" [ ArgumentList ] ")"
ResumeExpr    ::= "resume" Expression
```

A leading `ref`/`mut`/`^mut` on a handler parameter specifies its operation-parameter mode before pattern interpretation. A `new` binder is `E0411`, and `via` is `E0412`. The remaining pattern must be irrefutable and unmodified: `var` is `E0403`, and nested modes are `E0406`. Modes must match the operation declaration (`E0406`); non-operation handler targets use `E0621`.

```ril
eff ReadAt { get(int) -> int }
fn read_zero() -> int {
    with ReadAt::get(index) -> match index {
        0 -> resume 1,
        _ -> resume 2,
    }
    ReadAt::get(0)
}
-- with ReadAt::get(0) -> resume 1      -- Error [E0345]: handler parameter is refutable

type Cell = .{ var count: int }
eff Edit { apply(mut Cell) &mut -> () }
fn edit_once(mut cell: Cell) &mut -> int {
    with Edit::apply(mut target) -> {
        target.count += 1
        let saved = target.count
        let answer = resume ()
        -- target.count += 1            -- Error [E0540]: this operation authority has ended
        answer + saved
    }
    Edit::apply(mut cell)
    cell.count
}
```

| Handler dispatch | Rule |
| :--- | :--- |
| One `with` | At most one arm per operation (`E0622`) |
| Parameters | Irrefutable patterns (`E0345`); explicit modes match the operation declaration (`E0406`) |
| Request-value branches | Ordinary `if`/`match` inside the arm |
| Unlisted operation | Forward outward; retain unhandled effects (`E0612`) |
| Direct operation / verified footprint | Remove the matching handled operation obligation; other possible operations remain |
| Discharge an abstract effect instance | Cover every operation that its available contract permits; an unknown `@Effect` boundary permits the whole instance. Preserve any verified operation footprint; built-in resource/system obligations follow their separate rules |

```ril
type Cell = .{ var count: int }
eff Store { keep(^mut cell: Cell) &^mut -> () }
let mut cell = Cell.{ count: 0 }
let mut held: [^mut]Cell = []
with Store::keep(^mut value) -> {
    held |> mut Array::push(^mut value)
    resume ()
}
Store::keep(^mut cell)
held[0].count += 1
assert(cell.count == 1)
-- with Store::keep(mut value) -> resume () -- Error [E0406]: temporary mode cannot replace retained mode
```

| Operation parameter | Handler binder | Granted authority |
| :--- | :--- | :--- |
| Default | Plain pattern | Deeply immutable data; value types copy |
| `ref` | `ref pattern` | Read-only observation of shared-object data or callable environments; preserve live origins and source lifetimes |
| `mut` | `mut pattern` | Temporary operation authority, ending when resumption starts |
| `^mut` | `^mut pattern` | Retained writable authority; actual retention remains tracked |

Destructured shared-object bindings receive no more than the mode and every source path permit; value-type constituents remain independent read-only copies. A `^mut` handler parameter still must exercise its authority under `E0527`. Resumption does not revoke lawful retained authority, but neither the handler mode nor the operation declaration extends a scoped lifetime or suspends exclusivity checks on independent origins.
`ref` parameters retain their observation restrictions across resumption; the following revocation rule concerns temporary `mut` authority only.

| Operation's ordinary `mut` authority | Arm's access |
| :--- | :--- |
| Before `resume`, including evaluation of its value | Access through the matching parameter |
| Continuation starts | Revoke the authority; end all arm access through the parameter and derived aliases (`E0540`) |
| `resume` returns | No restoration; value-type copies, independent data, and lawful retained `^mut` authority remain usable |

Outer function/callback activations stay active. Independent captures and ambient aliases remain separate exclusivity participants. Neither resumption nor `^mut` extends a call-scoped or resource-scoped lifetime.

| Retained handler context | Rule |
| :--- | :--- |
| New callable | Select creation-scope lexical handlers for transitive residual operations, including callees; use verified operation footprints and conservatively include the full instance at an unrefined abstract effect boundary |
| Handler inside callable body | Establish on invocation |
| Hoisted block-local function | Context at defining-block entry, before its sequential `with`; nested blocks inherit their enclosing context |
| Existing callable / first reference | Never rebind or select a new handler context |
| Expected callable type | Check after selection; reject an incompatible selection rather than substitute a future caller's handler |
| Uncovered operations | Remain residual; each later invocation must handle/forward them; closed contracts require discharge |
| Persistent definition (`E0614`) | Lawful environment and fresh boundary/resumptions per invocation; no old continuations, scoped resources, or return/loop targets |
| Answer (`E0614`) | Every retained arm tail fits the new answer type; outer dependencies have stable handlers or residual rows |
| Creation | Does not execute latent body operations; counts actual environment creation, sharing, and escape |
| Child task (`E0615`) | No ancestor active handler, unhandled `@Scope` / `@Yield<T>` / user effect, or live/mutable environment; immutable data may establish a child-local handler or nested `scope` |

Escape alone is valid. Retention preserves dispatch, required outer definitions, and access/sharing/escape facts for provenance diagnostics, without extra capture syntax. Effect discharge never removes state, capture, live `ref`, or mutable-environment obligations.

```ril
type Button = .{ label: str, on_click: fn() &up -> () }
fn make_button() -> Button {
    Button.{
        label: "Save",
        on_click: \-> {
            with Console::print(msg) -> resume ()
            Console::print("clicked")
        },
    }
}
-- The callback establishes its handler when invoked and has no captured environment.
```


```ril
eff Read { get() -> int }
type Reader = fn() &up -> int
fn make_reader() &capture -> Reader {
    with Read::get() -> resume 7
    \-> Read::get()
}
let reader = make_reader()
assert(reader() == 7)                 -- Fresh invocation boundary with compatible handler

-- A captured arm `{ let result = resume 7; "done" }` is not compatible
-- with this callback's int answer. Retaining it as this handler is E0614.
-- An arm that returns a Reader without resume also cannot answer an int callback.
```

```ril
eff Read { get() -> int }
type Reader = fn() &up -> int
type Deferred = fn() @Read -> int
fn ask_read() @Read -> int { Read::get() }
fn read_without_state(action: fn() @& -> int) &{} -> int { action() }
fn make_indirect_reader() &capture -> Reader {
    with Read::get() -> resume 7
    \-> ask_read()                    -- Captures the handler for the helper's residual Read operation
}
fn make_deferred() -> Deferred { \-> Read::get() }
fn make_chained_reader() &capture -> Reader {
    with Read::get() -> resume 7
    {
        with Read::get() -> {
            let outer = Read::get()
            resume (outer + 1)
        }
        \-> Read::get()
    }
}
fn same_block_helper() -> Deferred {
    with Read::get() -> resume 7
    helper
where
    fn helper() @Read -> int { Read::get() }
}
fn nested_block_helper() &capture -> Reader {
    with Read::get() -> resume 7
    {
        helper
    where
        fn helper() -> int { Read::get() }
    }
}
let captured = make_indirect_reader()
let deferred = make_deferred()
let chained = make_chained_reader()
let same_block = same_block_helper()
let nested_block = nested_block_helper()
let existing = { with Read::get() -> resume 7; ask_read }
{
    with Read::get() -> resume 99
    assert(captured() == 7)
    assert(chained() == 8)              -- Retains both required lexical handler definitions
    assert(deferred() == 99)
    assert(existing() == 99)            -- Referring to ask_read did not create a new callable
    assert(same_block() == 99)          -- Same-block with was not present at the declaration's creation scope
    assert(nested_block() == 7)         -- The nested declaration inherited the enclosing handler
    assert(read_without_state(deferred) == 99)
    -- read_without_state(captured)    -- Error [E0534]: the retained handler environment cannot cross a closed state row
}
-- read_without_state leaves callback effects symbolic and closes its own total state.
-- The retained-handler negative case therefore tests the state boundary independently of effect equality.
```

```ril
eff Tick { tick() -> () }
fn handled_write(mut cell: Cell) &mut -> () {
    with Tick::tick() -> { cell.count += 1; resume () }
    Tick::tick()
}
-- fn hidden_write(mut cell: Cell) -> () {
--     with Tick::tick() -> { cell.count += 1; resume () }
--     Tick::tick()
-- }                                   -- Error [E0510]: handling Tick does not discharge the parameter write
```

The earlier `make_button` body has no captured variables or retained outer handler. Adding `&capture` to it is excessive (`E0529`). A capturing version is:

```ril
fn make_label_button(label: str) &capture -> Button {
    Button.{ label: label, on_click: \-> {
        with Console::print(msg) -> resume ()
        Console::print(label)
    } }
}
-- label is immutable; returning the callback inside Button still publishes its environment.
```

### Parameterized Handler Applications

```ril
eff ReadConfig { get() -> int }
fn supply_config(value: int, action: fn() @& -> int) -> int {
    with ReadConfig::get() -> resume value
    action()
}
halt fn configured() -> int {
    with supply_config(7)
    ReadConfig::get() + 1
}
assert(configured() == 8)

-- The application form has the same behavior as the explicit call:
halt fn configured_explicit() -> int {
    supply_config(7, \-> { ReadConfig::get() + 1 })
}
assert(configured_explicit() == 8)
```

`with f(args)` without `->` makes the rest of the containing block a zero-argument anonymous callable, supplied as the final argument to `f`. The call result is the result of the remaining computation. The callable may define a parameterized handler or another scoped computation.

| Application rule | Behavior |
| :--- | :--- |
| Target and explicit arguments | Resolve and evaluate as an ordinary call, once, in ordinary evaluation order |
| Remaining computation | Becomes the final callable argument; its body is not evaluated during argument creation |
| Callable modes, captures, escape, default arguments, result types | Same checks as the corresponding explicit call with that final anonymous callable |
| Mutable callback handles | No implicit `mut` or `^mut` argument; a remainder requiring such a handle must use an explicit binding and ordinary authorized call |
| `return` in the remaining computation | Returns from that anonymous callable |
| `last` / `next` | Cannot target a loop outside that callable (`E0707`); inner loops retain their ordinary targets |
| Handler selection | Same creation-scope selection and residual forwarding as any anonymous callable; no rebinding of an already selected handler |
| Repeated or omitted invocation | Determined by `f`'s contract; the `with` syntax alone guarantees neither execution nor termination |
| Mixed forms | `with Eff::op(pattern) -> arm` binds operation parameters; `with helper(expression)` passes configuration arguments |

A helper's internal handler can discharge operations forwarded by the final callable; previously selected handlers retain their dispatch. The final callable follows ordinary declaration partition and `where` scope rules. Applications nest in source order, each including the following applications in its final callable. Supplied arguments must leave the final callable parameter unbound; incompatible targets and duplicate arguments use ordinary call diagnostics.

```ril
halt fn existing_selection() -> int {
    with ReadConfig::get() -> resume 3
    with supply_config(7)
    ReadConfig::get()
}
assert(existing_selection() == 3)     -- The callable already selected the outer handler

fn pass(action: fn() -> int) -> int { action() }
halt fn returned_from_action() -> int {
    with pass()
    return 9                         -- Returns from the supplied action; pass then returns 9
}
assert(returned_from_action() == 9)
-- with pass() -> resume 9            -- Error [E0621]: an operation arm cannot target an ordinary function
```

### Affine Resumption and Delimited Early Abort

`resume` is affine: repeated use or escape from its arm is rejected. An arm returning without resumption aborts the delimited computation and runs scoped cleanup in reverse order. Prior writes remain committed.

```ril
fn outside_handler() -> int {
    -- resume 1                      -- Error [E0623]: no enclosing operation arm
    1
}
```

`resume` without an enclosing effect-operation arm is `E0623`. Capturing an enclosing arm's resumption across a prohibited callable boundary remains `E0611`; a second use remains `E0610`. Access through an operation's ended temporary mutable authority, including a derived alias after resumption begins, is `E0540`. This does not revoke an independent lawful retained authority.

```ril
-- Affine Resumption Violation: invoking resume more than once
eff Op { query() -> int }
fn bad_double_resume() -> int {
    with Op::query() -> {
        let first = resume 1
        -- let second = resume 2        -- Error [E0610]: affine resumption 'resume' invoked more than once
        first
    }
    Op::query()
}

-- Escaping Resumption Violation: resume escaping the handler arm
fn bad_escaping_resume() &capture -> (fn() -> int) {
    with Op::query() -> {
        let esc = \-> { let _ = resume 42; 0 } -- Error [E0611]: resumption captured by an escaping callable
        esc
    }
    let value = Op::query()
    \-> value
}

-- Delimited abort with LIFO cleanup; earlier writes are not rolled back:
eff Auth {
    authenticate() -> bool,
}

type AuditLog = .{ mut entries: []str }

fn guarded_workflow(mut audit: AuditLog) @Auth &mut -> str {
    audit.entries |> mut Array::push("STEP_1")                             -- Write takes effect before the operation request
    let scoped mut file = Resource.{ name: "vault.dat", on_close: \-> audit.entries |> mut Array::push("CLEANUP_FILE") }
    let scoped mut session = Resource.{ name: "admin_token", on_close: \-> audit.entries |> mut Array::push("CLEANUP_SESSION") }

    if !Auth::authenticate() {
        "Unauthorized"
    } else {
        audit.entries |> mut Array::push("SUCCESS")
        "Authorized Access"
    }
}

fn test_early_abort() -> () {
    let mut audit = AuditLog.{ entries: [] }
    let res = {
        with Auth::authenticate() -> "Aborted"  -- Early abort without resume
        guarded_workflow(mut audit)
    }
    assert(res == "Aborted")
    -- Invariant: LIFO cleanups executed (session 1st, file 2nd); prior mutation "STEP_1" remains committed:
    assert(audit.entries == ["STEP_1", "CLEANUP_SESSION", "CLEANUP_FILE"]) -- OK
}
```

### Built-in System Effects

| Built-in `@` label | Category | Source `@` annotation | Discharge / containment |
| :--- | :--- | :--- | :--- |
| `@Fiber` | Operational | Required on named callers (`E0612`) | `Fiber::yield` via `with`; leaf I/O and cancellation queries stay `@Fiber` |
| `@Scope` | Operational (`ril/concurrent`) | Required on named nursery helpers (`E0612`) | `Concurrent::scope` / `scope_with` discharges `@Scope` into `@Concurrent`; no `main` handler (`E0612`), not an operation-arm target (`E0621`), cannot cross `fork` / `fork_with` unhandled (`E0615`) |
| `@Concurrent` | Operational | Required on named callers (`E0612`) | Propagates to `@Concurrent` / `@Async` callers |
| `@Async` | Operational alias (`{ ..Fiber, ..Concurrent }`) | Allowed | Expands to `Fiber + Concurrent` (excludes `@Scope`) |
| `@Yield<T>` | Operational (`emit(T) -> ()`) | Required on named callers (`E0612`) | `for` loops or `with Yield::emit(v) -> ...` |
| `@Diverge` | Implicit non-operational | Forbidden (`E0620`) | [`diverge_budget`](#finite-evaluation-with-diverge) $\rightarrow$ `Result<T, BudgetError>`; excluded by `halt` (`E0820`) |
| `@Panic` | Implicit non-operational | Forbidden (`E0620`) | [`absorb_panic`](#panic-absorption-with-absorb_panic) (`E0608`) $\rightarrow$ `Result<T, PanicError>`; child [`fork`](#structured-concurrency-and-panic-containment) $\rightarrow$ `Result<T, TaskFault>` |
| `@Fatal` | Implicit non-operational | Forbidden (`E0620`) | None; terminates the OS process immediately |

```ril
fn spin() -> int { loop {} }                   -- Semantic contract: @Diverge
fn ratio(a: int, d: int) -> int { a / d }      -- Semantic contract: @Panic
fn abort_now() -> never { fatal("corrupted") } -- Semantic contract: @Fatal

-- fn bad1() @Diverge -> int { spin() }        -- Error [E0620]: implicit effect cannot be written
-- fn bad2() @Panic -> int { ratio(1, 0) }     -- Error [E0620]: implicit effect cannot be written
-- fn bad3() @Fatal -> never { abort_now() }   -- Error [E0620]: implicit effect cannot be written
-- with Panic() -> 0                           -- Error [E0621]: non-operational built-in effect
```

The root operational system effect sets satisfy:

$$\emptyset \subset \lbrace\text{Fiber}\rbrace \subset \lbrace\text{Fiber}, \text{Concurrent}\rbrace \equiv \text{Async}$$

`Scope` (exported by `ril/concurrent`) is an orthogonal nursery-local operational effect outside `Async`: imperative task primitives (`fork`, `fork_with`, `join`, `cancel`, `cancel_scope`) require `@Scope`, and `Concurrent::scope` / `scope_with` discharges `@Scope` into `@Concurrent` ($(E \setminus \lbrace\text{Scope}\rbrace) \cup \lbrace\text{Concurrent}\rbrace$).

`Diverge`, `Panic`, and `Fatal` are inferred automatically and exposed in semantic interfaces and tooling (`@[OpEffects] + Diverge + Panic + Fatal`). The prelude supplies [`diverge_budget` / `BudgetError`](#finite-evaluation-with-diverge), [`absorb_panic` / `PanicError`](#panic-absorption-with-absorb_panic), and `fatal` without import.

#### Normative Rules for Built-in System Effects
- **Leaf I/O (`@Fiber`)**: Leaf I/O operations and cooperative cancellation queries (`Concurrent::is_cancelled`, `Concurrent::check_cancelled`) declare `@Fiber` without `@Concurrent`. Spawning or joining child tasks requires `@Scope` inside a `Concurrent::scope` / `scope_with` boundary (`@Concurrent`). Both remain subject to the ordinary task-boundary, provenance, and exclusivity rules.
- **Compound Asynchronous Workflows (`@Async`)**: Functions that both suspend on I/O and manage concurrent child tasks declare `@Async`.
- **Scheduling and Value Generators**: `Fiber::yield() -> ()` yields cooperatively without emitting a user value. Value-emitting streams use the prelude `Yield<T>` effect (`pub eff Yield<T> { emit(value: T) -> () }`, directly supported by [`for` loops](#loop-expressions)) or user-defined streaming effects, with affine resumption. A resumption cannot escape its handler arm to become a pull iterator (`E0611`).

```ril
use ril/file
fn handled_yield() -> () {
    with Fiber::yield() -> resume ()
    Fiber::yield()                     -- No residual Fiber request
}
fn read_name(path: str) @Fiber -> Result<str, str> {
    with Fiber::yield() -> resume ()
    File::read(path)                   -- Resource I/O still requires Fiber
}
-- Omitting @Fiber from read_name is E0612.
```

| System request / label | Discharge rule |
| :--- | :--- |
| `Fiber::yield` | A matching operation arm discharges this yield request |
| Leaf I/O / environmental cancellation or endpoint operation | Retains its `Fiber` obligation unless its public contract explicitly provides a handler |
| `Scope` (`fork`, `fork_with`, `join`, `cancel`, `cancel_scope`) | Discharged into `Concurrent` by `Concurrent::scope` / `scope_with`; not operation-arm targets (`E0621`) |
| `Concurrent` (`scope`, `scope_with`, concurrent combinators) | Retains its `Concurrent` obligation; not operation-arm targets (`E0621`) |
| `Diverge` | Removed only from a covered invocation by `diverge_budget` |
| `Panic` | Removed synchronously by `absorb_panic` (`E0608`) or across a child task by `fork` / `fork_with` / concurrent combinators |
| `Fatal` | Undischargeable; penetrates all handlers, budgets, `absorb_panic`, and task boundaries |

The current resource I/O and structured-concurrency contracts provide no source-level handler that replaces their external behavior. Handling yield alone never covers these obligations. A user-defined effect may expose a mockable interface before any resource operation is invoked. Handling a request does not make an excluded operation eligible for `diverge_budget` or remove its access, cleanup, or task-boundary restrictions.

```ril
-- Signature of the built-in yielding operation, not a redeclaration in user code:
eff Fiber {
    yield() -> (),                     -- Relinquishes quantum to runtime scheduler
}

use ril/concurrent

-- Leaf I/O Suspension Principle (@Fiber):
fn read_socket_chunk(fd: int) @Fiber -> []u8 {
    Socket::read_chunk(fd)             -- Fixture contract: waits for this socket and returns immutable data, @Fiber
}

-- Functions declared @Fiber cannot invoke structured concurrency primitives:
fn bad_leaf_fork(fd: int) @Fiber -> []u8 {
    -- let _ = Concurrent::scope(\-> { -- Error [E0612]: function declares '@Fiber' but invokes unhandled '@Concurrent' primitive 'scope'
    --     let _ = Concurrent::fork(\-> Socket::read_chunk(fd))
    --     Ok(())
    -- })
    read_socket_chunk(fd)
}

-- Compound Asynchronous Workflow (@Async = { ..Fiber, ..Concurrent }):
fn fetch_pipeline(url: str) @Async -> Result<str, Concurrent::TaskFault> {
    let raw = read_socket_chunk(80)    -- Inherits @Fiber
    with Concurrent::scope()           -- Discharges @Scope -> @Concurrent (present in @Async)
    let worker = Concurrent::fork(\-> parse(raw))
    let parsed = (worker |> Concurrent::join)?
    Ok(parsed)
}

-- Cooperative Fiber Yielding (@Fiber):
fn cooperative_worker(count: int) @Fiber -> () {
    var c = count
    while c > 0 {
        c -= 1
        Fiber::yield()                  -- Yields execution quantum to runtime scheduler
    }
}

-- Value-Streaming Generator Composition (using prelude Yield<T>):
fn range_stream(start: int, max: int) @Yield<int> -> () {
    var cur = start
    while cur < max {
        Yield::emit(cur)
        cur += 1
    }
}

-- (a) Synchronous Consumer with Delimited Early Abort:
fn collect_first_evens() -> []int {
    let mut collected: []int = []
    with Yield::emit(v) -> {
        if v % 2 == 0 {
            collected |> mut Array::push(v)
        }
        if len(ref collected) >= 3 {
            -- Delimited early abort: returning without 'resume' cleanly terminates generator
            return collected
        }
        resume ()                      -- Resumes generator execution within lexical handler
    }
    range_stream(0, 100)
    collected
}

-- (b) Independent Composition: Suspendable Async Generator:
fn stream_remote_chunks(fd: int) @Yield<[]u8> + Fiber -> () {
    while true {
        let chunk = read_socket_chunk(fd)
        if len(chunk) == 0 { last }
        Yield::emit(chunk)             -- Composes independent @Yield<[]u8> and @Fiber
    }
}

-- Possible infinite computation automatically adds Diverge to the effect row:
fn collatz(n: int) -> int {
    if n <= 1 { 1 }
    else if n % 2 == 0 { collatz(n / 2) }
    else { collatz(3 * n + 1) }
}

-- Pure recursion retains Diverge even with decreasing arguments:
fn factorial(n: int) -> int {
    if n <= 1 { 1 } else { n * factorial(n - 1) }
}
-- halt fn bad_total(n: int) -> int {  -- Error [E0820]: residual Diverge
--     collatz(n)
-- }
```

<a id="finite-evaluation-with-div"></a>

### Finite Evaluation with Diverge

```ril
fn spin() -> int { loop {} }
halt fn bounded() -> Result<int, BudgetError> {
    diverge_budget(10_000, spin)
}
assert(bounded() is Err(BudgetError::Exhausted))

-- The ordinary with application supplies the remaining computation as the action:
halt fn bounded_with() -> Result<int, BudgetError> {
    with diverge_budget(10_000)
    spin()
}
-- Equivalent to diverge_budget(10_000, \-> spin()).
assert(bounded_with() is Err(BudgetError::Exhausted))
```

`with diverge_budget(limit)` follows [ordinary parameterized application](#parameterized-handler-applications). The remaining computation produces T; the application produces `Result<T, BudgetError>`, which must be inspected, propagated, or returned. `return` in that remaining computation returns from the supplied action.

The prelude supplies Diverge, `diverge_budget`, and `BudgetError` directly. The budget primitive and its result data have these declaration shapes:

```ril
-- Declarations supplied by the prelude, not user redeclarations:
pub type BudgetError { Exhausted }
pub fn diverge_budget<T>(limit: u64, action: fn() @& -> T) -> Result<T, BudgetError>
```

For a covered action with effect row E, the invocation of `diverge_budget` has effects E minus Diverge. Other effects and all outward state/provenance obligations, including result publication, propagate normally; parameter modes and callable-handle authority remain unchanged. The primitive also accepts an action without Diverge. It introduces no exhaustion effect: normal action completion produces `Ok(value)`, and exhaustion produces `Err(BudgetError::Exhausted)` after required cleanup. Mandatory Result inspection applies (`E0720`). A panic retains ordinary run-time unwinding or static diagnostic behavior and is not converted to `Err`.

```ril
eff Ask { get() -> int }
fn ask() @Ask -> int { Ask::get() }
fn attempt() @Ask -> Result<int, BudgetError> {
    diverge_budget(100, ask)                           -- Ask remains; selected handlers must be covered
}
-- diverge_budget(100, \-> 42)                         -- Error [E0720]: unused Result
```

Only the built-in declaration identity receives these rules; callable aliases and re-exports preserve it. Ordinary lexical shadowing applies, and a same-named user function has no privilege. Using `diverge_budget` as an operation-arm target is `E0621`. The primitive is dual-phase: it invokes a same-phase action in type, meta-value, or run-time evaluation. A static intermediate `Result` may contain a type token; ordinary phase/result restrictions still prevent token materialization or a meta function returning type-producing authority. The primitive gives no cross-family exception to user callables (`E0810`).

#### Coverage and Finite Outcomes

The action may have Diverge, but all required computation must be covered by charging or a specified finite primitive contract (`E0822`). Check actual calls, callbacks, selected handlers, resumptions, cleanup, origins, sharing, and escape. A budget or Diverge-free assertion cannot certify its own coverage through a dependency cycle; every potentially infinite execution path must consume unboundedly many units from at least one finite allowance without replenishing it. Symbolic coverage requirements follow actual callable values through aliases, fields, returns, and modules. Preserve unresolved requirements in generic interfaces; an incompatible or unresolved actual requirement at a required concrete use is `E0822`. An empty effect row alone does not prove coverage.

```ril
halt fn limited_sum(values: []int) -> Result<int, BudgetError> {
    diverge_budget(100, \-> {
        var total = 0
        for values as value { total += value }
        total
    })
}
assert(limited_sum([1, 2, 3]) is Ok(6))         -- Confined mutation is covered; Result is inspected

var outside_count = 0
fn write_once() &up(sub){mut outside_count} -> int { outside_count += 1; 7 }
fn bounded_write() &up(sub){mut outside_count} -> Result<int, BudgetError> {
    diverge_budget(100, write_once)               -- State remains; this wrapper is not pure
}
-- halt fn impure() &up(sub){mut outside_count} -> Result<int, BudgetError> {
--     bounded_write()                         -- Error [E0821]: budget does not discharge external writes
-- }

-- Removing an effect label does not make excluded computation covered:
-- with Fiber::yield() -> resume ()
-- diverge_budget(100, \-> Fiber::yield())        -- Error [E0822]
```

Reachable bodyless foreign calls, Fiber/I/O and cancellation queries (`Concurrent::is_cancelled`, `Concurrent::check_cancelled`), `@Scope` operations (`fork`, `fork_with`, `join`, `cancel`, `cancel_scope`), structured-concurrency scopes and combinators, resource endpoint operations, and parallel combinators remain excluded (`E0822`) even when their effect labels are handled. Ordinary algebraic effects may propagate with their selected handlers' coverage requirements; the budget never erases their labels. Finite ordinary-data primitives and sequential collection computations follow their contracts; repeated computation must be charged or have a finite contract. Coverage does not grant state, access, lifetime, or resource authority.

Exhaustion is a private control transfer to the particular budget invocation whose allowance expired. It irrevocably abandons that protected computation, runs its required Diverge-free cleanup, then returns `Err` from that invocation. It is neither an algebraic operation nor a catchable panic. Inner source handlers, Result fallbacks, and budgets cannot intercept or resume an outer exhaustion; no refill is possible. Prior writes remain committed.

```ril
fn bad_recovery() -> int {
    match diverge_budget(0, \-> 42) {
        Ok(value) -> value,
        Err(_) -> spin(),                      -- Recovery is outside this budget; propagates Diverge
    }
}
-- halt fn invalid() -> int { bad_recovery() }  -- Error [E0820]
```

Only the protected invocation's Diverge is removed. Evaluating the limit/action expressions and inspecting or recovering from the Result retain their own effects, Diverge, and state/provenance obligations. Whole-expression `halt` checking includes them. Returned callables retain their complete latent rows and receive no continuing allowance:

```ril
halt fn make_later() -> Result<fn() -> int, BudgetError> {
    diverge_budget(100, \-> spin)                -- Returning spin does not execute it
}
fn run_later() -> int {
    match make_later() {
        Ok(action) -> action(),               -- Diverge remains on this later invocation
        Err(_) -> 0,
    }
}
-- halt fn invalid_later() -> int { run_later() } -- Error [E0820]
```

The compiler's root evaluation limit remains active throughout static budgeting, cleanup, and recovery; exhausting that limit is `E0811`, not a catchable `BudgetError` and not a Diverge discharge.

#### Allowance and Charging

Evaluate `limit: u64` and `action` once in ordinary argument order before establishing the boundary. Zero returns `Err(BudgetError::Exhausted)` without invoking the action; a positive allowance permits entry. Argument evaluation remains covered by active outer boundaries and retains its own obligations.

```ril
fn one() -> int { 1 }
halt fn zero() -> Result<int, BudgetError> {
    diverge_budget(0, one)
}
halt fn one_entry() -> Result<int, BudgetError> {
    diverge_budget(1, one)                        -- One action entry, then normal return
}
assert((zero() is Err(BudgetError::Exhausted)) && (one_entry() is Ok(1)))
fn spin_limit() -> u64 { loop {} }
-- halt fn bad_limit() -> Result<int, BudgetError> {
--     diverge_budget(spin_limit(), one)          -- Error [E0820]: limit evaluation is outside this boundary
-- }
```

| Charged event | Cost before the event |
| :--- | :--- |
| Ordinary/meta/type function or anonymous-callable entry, including the action | One unit |
| Each loop condition/next-element test and possible body; `next` cannot bypass it | One unit |
| Each effect-handler entry and each `resume` | One unit |
| Entry to an inner `diverge_budget` | One unit to existing outer boundaries, before creating its allowance |
| Finite primitive or other finite expression step | No additional cost beyond its specified callable entry, if any |

These source-semantic events survive equivalent optimization in either phase. Sequential combinators retain iteration and callback-entry charges. Every infinite path in covered computation must encounter unboundedly many charged events, including indirect invocation and handler/resumption cycles; no uncharged primitive may hide one. Installing a handler alone executes no operation.

Before each event, exhaust the outermost active boundary with no remaining units and do not execute the event. Otherwise subtract one from every active allowance together and execute it. Spending the last unit permits that event; a later charged event triggers exhaustion. Inner boundaries do not replenish, hide, or suspend outer allowances during ordinary computation, and inner handlers cannot intercept outer exhaustion.

```ril
halt fn nested_limits() -> Result<int, BudgetError> {
    diverge_budget(2, \-> {
        match diverge_budget(100, spin) {
            Ok(value) -> value,
            Err(_) -> 99,
        }
    })
}
assert(nested_limits() is Err(BudgetError::Exhausted)) -- Outer exhaustion bypasses the inner match
```

| Cleanup / allowance | Rule |
| :--- | :--- |
| Cleanup eligibility | Independently Diverge-free (`E0617`); no other residual effects (`E0616`) |
| Cleanup entry | Suspend all previously active allowances, including depleted ones |
| Budget created inside cleanup | Its new allowance remains active |
| Cleanup exit | Restore surviving outer allowances before recovery |
| Unwinding | Ordinary LIFO abort and double-fault rules; no rollback |
| Bound | Protected evaluation events; cleanup is independently Diverge-free, caller recovery retains its own Diverge, and there is no wall-clock bound |

Cleanup's absence of Diverge must be established independently of the allowances suspended on entry. Invocation cycles through cleanup cannot use those allowances, or allowances repeatedly recreated on that cycle, as a finiteness justification (`E0617`; uncovered budget computation is `E0822`). Creating a budget inside independently Diverge-free cleanup is otherwise permitted. This prevents an exhaustion/cleanup/re-entry cycle from repeatedly discarding its limiting allowance.

### Panic Absorption with absorb_panic

```ril
-- Prelude declarations (not user redeclarations):
pub type PanicError { Panicked(str) }
pub fn absorb_panic<T>(action: fn() @& -> T) -> Result<T, PanicError>
pub halt fn fatal(message: str) -> never
```

```ril
fn ratio(a: int, d: int) -> int { a / d }      -- Implicit @Panic

fn safe_ratio(a: int, d: int) -> Result<int, PanicError> {
    absorb_panic(\-> ratio(a, d))              -- Discharges action's @Panic -> Result
}

fn safe_ratio_with(a: int, d: int) -> Result<int, PanicError> {
    with absorb_panic()
    ratio(a, d)
}
assert(safe_ratio(10, 2) == Ok(5))
assert(safe_ratio(10, 0) is Err(PanicError::Panicked(_)))

-- Orthogonal composition with diverge_budget:
halt fn sandbox(work: fn() -> int) -> Result<Result<int, BudgetError>, PanicError> {
    with absorb_panic()
    with diverge_budget(50_000)
    work()
}

-- Unwind-safety enforcement (E0608):
var global_state = 0
-- let bad_mut = absorb_panic(\-> { global_state += 1; 1 }) -- Error [E0608]: external mutable state
```

| Boundary aspect | Rule |
| :--- | :--- |
| Effect discharge | Removes `@Panic` from `action`'s invocation; preserves `@Diverge`, `@Fatal`, and read-only deeply immutable `.ril` `&up(...)` / `&up{...}` state; mandatory `Result` inspection (`E0720`) |
| Unwind safety (`E0608`) | `action` must have no external mutable/live (`mut`, `^mut`, `ref`) reads or writes, no `.d.ril` foreign handle/call access, no escaping mutable or scoped state (`&mut`, `&^mut`, mutable/scoped `&capture`), and no unhandled outward operational effects |
| Confined locals | Fresh local `var` / `let mut` / `let scoped` resources and locally handled algebraic effects inside `action` are permitted; LIFO cleanups run during unwinding before returning `Err(PanicError::Panicked(msg))` |
| Phase & handler arms | Run-time only (`E0810` in static evaluation); using `absorb_panic`, `fatal`, `Panic`, or `Fatal` as a `with ... ->` operation-arm target is `E0621` |
| `@Fatal` penetration | `fatal(message)` and cleanup double-fault (`DoubleFaultFatal`) carry `@Fatal`, bypass `absorb_panic`, and terminate the OS process immediately |

### Structured Concurrency and Panic Containment

```ril
-- Canonical declarations in ril/concurrent (explicit module Concurrent):
-- Built-in effect, handle, and guard:
--   Scope, Task<T, M: MemberMode = MemberMode::Let>, Movable (kind: Type -> Type)

pub type TaskFault {
    Panicked(str),
    Cancelled,
}

-- Nursery boundaries (@Scope -> @Concurrent):
pub fn scope<T>(via body: fn() @& -> infer Result<T, TaskFault>) @Concurrent -> infer Result<T, TaskFault>
pub fn scope_with<P, T>(
    via ctx: P,
    via body: fn(via P) @& -> infer Result<T, TaskFault>,
) @Concurrent -> infer Result<T, TaskFault>

-- Nursery operations (@Scope):
pub fn fork<T, M: MemberMode>(via work: fn() @& -> infer T) @Scope -> Task<T, M>
pub fn fork_with<P, T, M: MemberMode>(
    via payload: P,
    via work: fn(via P) @& -> infer T,
) @Scope -> Task<T, M>
pub fn join<T, M: MemberMode>(task: Task<T, M>) @Scope -> new Result<T, TaskFault>
pub fn cancel<T, M: MemberMode>(task: Task<T, M>) @Scope -> new Result<?T, TaskFault>
pub fn cancel_scope() @Scope -> ()

-- Cooperative cancellation (@Fiber):
pub fn is_cancelled() @Fiber -> bool
pub fn check_cancelled() @Fiber -> ()

-- Declarative combinators (@Concurrent):
pub fn zip<A, B>(
    via left: fn() @& -> infer A,
    via right: fn() @& -> infer B,
) @Concurrent -> infer Result<(via A, via B), TaskFault>
pub fn try_zip<A, B, E>(
    left: fn() @& -> Result<A, E>,
    right: fn() @& -> Result<B, E>,
) @Concurrent -> Result<Result<(A, B), E>, TaskFault>

pub fn all<T>(tasks: []fn() @& -> T) @Concurrent -> Result<[]T, TaskFault>
pub fn try_all<T, E>(
    tasks: []fn() @& -> Result<T, E>,
) @Concurrent -> Result<Result<[]T, E>, TaskFault>

pub fn map<T, U>(
    via items: [via]T,
    via work: fn(via T) @& -> infer U,
) @Concurrent -> infer Result<[via]U, TaskFault>
pub fn try_map<T, U, E>(
    items: []T,
    work: fn(T) @& -> Result<U, E>,
) @Concurrent -> Result<Result<[]U, E>, TaskFault>

pub fn for_each<T>(items: []T, work: fn(T) @& -> ()) @Concurrent -> Result<(), TaskFault>
pub fn try_for_each<T, E>(
    items: []T,
    work: fn(T) @& -> Result<(), E>,
) @Concurrent -> Result<Result<(), E>, TaskFault>

pub fn race<T>(left: fn() @& -> T, right: fn() @& -> T) @Concurrent -> Result<T, TaskFault>
pub fn race_all<T>(tasks: []fn() @& -> T) @Concurrent -> Result<?T, TaskFault>
pub fn race_ok<T, E>(
    tasks: []fn() @& -> Result<T, E>,
) @Concurrent -> Result<Result<T, []E>, TaskFault>
```

```ril
use ril/concurrent::{Scope, scope, scope_with, fork, fork_with, join, Task, TaskFault}

fn spawn_step(x: int) @Scope -> Task<int> {
    fork \-> x + 1                             -- Nursery helper composable inside any @Scope
}

fn sum_steps(mut log: []int) @Concurrent &mut -> Result<int, TaskFault> {
    log |> mut scope_with \mut out -> {
        let a = spawn_step(10)
        let b = spawn_step(30)
        let total = join(a)? + join(b)?
        out |> mut Array::push(total)
        Ok(total)
    }
}

type Packet = .{ mut bytes: []u8 }

fn enrich_packet(new pkt: Packet, tag: u8) @Concurrent &mut -> new Result<Packet, TaskFault> {
    pkt |> new scope_with \new p0 -> {
        let task = p0 |> new fork_with \new p -> {
            p.bytes |> mut Array::push(tag)
            new p
        }
        -- p0.bytes                            -- Error [E0549]: 'p0' ended at handoff
        let mut out = join(task)?
        out.bytes |> mut Array::push(0u8)
        Ok(new out)
    }
}

-- Static rejections:
-- fn bare_fork() @Concurrent -> () { let _ = fork(\-> 1) }         -- Error [E0612]: unhandled @Scope
-- fn leak_scope() @Concurrent -> Result<int, TaskFault> {
--     with scope()
--     join(fork \-> { let _ = fork(\-> 1); 2 })                    -- Error [E0615]: child cannot use parent @Scope
-- }
-- fn nested_join() @Concurrent -> Result<int, TaskFault> {
--     with scope()
--     let t = fork \-> 1
--     scope \-> join(t)                                            -- Error [E0606]: wrong owning scope
-- }
-- fn pack_task() @Scope -> () { let _ = [fork(\-> 1)] }            -- Error [E0606]: Task cannot enter aggregates
-- fn double_join() @Scope -> Result<int, TaskFault> {
--     let t = fork \-> 1
--     let _ = join(t)?
--     join(t)                                                      -- Error [E0609]: duplicate Task consumption
-- }
-- fn capture_mut() @Concurrent -> Result<int, TaskFault> {
--     var n = 0
--     with scope()
--     join(fork \-> { n += 1; n })                                 -- Error [E0601]: live capture across task
-- }
```

| Nursery aspect | Rule |
| :--- | :--- |
| `@Scope` discharge (`E0612`, `E0621`) | `fork`, `fork_with`, `join`, `cancel`, and `cancel_scope` require `@Scope` (`cancel_scope`, `is_cancelled`, and `check_cancelled` omit `Diverge`). `scope` and `scope_with` discharge `@Scope` into `@Concurrent` and forward `body`'s remaining effects and state; `@Scope` is outside `@Async`, has no `main` handler (`E0612`), and is not a `with ... ->` arm target (`E0621`) |
| Child effect isolation (`E0615`) | Child callbacks admit residual operational effects only in $\lbrace\text{Fiber}, \text{Concurrent}\rbrace$; unhandled `@Scope`, `@Yield<T>`, or user effects fail `E0615`. Children may open local handlers or nested `scope` / `scope_with`; implicit `Diverge` propagates |
| Owning scope (`E0606`) | Each `scope` / `scope_with` activation creates a distinct nursery identity. `join` and `cancel` require a handle created in the innermost active scope (`E0606` in an inner or outer scope) |
| Parent context (`scope_with`, `E0405`) | `with scope()` follows [parameterized handler applications](#parameterized-handler-applications); `scope_with` passes `ref` / `mut` parent bindings or `new` inputs explicitly (`E0405` if omitted) |
| Cross-task inputs (`E0601`, `E0549`) | Capturing mutable, `^mut`, `ref`, `let scoped`, or uncontracted `.d.ril` bindings across `fork` / `fork_with` or combinators is `E0601`; immutable `.ril` bindings propagate `&up` / `&up(sub)` provenance (retaining latent callable obligations). `fork_with` and `map` admit only immutable or `new` inputs (`E0601` for `ref`/`mut`/`^mut`), ending `new` caller paths immediately (`E0549`) and invoking each child callback at most once |
| Target lowering (`E0208`, `E0612`) | Explicit target-runtime capability (`use ril/concurrent`). Multi-core targets schedule tasks on M:N fibers; single-threaded event-loop GC targets may map cooperative `@Fiber` suspension points to event-loop tasks; purely synchronous or restricted client targets omit `ril/concurrent*` (`E0208`) and reject `@Fiber` / `@Concurrent` on `main` (`E0612`) |

#### Task Handles, Movable Guard, and Combinators

```ril
use ril/concurrent
use ril/concurrent::{scope, fork, Movable, Task, TaskFault}
use ril/concurrent/channel::{Sender}

type Packet = .{ mut bytes: []u8 }
type Pipe = .{ mut tx: Sender<int>, tag: str }
type RebindPipe = .{ var mut tx: Sender<int> }

meta let _ = assert(<Movable<Packet>> == <Packet>)
meta let _ = assert(<Movable<Sender<int>>> == <Sender<int>>)
meta let _ = assert(<Movable<Sender<Packet, mut>>> == <Sender<Packet, mut>>)
meta let _ = assert(<Movable<Pipe>> == <Pipe>)
meta let _ = assert(<Movable<RebindPipe>> == <never>)      -- var slot on endpoint
meta let _ = assert(<Movable<int>> == <never>)             -- Value type
meta let _ = assert(<Movable<Task<int>>> == <never>)       -- Nursery handle

fn fan_out() @Concurrent -> Result<(Packet, Packet), TaskFault> {
    let (mut a, mut b) = Concurrent::zip(
        \-> Packet.{ bytes: [1u8] },
        \-> Packet.{ bytes: [2u8] },
    )?                                                     -- Disjoint new elements via mode inference
    a.bytes |> mut Array::push(9u8)
    b.bytes |> mut Array::push(9u8)
    Ok((a, b))
}

fn validate_all(xs: []int) @Concurrent -> Result<Result<[]int, str>, TaskFault> {
    xs |> Concurrent::try_map \x -> if x < 0 { Err("neg") } else { Ok(x * 2) }
}

fn first_ok() @Concurrent -> Result<Result<int, []str>, TaskFault> {
    Concurrent::race_ok([\-> Err("e1"), \-> Ok(7)])        -- Ok(7) cancels remaining branches
}

-- Fallible Result rejections (E0720):
-- fn check(x: int) -> Result<int, str> { Ok(x) }
-- let _ = Concurrent::race(\-> check(1), \-> check(2))    -- Error [E0720]: race forbids Result payload
-- fn drop_fallible() @Concurrent -> Result<(), TaskFault> {
--     with scope()
--     let _t = fork \-> check(1)
--     Ok()                                                -- Error [E0720]: unconsumed Task<Result<...>>
-- }
```

| Construct | Rule |
| :--- | :--- |
| `Movable` (`E0411`) | Pure guard (`Type -> Type`) returning `<T>` for `SharedObject` types, channel endpoints (`Sender<T, M>`, `Receiver<T, M>`), and nonempty tuples, records, nominal wrappers, opaque representations, or sums of value/`Movable` constituents with fixed `mut` on endpoint-bearing slots; returns `<never>` for value types, `Task<T, M>`, callables, `let scoped` (`E0548`/`E0604`), and uncontracted `.d.ril` handles (`E0411`/`E0601`/`E0908`) |
| `Task<T, M>` | Affine handle (`<SharedObject<Task<T, M>>> == <never>`; `clone` `E0530`, `derive` `E0536`, `new` `E0411`). `M` defaults to `MemberMode::Let` (immutable/copied `T`) and admits `mut` (`MemberMode::Mut`) for isolated `new T` returns where `T \|> Movable` (`ref`/`^mut`/`var` fail `E0601`/`E0356`). When `M` is `mut`, `let mut v = join(task)?` restores active `new` qualification on `v` |
| Confinement & consumption (`E0606`, `E0609`) | Placing a handle in any aggregate/collection, capturing in an escaping closure or child task, sending on a channel, returning from `scope` / `scope_with`, or consuming in another scope reports `E0606` first. Consuming a handle twice or after branch-uncertain consumption reports `E0609` |
| `join`, `cancel`, `Result` duty (`E0720`) | `cancel` awaits child termination and returns `Ok(Some(v))` (completed), `Err(TaskFault::Panicked(msg))` (panicked), or `Ok(None)` (cancelled). `join` returns `Err(TaskFault::Cancelled)` only after prior cancellation. Dropping an unconsumed `Task<R, M>` whose `R` contains a `Result` on normal exit or `?` is `E0720` |
| Declarative combinators | `zip` and `map` preserve `new` child results (`zip` yields disjoint `(mut A, mut B)` when branches return `new`; `map` yields element-isolated `new Result<[mut]U, TaskFault>` when `work` returns `new U` for `U \|> SharedObject`). `race` and `race_all` (`race_all([]) == Ok(None)`) forbid `Result` in `T` (`E0720`). `try_*` and `race_ok` (`race_ok([]) == Ok(Err([]))`) cancel siblings on the first `Err` (`try_*`) or `Ok` (`race_ok`) and forbid nested `Result` payloads (`E0720`) |
| Phase, budgets, `absorb_panic` | Run-time only (`E0810`), excluded from `diverge_budget` (`E0822`), and rejected unhandled across `absorb_panic` (`E0608`); pure slices inside a child body may still use budgets or `absorb_panic` |

#### Structured Cancellation and Fault Precedence

```ril
use ril/concurrent::{scope, fork, join, cancel, check_cancelled, TaskFault}

fn consumed_panic_recovers() @Concurrent -> Result<int, TaskFault> {
    with scope()
    let a = fork \-> { panic("boom"); 1 }
    match join(a) {
        Ok(v)                         -> Ok(v),
        Err(TaskFault::Panicked(_))   -> Ok(0), -- Consumes a's panic; scope returns Ok(0)
        Err(TaskFault::Cancelled)     -> Err(TaskFault::Cancelled),
    }
}

fn unconsumed_sibling_wins() @Concurrent -> Result<int, TaskFault> {
    with scope()
    let a = fork \-> { panic("a"); 1 }
    let _b = fork \-> { panic("b"); 2 }
    let _ = join(a) ?? \_ -> 0                 -- Consumes a only; unjoined _b still fails scope
    Ok(99)                                     -- Returns Err(TaskFault::Panicked("b"))
}

fn cancel_worker() @Async -> Result<?int, TaskFault> {
    with scope()
    let worker = fork \-> {
        loop {
            check_cancelled()                  -- Unwinds here once cancelled
            Fiber::yield()
        }
    }
    cancel(worker)                             -- Ok(None)
}
```

| Lifecycle aspect | Rule |
| :--- | :--- |
| Cancellation triggers | Triggered immediately by: (1) any unhandled child `@Panic` (recorded in arrival order; consuming one via `join`/`cancel` removes only that child's record without revoking sibling cancellation), (2) parent `body` exit while children remain unfinished, or (3) `cancel` / `cancel_scope()` |
| `@Fiber` points | Observed at `Fiber::yield()`, `check_cancelled()`, suspending `Channel` and `@Fiber` I/O operations, and `scope`/`scope_with`/`join`/`cancel` barriers (`is_cancelled()` polls without unwinding). Cancelled channel waiters detach without consuming buffered or in-flight items |
| Unwinding & barrier | Uncatchable by handlers or `absorb_panic`; runs frame `let scoped` cleanups LIFO, closes unreturned local channel endpoints, and suspends enclosing `diverge_budget` allowances (cleanup panic $\rightarrow$ `@Fatal`). Every spawned child terminates and finishes cleanup before `scope` / `scope_with` returns or runs outer parent cleanups |
| Exit precedence | **`@Fatal`** $>$ **parent `@Panic`** $>$ **earliest unconsumed child `@Panic`** (`Err(TaskFault::Panicked(msg))`) $>$ **parent `body` return** (`Ok`/`Err`, unaffected by siblings cancelled only on parent exit) $>$ **`Err(TaskFault::Cancelled)`**. Concurrent unconsumed child panics choose the first recorded message nondeterministically within `Panicked` |

### Deterministic Data Parallelism and Divide-and-Conquer Primitives

```ril
-- Canonical declarations in ril/parallel (explicit module Parallel):
-- Built-in view type: Slice<T, M: MemberMode = MemberMode::Let> (satisfies LenTarget)

pub type Step<P, R> {
    Done(R),
    Split(via P, via P),
}

-- Divide-and-conquer:
pub fn join<L, R>(via left: fn() & -> infer L, via right: fn() & -> infer R) -> infer (via L, via R)
pub fn join_with<A, B, L, R>(
    via a: A,
    via b: B,
    via left: fn(via A) & -> infer L,
    via right: fn(via B) & -> infer R,
) -> infer (via L, via R)
pub fn divide_and_conquer<P, R>(
    via problem: P,
    max_depth: u8,
    via step: fn(via P) & -> infer Step<P, R>,
    via base: fn(via P) & -> R,
    via combine: fn(R, R) & -> R,
) -> R

-- Functional collection combinators:
pub fn map<T, R>(via xs: [via]T, via f: fn(via T) & -> infer R) -> infer [via]R
pub fn map_indexed<T, R>(via xs: [via]T, via f: fn(int, via T) & -> infer R) -> infer [via]R
pub fn try_map<T, R, E>(via xs: [via]T, via f: fn(via T) & -> Result<R, E>) -> Result<[]R, E>
pub fn filter<T>(via xs: [via]T, via pred: fn(via T) & -> bool) -> infer [via]T
pub fn filter_map<T, R>(via xs: [via]T, via f: fn(via T) & -> infer ?R) -> infer [via]R
pub fn reduce<T>(via xs: []T, via op: fn(T, T) & -> T) -> ?T
pub fn fold<T, Acc>(
    via xs: [via]T,
    init: Acc,
    via leaf: fn(via T) & -> Acc,
    via combine: fn(Acc, Acc) & -> Acc,
) -> Acc
pub fn find<T>(via xs: [via]T, via pred: fn(via T) & -> bool) -> infer ?T
pub fn find_index<T>(via xs: [via]T, via pred: fn(via T) & -> bool) -> ?int
pub fn find_map<T, R>(via xs: [via]T, via f: fn(via T) & -> ?R) -> ?R
pub fn any<T>(via xs: [via]T, via pred: fn(via T) & -> bool) -> bool
pub fn all<T>(via xs: [via]T, via pred: fn(via T) & -> bool) -> bool

-- In-place collection combinators:
pub fn map_in_place<T>(mut xs: []T, via f: fn(T) & -> T) &mut -> ()
pub fn map_indexed_in_place<T>(mut xs: []T, via f: fn(int, T) & -> T) &mut -> ()
pub fn for_each<T |> SharedObject>(mut xs: [mut]T, via f: fn(mut T) &mut & -> ()) &mut -> ()
pub fn for_each_indexed<T |> SharedObject>(
    mut xs: [mut]T,
    via f: fn(int, mut T) &mut & -> (),
) &mut -> ()

-- Slice views (read-only, var-slot replacement, and mut-element mutation):
pub fn as_slice<T, M: MemberMode>(via xs: [via]T) -> infer Slice<T, M>
pub fn subslice<T, M: MemberMode>(via xs: [via]T, lo: int, hi: int) -> infer Slice<T, M>
pub fn slice_range<T, M: MemberMode>(via s: Slice<T, M>, lo: int, hi: int) -> infer Slice<T, M>
pub fn split_at<T, M: MemberMode>(
    via s: Slice<T, M>,
    mid: int,
) -> infer (via Slice<T, M>, via Slice<T, M>)
pub fn slice_at<T, M: MemberMode>(via s: Slice<T, M>, index: int) -> infer T
pub fn slice_get<T, M: MemberMode>(via s: Slice<T, M>, index: int) -> infer ?T
pub fn with_slice<T, M: MemberMode, R>(
    mut xs: [via]T,
    via body: fn(mut Slice<T, M>) &mut & -> R,
) &mut -> R
pub fn split<T, M: MemberMode, R>(
    mut s: Slice<T, M>,
    mid: int,
    via body: fn(mut Slice<T, M>, mut Slice<T, M>) &mut & -> R,
) &mut -> R
pub fn split_join<T, M: MemberMode, L, R>(
    mut s: Slice<T, M>,
    mid: int,
    via left: fn(mut Slice<T, M>) &mut & -> L,
    via right: fn(mut Slice<T, M>) &mut & -> R,
) &mut -> (L, R)
pub fn divide<T, M: MemberMode, R>(
    via s: Slice<T, M>,
    threshold: int,
    via leaf: fn(via Slice<T, M>) & -> R,
    via combine: fn(R, R) & -> R,
) -> R
pub fn slot_set<T>(mut s: Slice<T, var>, index: int, value: T) &mut -> ()
pub fn with_elem<T, R>(mut s: Slice<T, mut>, index: int, via f: fn(mut T) &mut & -> R) &mut -> R
```

```ril
use ril/parallel

halt fn square_sum(xs: []f64) -> f64 {
    let squares = xs |> Parallel::map(\x -> x * x)
    (squares |> Parallel::reduce(\a, b -> a + b)) ?? 0.0   -- Midpoint tree: deterministic f64 sum
}

type Pair = .{ var x: int }

halt fn independent_halves() -> (Pair, Pair) {
    let (mut a, mut b) = Parallel::join(\-> Pair.{ x: 1 }, \-> Pair.{ x: 2 })
    a.x += 10
    b.x += 20
    (a, b)
}

-- Static rejections:
-- fn bad_eff(xs: []int) @Parallel -> []int { xs }                        -- Error [E0620]: not an effect
-- fn bad_io(xs: []int) @Fiber -> []int {
--     xs |> Parallel::map \x -> { Fiber::yield(); x }                    -- Error [E0534]: callback row is closed
-- }
-- var counter = 0
-- fn bad_state(xs: []int) &up(sub){mut counter} -> []int {
--     xs |> Parallel::map \x -> { counter += 1; x }                      -- Error [E0605]: outside write
-- }
```

| Parallel aspect | Rule |
| :--- | :--- |
| Deterministic evaluation & lowering (`E0620`, `E0621`, `E0810`) | Run-time evaluation strategy (`E0810` in static evaluation) observably equivalent to sequential reference order regardless of core count or scheduling; multi-core targets execute branches in parallel while single-threaded or client GC targets may lower `Parallel` primitives directly to sequential evaluation. `@Parallel` is `E0620`; `Parallel` is not a handler target (`E0621`) |
| Callbacks & finiteness (`E0534`, `E0820`, `E0604`, `E0605`) | Closed empty operational row (`E0534` on `@Fiber`/`@Scope`/`@Concurrent`/user effects) and Diverge-free (`E0820`), adding no `Diverge` to `halt` callers. Admits immutable `.ril` reads and lent observations; rejects `let scoped` capture (`E0604`), outside writes/retention, `.d.ril` state, direct `fatal`, and view escape (`E0605`) |
| Divide-and-conquer | `join` and `join_with` evaluate `left` then `right` in reference order (returning proven disjoint `(mut L, mut R)` when branches return `new`). `divide_and_conquer` recurses up to `max_depth` ($\le 255$; `0u8` calls `base`); `divide` splits `s` at `n / 2` while `n > max(1, threshold)` |
| Reductions & short-circuiting (`E0720`) | `map`, `map_indexed`, `filter`, and `filter_map` preserve input order (yielding element-isolated `new [mut]R` when callbacks construct `new` elements, or `new [ref]R` for observed `ref` elements). `reduce` (`[] -> None`, `[x] -> Some(x)`) and `fold` (`[] -> init`, else `combine(init, tree)`) split `[lo, hi)` at `lo + (hi - lo) / 2`. `try_map`, `find*`, `any`, and `all` stop at the smallest deciding or faulting index `k` and discard indices $> k$; `try_map` and `find_map` forbid nested `Result` payloads (`E0720`) |
| `Slice<T, M>` views | Satisfies `LenTarget` (`len(s)` / `len(ref s)`); excluded from `SharedObject` and `Movable` (`clone` `E0530`, `derive` `E0536`, `new` `E0411`, `==` `E0327`, `s[i]` `E0352`), panicking on out-of-bounds access or split. `M` specializes to `MemberMode::Let` (read-only `T`), `ref` (observed `ref T`), `var` (replaceable slots via `with_slice` on `mut []T`), or `mut` (isolated elements via `with_slice` on `mut [mut]T`); `^mut` and `var mut` fail `E0406`. Mutable slices cannot escape `with_slice` (`E0605`), and `split` / `split_join` / `divide` suspend the parent slice during their callbacks |

#### Zero-Copy Read-Only Parallel Inputs

```ril
use ril/parallel
type Cell = .{ var count: int }

fn zero_copy_reads() -> () {
    let mut prices: []int = [10, 20, 30]
    let doubled = prices |> ref Parallel::map(\p -> p * 2)
    let total = (prices |> ref Parallel::reduce(\a, b -> a + b)) ?? 0
    prices[0] = 99
    assert(doubled == [20, 40, 60] && total == 60)

    let mut cells: [mut]Cell = [Cell.{ count: 2 }, Cell.{ count: 15 }]
    let scaled = cells |> ref Parallel::map(\ref c -> c.count * 3)
    let ref big = cells |> ref Parallel::filter(\ref c -> c.count > 10)
    let ref hit = cells |> ref Parallel::find(\ref c -> c.count > 10)
    assert(scaled == [6, 45] && len(ref big) == 1 && hit is Some(_))
    cells[0].count += 1
    -- let _ = prices |> mut Parallel::map(\p -> p)        -- Error [E0406]: read-only input
}

fn parallel_sum(ref xs: []int) -> int {
    let ref view = Parallel::as_slice(ref xs)
    Parallel::divide(ref view, 1024, \ref leaf -> {
        var sum = 0
        for 0..len(ref leaf) as i { sum += Parallel::slice_at(ref leaf, i) }
        sum
    }, \a, b -> a + b)
}
```

| Read-only rule | Requirement |
| :--- | :--- |
| Input modes (`E0401`, `E0406`) | Read-only combinator and `as_slice`/`subslice` `via` inputs specialize to ordinary or `ref` only (`mut`/`^mut`/`new` is `E0406`; `ref` on a value type is `E0401`). Under `ref xs`, value elements pass by value and shared-object elements of `[mut]T`, `[^mut]T`, or `[ref]T` arrive as `ref T` |
| Branch separation (`E0619`) | Shared read-only observations are race-free; any writable region lent to a branch must be proven disjoint from every sibling read and write (`E0619`) |
| Returned observations (`E0535`, `E0537`) | `find`, `filter`, `filter_map`, `map`, `join_with`, `slice_at`, `slice_get`, and `Slice<T, M>` anchor live results to `&return{ref xs}` or `ref(s)`, subject to `ref` reception (`E0535`, `E0531`) and array invalidation (`E0537`) |

#### In-Place Mutable Parallelism

```ril
use ril/parallel
type Counter = .{ var value: int }
type Leaf = .{ var count: int }
type Holder = .{ var ^mut item: Leaf }

halt fn update_arrays(seeds: []int) -> ([]int, []Counter) {
    let mut nums = clone(seeds)
    nums |> mut Parallel::map_in_place(\x -> x + 1)        -- []T slot replacement: valid for any T
    let _ = nums |> mut Parallel::with_slice \mut slots -> {
        slots |> mut Parallel::divide(64, \mut leaf -> {
            for 0..len(ref leaf) as i {
                Parallel::slot_set(mut leaf, i, Parallel::slice_at(ref leaf, i) * 10)
            }
        }, \_, _ -> ())
    }

    let mut counters: [mut]Counter = seeds |> Parallel::map(\s -> Counter.{ value: s })
    counters |> mut Parallel::for_each_indexed \idx, mut c -> { c.value = c.value * 2 + idx }
    let _ = counters |> mut Parallel::with_slice \mut slice -> {
        slice |> mut Parallel::divide(64, \mut leaf -> {
            for 0..len(ref leaf) as i {
                Parallel::with_elem(mut leaf, i, \mut item -> { item.value += 1 })
            }
        }, \_, _ -> ())
    }
    (nums, counters |> ref Parallel::map(\ref c -> Counter.{ value: c.value }))
}

fn isolated_vs_aliased() -> () {
    let mut ok: [mut]Holder = [
        { let mut a = Leaf.{ count: 1 }; Holder.{ item: ^mut a } },
        { let mut b = Leaf.{ count: 2 }; Holder.{ item: ^mut b } },
    ]
    ok |> mut Parallel::with_slice \mut slice -> {
        Parallel::split(mut slice, 1, \mut left, mut right -> {
            Parallel::with_elem(mut left, 0, \mut h0 -> { h0.item.count += 1 })
            Parallel::with_elem(mut right, 0, \mut h1 -> { h1.item.count += 1 })
            -- Parallel::with_elem(mut left, 0, \mut h0 -> {
            --     Parallel::with_elem(mut right, 0, \mut h1 -> { h1.item = ^mut h0.item })
            -- })                                          -- Error [E0619]: cross-slice ^mut write
        })
    }
    ok[1].item = ^mut ok[0].item                           -- Sequential alias across slots
    -- ok |> mut Parallel::for_each(\mut h -> { h.item.count += 1 }) -- Error [E0619]: non-disjoint slots
}
```

| In-place rule | Requirement |
| :--- | :--- |
| `mut xs: []T` (`map_in_place*`, `Slice<T, var>`) | Admits every element type `T`; slots hold values or immutable snapshots and update by whole-slot replacement (`slot_set`) while length is fixed |
| `mut xs: [mut]T` entry (`E0406`, `E0619`) | Rejects `[^mut]T` and `[ref]T` (`E0406`) and requires pairwise disjoint element live graphs at entry (`E0619` otherwise), proved either by flat mutable shape or by element-isolation provenance |
| Flat mutable shape | Rigid concrete type (or closed type set whose members all qualify; unconstrained generics and out-of-scope opaques fail) whose expanded fields and payloads contain only values or immutable constituents—no `mut`, `^mut`, or `ref` members or collections (`[mut/^mut/ref]U`, `[K: mut/^mut/ref V]`) and no live-environment callables |
| Element-isolation provenance | Established by `[]`, `Parallel::map` / `map_indexed` / `filter_map`, `Concurrent::map`, `Channel::drain` / `close_and_drain` with `new` elements, fresh isolated literals, and `clone` of immutable data (`clone(ref live)` inherits `live`'s isolation); preserved by `push`/`insert` of `new` elements and normal in-place return; invalidated by writes linking a slot to another slot or outside live origin, or by unsummarized parameters |
| Callback writes & unwind (`E0619`, `E0605`) | Element callbacks may mutate the element's own graph, store values/immutable snapshots, or install non-escaping local allocations; storing an outside `^mut` or `ref` origin is `E0619` (`with_elem`) or `E0605` (`for_each*`). Overlapping an enclosing `let scoped` cleanup footprint with `xs` is `E0619`; no `Result`-returning in-place primitive exists |

#### Parallel Faults, Fatal Visibility, and Budgets

```ril
use ril/parallel

fn collatz_steps(start: int) -> int {
    var n = start
    var steps = 0
    while n > 1 {
        n = if n % 2 == 0 { n / 2 } else { 3 * n + 1 }
        steps += 1
    }
    steps
}                                                          -- Inferred Diverge

halt fn parallel_collatz(inputs: []int, limit: u64) -> Result<[]int, BudgetError> {
    inputs |> Parallel::try_map \x -> {
        with diverge_budget(limit)                         -- Branch-local sequential allowance
        collatz_steps(x)
    }
}

-- Reference-order fault visibility: index 0 short-circuits, discarding index 1's panic
let r: Result<[]int, str> = [0, 1] |> Parallel::try_map \i -> {
    if i == 0 { Err("stop") } else { Ok(10 / (i - 1)) }
}
assert(r == Err("stop"))

-- Static rejections:
-- fn loud(x: int) -> int { if x < 0 { fatal("neg") } else { x } }
-- halt fn bad_fatal(xs: []int) -> []int { xs |> Parallel::map(\x -> loud(x)) } -- Error [E0605]: direct fatal
-- halt fn bad_budget(xs: []int) -> Result<[]int, BudgetError> {
--     diverge_budget(100, \-> xs |> Parallel::map(\x -> x))                    -- Error [E0822]: outer budget
-- }
```

| Fault / budget aspect | Rule |
| :--- | :--- |
| Budgets (`E0822`) | `diverge_budget` cannot wrap a parallel call (`E0822`); branch-local budgets inside callbacks charge sequentially and independently per branch |
| Direct `fatal` (`E0605`) | Callbacks reaching `fatal(message)` or bodyless foreign calls carrying `@Fatal` are rejected (`E0605`) |
| `@Panic` & cleanup double fault | Branch panics run branch LIFO cleanups; panics and cleanup double faults at indices discarded by an earlier short-circuit or fault are ignored, while the first visible `@Panic` unwinds the caller and a visible cleanup double fault terminates the process (`@Fatal`) |
| Host exhaustion | Host memory or stack exhaustion terminates the process immediately outside reference order |

### Structured Concurrency Channels

```ril
-- Canonical declarations in ril/concurrent/channel (explicit module Channel):
-- Built-in endpoint types:
--   Sender<T, M: MemberMode = MemberMode::Let>
--   Receiver<T, M: MemberMode = MemberMode::Let>

pub type SendError<T> { Closed(T) }
pub type TrySendError<T> { Full(T), Closed(T) }
pub type RecvError { Closed }
pub type TryRecvError { Empty, Closed }

pub type Select2<A, B> {
    First(Result<A, RecvError>),
    Second(Result<B, RecvError>),
}
pub type Select3<A, B, C> {
    First(Result<A, RecvError>),
    Second(Result<B, RecvError>),
    Third(Result<C, RecvError>),
}
pub type SelectSendRecv<S, R> {
    Sent(Result<(), SendError<S>>),
    Received(via S, Result<R, RecvError>),
}

-- Creation & producer duplication:
pub fn bounded<T, M: MemberMode>(capacity: int) @Fiber -> new (mut Sender<T, M>, mut Receiver<T, M>)
pub fn unbounded<T, M: MemberMode>() @Fiber -> new (mut Sender<T, M>, mut Receiver<T, M>)
pub fn clone_sender<T, M: MemberMode>(ref tx: Sender<T, M>) @Fiber -> new Sender<T, M>

-- Send & receive:
pub fn send<T, M: MemberMode>(
    mut tx: Sender<T, M>,
    via item: T,
) @Fiber &mut -> infer Result<(), SendError<T>>
pub fn try_send<T, M: MemberMode>(
    mut tx: Sender<T, M>,
    via item: T,
) &mut -> infer Result<(), TrySendError<T>>
pub fn recv<T, M: MemberMode>(mut rx: Receiver<T, M>) @Fiber &mut -> new Result<T, RecvError>
pub fn try_recv<T, M: MemberMode>(mut rx: Receiver<T, M>) &mut -> new Result<T, TryRecvError>

-- Close, inspection & drain:
pub fn close<T, M: MemberMode>(mut tx: Sender<T, M>) &mut -> ()
pub fn close_recv<T, M: MemberMode>(mut rx: Receiver<T, M>) &mut -> ()
pub fn is_closed<T, M: MemberMode>(ref rx: Receiver<T, M>) -> bool
pub fn len<T, M: MemberMode>(ref rx: Receiver<T, M>) -> int
pub fn capacity<T, M: MemberMode>(ref rx: Receiver<T, M>) -> ?int
pub fn drain<T, M: MemberMode>(new rx: Receiver<T, M>) @Fiber -> new [M]T
pub fn close_and_drain<T, M: MemberMode>(new rx: Receiver<T, M>) @Fiber -> new [M]T

-- Multi-way waiting:
pub fn select_recv2<A, B, MA: MemberMode, MB: MemberMode>(
    mut rx1: Receiver<A, MA>,
    mut rx2: Receiver<B, MB>,
) @Fiber &mut -> new Select2<A, B>
pub fn select_recv3<A, B, C, MA: MemberMode, MB: MemberMode, MC: MemberMode>(
    mut rx1: Receiver<A, MA>,
    mut rx2: Receiver<B, MB>,
    mut rx3: Receiver<C, MC>,
) @Fiber &mut -> new Select3<A, B, C>
pub fn select_send_recv<S, R, MS: MemberMode, MR: MemberMode>(
    mut tx: Sender<S, MS>,
    via item: S,
    mut rx: Receiver<R, MR>,
) @Fiber &mut -> infer SelectSendRecv<S, R>
```

```ril
use ril/concurrent::{scope, fork_with, join, TaskFault}
use ril/concurrent/channel

type Packet = .{ mut bytes: []u8 }
type CloseGuard = .{ mut on_close: fn() & -> () }

fn run_pipeline(items: []u8) @Async -> new Result<[mut]Packet, TaskFault> {
    with scope()
    let (mut tx, mut rx) = Channel::bounded<Packet, mut>(8)
    let producer = tx |> new fork_with \new p_tx -> {
        let scoped mut _close = CloseGuard.{ on_close: \-> Channel::close(mut p_tx) }
        let scoped mut extra_tx = Channel::clone_sender(ref p_tx) -- Built-in Sender scoped close
        let _ = (extra_tx |> mut Channel::send(new Packet.{ bytes: [0u8] })) ?? \_ -> ()
        for items as b {
            let _ = (p_tx |> mut Channel::send(new Packet.{ bytes: [b] })) ?? \_ -> ()
        }
    }
    let consumer = rx |> new fork_with \new c_rx -> {
        c_rx |> new Channel::drain
    }
    join(producer)?
    let mut collected = join(consumer)?
    Ok(new collected)
}

fn sum_fallible(new rx: Channel::Receiver<Result<int, str>>) @Fiber -> int {
    var sum = 0
    for (rx |> new Channel::close_and_drain) as item {     -- Required drain for Result payloads
        sum += item ?? \_ -> 0
    }
    sum
}

-- Static rejections:
-- let (mut tx, mut rx) = Channel::bounded(4)
-- let _ = Channel::send(mut tx, 1)
-- let _ = rx |> new fork_with \new r -> Channel::recv(mut r) ?? \_ -> 0
-- let _ = Channel::recv(mut rx)                          -- Error [E0549]: 'rx' ended at handoff
-- let ^mut shared_rx = rx                                -- Error [E0603]: ^mut forbidden on endpoints
-- let frozen_tx = tx                                     -- Error [E0603]: plain let forbidden on endpoints
-- var mut slot_tx = tx                                   -- Error [E0603]: var slot forbidden on endpoints
-- let _ = clone(ref tx)                                  -- Error [E0530]: use Channel::clone_sender
-- let _ = Channel::select_recv2(mut rx, mut rx)          -- Error [E0523]: aliased mutable endpoints
-- let (mut ftx, mut frx): (mut Channel::Sender<Result<int, str>>, mut Channel::Receiver<Result<int, str>>) = Channel::bounded(2)
-- Channel::close_recv(mut frx)                           -- Error [E0720]: fallible payload must be drained
```

| Channel aspect | Rule |
| :--- | :--- |
| Creation | `bounded` (`capacity < 0` panics; `capacity == 0` is synchronous rendezvous) and `unbounded` require `@Fiber`, omit `Diverge`, and return proven disjoint `(mut tx, mut rx)` endpoints |
| Ownership & transfer (`E0603`, `E0549`, `E0606`) | `Sender<T, M>` and `Receiver<T, M>` satisfy `Movable` (`<SharedObject<...>> == <never>`; `clone` `E0530`, `derive` `E0536`, `[mut]E` `E0411`). Same-task calls borrow via `mut` / `ref`; cross-task handoff uses `new` (`E0549` after transfer). `^mut`, plain `let`, and `var` / `var mut` on endpoints or endpoint-bearing fields fail `E0603`; escaping an owning `scope` / `scope_with` fails `E0606`. `clone_sender` (`@Fiber`, no `Diverge`) duplicates producers |
| Payload eligibility (`E0602`) | `M` defaults to `MemberMode::Let` (deeply immutable or value `T`) and admits `mut` (`MemberMode::Mut`) for isolated `new T` handoff where `T \|> Movable` (`drain` and `close_and_drain` return element-isolated `new [mut]T` when `M` is `mut` and `T \|> SharedObject`). `ref`, `^mut`, `var`, `Task<T, M>`, `let scoped`, or uncontracted `.d.ril` payloads fail `E0602` / `E0356` |
| Closure & `let scoped mut` | Endpoints close deterministically on `close` / `close_recv` / `drain`, `let scoped mut` exit, unreturned child exit, or owning `scope` / `scope_with` completion; once the last active sender closes, receivers drain buffered items then return `Closed`. Built-in `scoped` cleanup closes `Sender<T, M>` (`close`) and `Result`-free `Receiver<T, M>` (`close_recv`) |
| Non-blocking vs `@Fiber` calls | `try_send`, `try_recv`, `close`, `close_recv` (idempotent), `is_closed`, `len`, and `capacity` (`None` if unbounded) have empty operational effects and no `Diverge` (eligible in `scoped` cleanups). `send`, `recv`, `drain`, `close_and_drain`, and `select_*` carry `@Fiber` + `Diverge` and check cancellation; `select_*` polls ready branches fairly, commits at most one branch, and rejects aliased endpoints (`E0523`) |
| Fallible payload conservation (`E0720`) | `SendError::Closed`, `TrySendError::Full`/`Closed`, and `SelectSendRecv::Received(item, ...)` return undelivered items with `new` and `Result` obligations intact. When `T` contains a `Result`, `Receiver<T, M>` forbids `close_recv`, `let scoped mut`, and dropping an undrained receiver (`E0720`); consume to `Closed` or call `drain` / `close_and_drain` and inspect the returned slice |



## Compile-Time Computation and Finiteness

### Static Type Values and Type Quotation

```ebnf
TokenType        ::= "Type" "<" TypeExpression ">"
TypeFunctionExpr ::= "\" TypeFnParam { "," TypeFnParam } "->" Expression
TypeFnParam      ::= PascalCase [ TypeConstraint ] [ "=" TypeExpression ]
                   | ValueName ":" ValueType { "|>" PipelineConstraint } [ "=" Expression ]
                   | ModeParamDecl
```

`TokenType` is the protected intrinsic family resolved through `NominalRef`. A quote is a static value expression whose root must denote one type after removing grouping parentheses (`E0306` otherwise). Const, `typeof` and mapped-type expression slots follow their defining rules.

| Position | Spelling / meaning |
| :--- | :--- |
| Type declaration / data annotation | `type User = .{ id: int }`, `x: User`; direct type syntax |
| Static type value | `<User>`, `<int>`, `<.{ id: int }>` |
| Explicit value-to-type | `typeof e`; the only conversion from a value to its type in a type position |
| Record shape | `.{...}` in type, value, pattern, and test positions; a `TypeReference` may select a runtime construction (`User.{...}`) |
| Tuple token | `<()>` quotes the zero-element tuple. `<(T, U)>` quotes a two-element tuple |
| Generic application | `F<T, U>`; two arguments, not a tuple quote |
| Type pattern | `<Option<let U>>`; pattern-only binders/rests |
| Token type | `Type<T>` denotes the exact static metatype for target `T`; bare `Type` is prohibited |
| Type-parameter sort | `T: Type`; distinct from a const parameter `tok: Type<T>` |
| Value names | `Marker` is a singleton and `UserId` a constructor; their types use `<Marker>` / `<UserId>` |

The following local bindings are fragments of static type-function evaluation:

```ril
type User = .{ id: int, name: str }
let exact = <User>                     -- Type<User>
let tuple = <(int, str)>               -- Type<(int, str)>
let unit = <()>
let callable = <fn(int) -> str>
let saved = exact                     -- Already a token; no second quote
assert(<(int)> == <int> && <int> != <str>)
-- let bad = int                      -- Error [E0319]: use <int> as a value
-- let bad = <int, str>                -- Error [E0120]: quote contains one type
-- let bad = <>                        -- Error [E0120]: missing type
-- let bad = <(\T -> <T>)>             -- Error [E0306]: grouped type-function program is not a quoted type
-- let bad: <int> = <int>              -- Error [E0120]: write Type<int> in an annotation

-- Explicit value-to-type conversion:
type IntFromLiteral = typeof 1024      -- int
-- type BadLiteralType = 1024          -- Error [E0318]: literal values cannot be used as types
```

| Token typing | Rule |
| :--- | :--- |
| Exact metatype | Every token is strictly `Type<T>` with an exact target `T`; `let` and `var` preserve `Type<T>` |
| Definitional target | `Type<A>` matches `Type<B>` only when `A` and `B` are definitionally equal; target subtyping is insufficient |
| Immutability | Tokens are atomic immutable static values; `var` binds a fixed `Type<T>` slot (`E0301` on mismatch) |
| Described schema | Preserve nominal/opaque identity, member modes, and callable contracts |
| Equality | Any two tokens support `==` / `!=` by target definitional identity; no ordering (`E0327`) |
| Kind | Static generics may admit meta-value types; materializing them at run time is `E0816` |

```ril
-- Static fixture; User has the preceding schema.
let exact: Type<User> = <User>
-- let wrong: Type<int> = <never>       -- Error [E0301]: never being a subtype of int does not make targets equal
var fixed = <int>                      -- Type<int>
fixed = <int>
-- fixed = <str>                      -- Error [E0301]: expected Type<int>, found Type<str>

meta fn target_size<T>(token: Type<T>) -> int { byte_size(token) }
meta fn object_size<T>(value: T) -> int { byte_size(<T>) }
meta fn value_type_name<T>(value: T) -> str { type_name(<T>) }
meta fn field_size<T: .{ .. }>(token: Type<T>, meta key: str |> Key<T>) -> int {
    byte_size(<T.(key)>)
}
var user_tok = <User>                  -- Type<User>
let first_size = field_size(user_tok, "id")
-- user_tok = <int>                   -- Error [E0301]: expected Type<User>, found Type<int>
assert(first_size >= 0 && byte_size(user_tok) >= 0)
-- let bad = object_size(<User>)        -- Error [E0306]: Type<User> has no ordinary run-time layout
```

| Inference at a use | Required evidence |
| :--- | :--- |
| `value: T` | Infer the argument's own checked value type: a token yields `Type<User>`, never `User` |
| `token: Type<T>` | Bind `T` from exact token typing; then validate structural/kind constraints |
| `meta key: str \|> Key<T>` | Bind the static key value, then check coordinate membership against target `T` using the `Key<T>` guard |
| Unresolved proof | Defer dependent checks until the required static evaluation; unproved target information is `E0344`, a non-static argument is `E0814`, and a proved incompatible target keeps `E0301` |

Target evidence checks a token against `Type<T>`; it never converts the token into an ordinary `T` value. `typeof e` is the explicit value-to-type conversion: it checks names, types, and access modes without evaluating `e` or producing effects, writes, or environments.

```ril
type Wrap = \T -> <.{ field: T }>
type Nullable = \T -> <?T>
type PairOf = \T, U -> <(T, U)>

type IntNullable = Nullable<int>
type StringIntPair = PairOf<str, int>
type WrappedInt = Wrap<int>

type PaddedBuf = \cap: int, T -> <.{ len: int, data: Buffer<T, cap> }>

-- Symmetric unpacking (<token>):
type TokenUnpack = \T -> {
    let tok = <T>
    <.{ inner: <tok> }>                -- <tok> unquotes static token into type
}

-- meta fn reflection requires explicit tokens:
pub meta fn meta_byte_size<T>(token: Type<T>) -> int { byte_size(token) }
let s = meta_byte_size(<User>)
-- let bad = meta_byte_size(User)      -- Error [E0319]: bare type in expression context
```

Type functions use anonymous-function syntax with a type-producing body. Parameter casing distinguishes categories: `PascalCase` (`\T, \U`) denotes type parameters; `snake_case` (`\cap: int`, `\key: str`) denotes const value parameters. Calling a type function passes type arguments in single angle brackets (`Wrap<int>`). Inside type expressions, `<token>` symmetrically unquotes a static token value into its represented type.

| Angle context | Deterministic parsing |
| :--- | :--- |
| Prefix `<T>` | Primary type quote in expression context; no top-level comma list. `<(T, U,)>` uses existing tuple rules; `<(T,)>` remains invalid |
| Primary type `<token>` | Symmetric unpacking in type context; splices a static token value into a type |
| Expression `QName<...>` | Commit to generic application only when the resolved declaration or preserved item/constructor alias supplies an application signature; otherwise `<` is infix comparison |
| `F<T, U>` / `fn f<T, U>` | Generic argument / parameter lists; the declared parameter category controls checking |
| Value at a type parameter | Not admitted; write `typeof e`; `F<1024>` is `E0306` |
| Expected angle closure | Consume one original `>` character, then rescan the remainder: `<Box<T>>`, `<Type<T>>`, `<T>==<U>`, `type A<T>=T` |
| Ordinary operators | `>=`, `>>`, and `>>=` retain their normal meanings outside an expected closure |
| Const / `typeof` angle operations | Parenthesize: `Flag<(n > 0)>`, `Buffer<u8, (1 << n)>`, `<typeof (a > b)>` |
| Pattern quote | Use the type-pattern extension, including `let U` and rests; those binders are not expression syntax |

Resolve declaration-header/application metadata before committing an expression's postfix generic list; never choose the parse by testing operand types, constraints, or current variable contents. A named callable without explicit generic parameters has an empty explicit generic signature, including one with inferred anonymous input rows; explicit arguments retain `E0340`. Type syntax, type patterns, and generic parameter declarations keep their own list productions; embedded expression slots use the expression rule. No post-commit backtracking is performed.

An empty quote or top-level comma is `E0120`; missing/mismatched committed delimiters use `E0122` / `E0123`. `Type<T, U>` is arity error `E0340`.

```ril
fn comparisons(a: int, b: int, c: int, d: int) -> bool { a < b && c > (d) }
fn choose<flag: bool>(value: int) -> int { if flag { value } else { 0 } }
assert(comparisons(1, 2, 4, 3))        -- a is an ordinary value parameter, not a generic declaration
assert(choose<true && false>(4) == 0) -- Known declaration; const argument need not add parentheses for &&
-- let bad = comparisons<int>(1, 2, 4, 3) -- Error [E0340]: known callable has no generic parameters
```

### Pure Type Functions and Result Restrictions

```ril
halt type SafeRecord = \T ->
    if <T> == <int> { <.{ val: int, valid: bool }> }
    else { <.{ val: T, valid: bool }> }
type IntRecord = SafeRecord<int>
```

```ril
halt type Identity = \T -> <T>              -- OK: type-producing function
meta fn size_of<T>(t: Type<T>) -> int { byte_size(t) } -- OK: reflection produces an ordinary value
halt meta fn checked_size<T>(t: Type<T>) -> int { byte_size(t) } -- Optional pure, Diverge-free assertion
halt fn checked_increment(n: int) -> int { n + 1 } -- Pure, Diverge-free arithmetic on unbounded int
-- halt fn yield_once() @Fiber -> () { Fiber::yield() } -- Error [E0821]: halt requires outward purity
-- halt fn forever() -> () { loop {} }                  -- Error [E0820]: residual Diverge
-- meta let BAD_INDEX = [10][5]                         -- Error [E0831]: panic during static evaluation
```

| Static definition | Result / restriction |
| :--- | :--- |
| Type declaration/function | Type functions produce one type token under the declaration's anonymous-function context; no ordinary result annotation. Effects and state/provenance annotations forbidden (`E0335`) |
| `meta fn` result | Ordinary value free of tokens and type-producing authority; reject after generic instantiation (`E0812`). Effect/state annotations remain forbidden (`E0813`) |
| `meta fn` reflection | May inspect immutable tokens and quote given type syntax, including anonymous shapes; cannot mutate described types or expose a type-producing result API |
| `meta let` | May hold static tokens; only recursively token-free ordinary results can become run-time constants |
| Run-time materialization | Reject tokens and static-only metatypes in materialized value parameters/results, storage, and captures (`E0816`), including through aliases, generics, and opaque wrappers; static generic metadata is excluded |

Both run in the pure static domain: no outward operational effects or state/provenance obligations, with implicit `Diverge` allowed. They support local bindings, control flow, pure static helpers and recursion. Effect/state source annotations remain forbidden (`E0335` / `E0813`), and explicit `@Diverge`/`@Panic`/`@Fatal` remain `E0620`; inference retains `Diverge` in their checking interfaces. Generic type metadata is static and erased from run-time values. Type functions do not distribute over type sets (`E0306`); evaluated results must be a single rigid type token (`E0318`). In type patterns, `<int> | <f64>` is an or-pattern matching atomic tokens.

```ril
type Wrap = \T -> <[]T>
type IntList = Wrap<int>                        -- []int
-- type BadSet = Wrap<int | f64>                -- Error [E0306]: type parameter 'T' requires a rigid type, not a type set
-- type BadUnion = \T -> <int | f64>            -- Error [E0318]: untagged unions cannot be quoted or returned as types

meta fn record_bytes() -> int { byte_size(<.{ id: int }>) }
meta fn meta_identity<T>(value: T) -> T { value }
meta let NUMBER = meta_identity(1)
-- meta let BAD_TOKEN = meta_identity(<int>) -- Error [E0812]: instantiated result is Type<int>
-- meta fn leak<T>(token: Type<T>) -> .{ token: Type<T> } { .{ token: token } }
-- Error [E0812]: wrapping does not remove the returned token

meta let TOKEN = <int>
meta let SIZE = byte_size(TOKEN)
fn runtime_size() &up(sub){SIZE} -> int { SIZE }
fn runtime_client(value: int) -> int {
    -- let token = <int>              -- Error [E0816]: ordinary execution cannot materialize a token
    value
}
-- fn leak_constant() &up(sub){TOKEN} -> Type<int> { TOKEN } -- Error [E0816]: no run-time token values
-- fn leak_shape(value: .{ token: Type<int> }) -> () {} -- Error [E0816]: nested token type in a run-time parameter
```

Phase checks inspect the entire instantiated result/value graph, opaque summaries, captured environments and latent type-producing callable contracts. Results reduced to ordinary constants free of tokens and type-producing authority may cross as ordinary data. A bare `<T>` value expression at run time is `E0816`; forbidden calls use `E0810`.

Symbolic computation follows [Termination and halt Contracts](#termination-and-halt-contracts). `halt type` and `halt meta fn` optionally require pure, Diverge-free computation for every admitted invocation, including reached helpers and defaults; the helpers need not carry `halt`. Residual Diverge is `E0820`; prohibited type/meta annotations remain `E0335`/`E0813`. Panic or a static defect can still fail with its ordinary diagnostic.

Ordinary type/meta declarations and compile-time roots do not require `halt` or absence of Diverge. Loops and recursion are admissible subject to the compiler's root evaluation budget; every root, including a `halt` call, uses that budget. Exhaustion rejects the evaluation with `E0811` and cannot be caught or converted by a source budget. This compiler limit neither removes Diverge from a callable contract nor satisfies a `halt` assertion. An explicit `diverge_budget` runs within that limit, returns an ordinary Result, and can remove Diverge from its covered static action.

```ril
meta fn factorial(n: int) -> int {              -- Implicit Diverge; no source effect annotation
    if n <= 1 { 1 } else { n * factorial(n - 1) }
}
meta let DIRECT = factorial(5)                 -- OK: halt and a source budget are optional

halt meta fn checked_factorial(n: int) -> int {
    match diverge_budget(1_000, \-> factorial(n)) {
        Ok(value) -> value,
        Err(_) -> panic("factorial exceeded evaluation budget"),
    }
}
meta let CHECKED = checked_factorial(5)         -- 120

type Peel = \T -> match <T> {                  -- Recursive type function has implicit Diverge
    <[]let U> -> Peel<U>,
    _ -> <T>,
}
halt type Leaf = \T -> {
    match diverge_budget(1_000, \-> Peel<T>) {
        Ok(token) -> token,
        Err(_) -> panic("type expansion exceeded evaluation budget"),
    }
}
type DirectLeaf = Peel<[][]int>                -- int; ordinary root evaluation is allowed
type CheckedLeaf = Leaf<[][]int>               -- int; optional Diverge-free wrapper
```

| Static evaluation | Budget / failure |
| :--- | :--- |
| Each root evaluation | Configured positive budget, including certified computations |
| Meta/type function entry, static callback entry, loop iteration | Consume one unit each; explicit source budgets add their own charging without resetting this limit |
| Next charged step with no budget | `E0811` |
| Alias cycle | Separate `E0313` check |
| Failed `assert` / other panic | Static `E0830` / `E0831` |

- **Custom Diagnostics and Static Panic (`panic`, `E0831`)**: Type functions, pipeline guards, and meta evaluation blocks may emit developer-specified diagnostics with `panic(message)`. Its `never` result fits any expected branch result, including a type-producing branch. Static panic stops evaluation with `E0831: StaticEvaluationPanicError`, attributed to the triggering instantiation; no run-time unwinding occurs.

```ril
-- Custom diagnostic in pure type function via static panic:
type SizedRecord = \T -> match <T> {
    <.{ id: int, .. }> -> <T>,
    _ -> panic("SizedRecord requires a record containing an 'id: int' field"),
}
-- type BadRecord = SizedRecord<str> -- Error [E0831]: panic during static evaluation: SizedRecord requires a record containing an 'id: int' field
-- Meta helper: ordinary value computation only (returns int, not a type token)
meta fn pad_align(size: int, align: int) -> int {
    assert(size >= 0 && align > 0 && (align & (align - 1)) == 0)
    (size + align - 1) & ~(align - 1)
}

-- Meta predicate inspecting an immutable static type token:
meta fn is_compact<T>(t: Type<T>) -> bool {
    byte_size(t) <= 16                         -- OK: inspects shape, returns value bool
}

-- Type functions provide type-producing interfaces; meta helpers return ordinary values.
halt type PaddedBuffer = \raw_size: int, T -> {
    let actual_size = pad_align(raw_size, 8)   -- OK: consumes meta fn value output
    if is_compact(<T>) {                   -- OK: consumes meta predicate
        <.{ inline_data: []T, len: int }>   -- OK: constructs shape
    } else {
        <.{ chunks: [][]T, cap: int }>      -- OK: constructs shape
    }
}

type FastBuf = PaddedBuffer<64, u8>            -- Resolves to .{ inline_data: []u8, len: int }; 64 supplies the declared const 'raw_size'

-- Static Rejection of Violations:
-- meta fn bad_type_gen() -> Type<int> {       -- Error [E0812]: meta fn cannot expose a token result
--     <int>
-- }
-- halt type BadEffect = \T @Async -> <T>  -- Error [E0335]: type functions cannot declare algebraic effects
-- meta fn bad_eff() @Io -> int { 0 }          -- Error [E0813]: 'meta fn' cannot declare algebraic effects
-- type BadInfinite<T> = BadInfinite<T>        -- Error [E0313]: cyclic alias without nominal or sum indirection
-- type Spin = \T -> Spin<T>
-- type NeverFinishes = Spin<int>             -- Error [E0811]: recursive type-function evaluation exhausts its budget
```

#### Type-Evaluation Exhaustion Diagnostics

An explanation of compile-time budget exhaustion should identify the exhausted compiler evaluation or source budget, the source location where evaluation stopped, and the active instantiation when available. It may include a partial result preview or an evaluation trace. Availability, depth, formatting, and truncation limits are implementation-defined; a result preview is not required when no result structure has been established. The diagnostic code follows the actual failure: compiler-budget exhaustion is `E0811`, while a source budget returns `Err(BudgetError::Exhausted)` and a later explicit panic remains `E0831`.

| Preview / trace | Requirement |
| :--- | :--- |
| Confirmed result structure | Display only structure established to belong to any successful result of this computation; intermediate types may appear separately in a trace, clearly identified as intermediate |
| Unfinished computation | Explicitly mark unresolved portions; do not guess a branch, shape, or member type |
| Presentation truncation | Distinguish completed content omitted for display from computation that has not completed |
| Inspection | Bound inspection and rendering of existing state; do not resume user computation or force further type expansion to fill the preview |
| Language status | Diagnostic data only; placeholders have no type meaning, do not participate in checking, and are not returned by diverge_budget or added to BudgetError |

When an outer result structure is established, an illustrative preview is:

```text
Type evaluation budget exhausted at schema.ril:24
While evaluating: Expand<Node>
Partial result (diagnostic only):
.{
    id: int,
    children: []⟪pending Expand<Node>⟫,
    ... (completed fields omitted)
}
```

If no result structure is established, the current computation and location suffice. Successful handling of source-budget exhaustion must not itself reject compilation. No exhaustion diagnostic is required in that case; tooling may expose its preview or trace on request. The selected fallback must still be a complete valid type:

```ril
halt type OrFallback = \T -> {
    match diverge_budget(0, \-> <T>) {
        Ok(token) -> token,
        Err(_) -> <int>,
    }
}
type Selected = OrFallback<str>               -- OK: int; source-budget exhaustion is handled
```

### Disjoint Call Families, Evaluation Budgets, and Branch Pruning

```ril
fn runtime_identity(value: int) -> int { value }
-- meta let INVALID_CALL = runtime_identity(1) -- Error [E0810]: run-time fn in static evaluation
halt fn twice(value: int) -> int { value * 2 }
-- meta let INVALID_HALT_CALL = twice(3) -- Error [E0810]: halt leaves the call family unchanged
meta let COUNT = len("Ril")              -- OK: ordinary static value reception
-- meta let FAIL = panic("invalid type") -- Error [E0831]: static panic
```

`E0810` diagnoses a forbidden call across the specified evaluation families. `E0814` diagnoses a run-time value where a static value is required, including const arguments and const generic keys. Wrong sorts retain `E0323`; a known negative static value is `E0815`. Direct record access with a dynamic computed key retains `E0324`.

```ril
eff Audit { write(str) -> () }
fn logged_worker(x: int) @Audit -> int { Audit::write("work"); x }

type DispatchMode { Run, Bypass }

fn dispatch_worker<mode: DispatchMode>(f: fn(int) @& -> int, val: int) -> int {
    match mode {
        DispatchMode::Run    -> f(val),
        DispatchMode::Bypass -> val,
    }
}

fn test_specialization(runtime_mode: DispatchMode) -> () {
    assert(dispatch_worker<DispatchMode::Bypass>(logged_worker, 10) == 10) -- OK: callback is not invoked
    -- dispatch_worker<runtime_mode>(logged_worker, 10)      -- Error [E0814]: a static value is required
}
fn run_logged() @Audit -> int { dispatch_worker<DispatchMode::Run>(logged_worker, 10) }
-- fn hidden_log() -> int { dispatch_worker<DispatchMode::Run>(logged_worker, 10) } -- Error [E0612]
```

| Call family | Permitted calls |
| :--- | :--- |
| Type function | Other type functions, `meta fn`, and listed dual-phase operations. An ordinary run-time `fn` is `E0810` |
| Meta value evaluation | `meta fn`, static reflection, and listed dual-phase operations; no ordinary run-time `fn` or direct type-function value call (`E0810`) |
| Run-time value evaluation | No type-function or meta-function value invocation (`E0810`) |
| Both phases | Pure arithmetic/comparison, `len`, `panic`, `fatal`, `assert`, `diverge_budget` with a same-phase action, and other library operations explicitly declared dual-phase |

Dual-phase admission follows the resolved operation's contract. Optional `halt` requires purity and absence of Diverge within the declaration's existing call family; it does not make an ordinary function callable at compile time. Static evaluation of `len` uses the ordinary immutable-value instance for a `LenTarget`. Its run-time `via` template also admits explicit `ref` observation of eligible collections. The [restriction on `via` parameters](#access-mode-inference-with-via-and-infer) applies to static declarations.

Type elaboration in declarations, annotations, quoted type syntax and generic type metadata is static, including inside an ordinary `fn`. Meta code permits local type quotations and read-only reflection while its result follows the [meta-result restrictions](#pure-type-functions-and-result-restrictions).

Static callbacks capture symbolic constants. Mutable resources, handlers, and ordinary run-time calls have no phase-polymorphic exception. Static budget exhaustion is `E0811`.

| Condition | Invocation effects, state, escape, authority use |
| :--- | :--- |
| Static condition (boolean or pattern arm) | Selected branch only |
| Run-time condition | Both branches' possible obligations |

Retain static/generic and callable-dependent [use conditions](#reachable-authority-use) in summaries until the required instantiation determines them. Reject a definition with a known absent required use, or a selected instantiation with absent mode/marker use (`E0527`) or excess concrete state/provenance annotation (`E0529`). Required use needs established evidence after static pruning.

```ril
type Cell = .{ var count: int }
fn selected_write<enabled: bool>(mut cell: Cell) &mut -> () {
    if enabled { cell.count += 1 }
}
let mut cell = Cell.{ count: 0 }
selected_write<true>(mut cell)           -- OK: selected instance has a write
-- selected_write<false>(mut cell)      -- Error [E0527]: selected instance has no writable use
-- Its fixed &mut annotation also has no inferred outward write (E0529).
```

Both branches require valid syntax, name resolution and ordinary type compatibility under their established [generic](#generic-evidence-and-definition-checking) and [arm-local evidence](#pattern-evidence-and-gadt-branches); unselected branches do not grant arbitrary ill-typed operations. Type-token reflection describes types; actual callable-value effects and provenance are retained in callable contracts.

```ril
use ril/platform
use platform/win32                      -- .d.ril foreign module

pub fn open_default() @Fiber &up(Platform){OS} -> Result<int, str> {
    if Platform::OS == Platform::Os::Windows {
        Win32::open_handle()            -- Type/effect-checked everywhere; pruned at lowering off Windows
    } else {
        Ok(0)
    }
}
```

In runtime `if` and `match` expressions over `meta let` constants (including `Platform::OS` and `Platform::ARCH`), all branches are parsed, name-resolved, and type/mode/effect-checked, contributing to the enclosing callable's static effect and state rows. During lowering, `meta let` conditions fold and statically unreachable branches—along with `.d.ril` external symbols referenced solely within them—are pruned prior to target code generation and linking.
### Static Introspection

<a id="coordinate-enumeration-with-keyof"></a>
<a id="static-key-parameters-and-computed-value-projection"></a>
<a id="universal-member-mode-projection"></a>

Static introspection provides coordinate enumeration `coords(<T>)` for product types, variant enumeration `variants(<T>)` for sum types, and constituent projection `T.(k)`.

```ebnf
MappedRecordType          ::= ".{" [ ModeModifier ] MappedComprehensionClause ":" TypeExpression "}"
MappedTupleType           ::= "(" [ ModeModifier ] MappedComprehensionClause ":" TypeExpression ")"
MappedComprehensionClause ::= "[" Expression "as" Pattern "]"
ModeModifier              ::= MemberMode | Identifier
```

#### Coordinate and Variant Introspection (coords, variants)

```ril
type State = .{ id: int, var title: str, mut items: []int }
meta let STATE_COORDS = coords(<State>)
-- [(MemberMode::Let, "id"), (MemberMode::Var, "title"), (MemberMode::Mut, "items")]
meta let TUPLE_COORDS = coords(<(var int, mut []int)>)
-- [(MemberMode::Var, 0), (MemberMode::Mut, 1)]
-- meta let BAD_COORDS = coords(<UiEvent>)  -- Error [E0358]: coords requires a product type

type UiEvent { Click(.{ x: int, y: int }), Hover(int, int), Focus }
meta let EVENT_VARIANTS = variants(<UiEvent>) -- ["Click", "Focus", "Hover"]
```

- **Product Types (`coords(<T>)`)**: For records and tuples, `coords(<T>)` evaluates to `[](MemberMode, CoordKey<T>)` pairing each coordinate's `MemberMode` with its coordinate key (`str` field names in UTF-8 byte order for records; ascending `int` indices for tuples; `[]` for `()`). Non-product targets trigger `E0358`.
- **Sum Types (`variants(<T>)`)**: For sum types, `variants(<T>)` evaluates to `[]str` of variant constructor names in UTF-8 byte order (`E0301` on non-sum).

#### Static Coordinate Parameters and Computed Value Projection

```ril
halt type Product = \T -> match <T> {
    <.{ .. }> | <()> | <(_, ..)> -> <T>,
    _ -> <never>,
}
fn get_coord<T |> Product>(via obj: T, meta key |> Key<T>) -> infer T.(key) {
    obj.(key)
}
fn get_field<T: .{ .. }>(via record: T, meta key: str |> Key<T>) -> infer T.(key) {
    record.(key)
}

type User = .{ id: int, name: str }
let user = User.{ id: 1, name: "Ada" }
let pair = (42, "status")

let name: str = get_coord(user, "name")
let first: int = get_coord(pair, 0)
let copied_name: str = get_coord(ref user, "name") -- Value-type result copies

type Cell = .{ var count: int }
let mut holder = .{ mut cell: Cell.{ count: 0 } }
let ref observed = get_coord(ref holder, "cell")
holder.cell.count += 1
assert(observed.count == 1)                   -- Shared-object result preserves observation

-- get_coord(user, "missing")          -- Error [E0323]: "missing" fails constraint Key<User>
-- get_coord(pair, 2)                  -- Error [E0323]: index 2 out of bounds for Tuple
fn dynamic_key(user: User, key: str) -> () {
    -- get_coord(user, key)            -- Error [E0814]: argument to 'meta' parameter 'key' must be statically known
}
```

A `meta` parameter receives a compile-time static argument in ordinary call position `(...)`. `key |> Key<T>` desugars to `Key<key, T>`, inferring `CoordKey<T>` as the parameter sort when omitted, producing `<()>` when valid and `<never>` otherwise (`E0323`). The key selects a concrete member statically, with the behavior of the corresponding access (`record.name` or `tuple.0`); the `meta` parameter has no run-time value. `-> infer T.(key)` derives reception from the selected constituent. Value-type constituents copy without a live source dependency; shared-object constituents preserve the effective access and actual selected origins. Root sources are expressed relative to the formal's call-entry graph, while contained origins use the separate return-provenance relation; selecting a member does not turn every result into a contained reference.

| Value projection | Requirement |
| :--- | :--- |
| `record.(key)` / `record.("name")` | Static key; preserve reference modes/origins; bracket indexing is `E0324` |
| Tuple `tuple.(idx)` / `tuple.(0)` | Static positional index; excluded by record constraints |
| Sum payload | `match` or variant narrowing; coordinate membership alone supplies no value-level product projection (`E0337`) |

#### Universal Constituent Projection

For a composite type $T$ and coordinate key $k$, `T.(k)` statically projects the constituent shape:
- **Records**: `User.id` or `User.("id")` resolves to the field type.
- **Sum Types**: `UiEvent.Click` or `UiEvent.("Click")` resolves to the variant payload type under Constructor-Tuple Equivalence (multi-field variants resolve to `(T1, ..., Tn)`; single-field to $T_1$; unit / nullary to `()`).
- **Tuples**: `Pair.0` or `Pair.(0)` resolves to the positional component type.

```ril
type Box<T> { Item<U>(U) -> Box<U> }
type ItemType = Box<int>.Item          -- int: U is recovered from Box<int>
type Expr<T> { Int(int) -> Expr<int>, Bool(bool) -> Expr<bool> }
type IntPayload = Expr<int>.Int       -- int
-- type WrongPayload = Expr<int>.Bool -- Error [E0301]: incompatible constructor result equation
```

#### Member Mode Introspection and Retention

```ril
type Elements<T, M: MemberMode> = [M]T
type Views = Elements<.{ var count: int }, ref>
-- type BadViews = Elements<.{ var count: int }, var ref>
-- Error [E0356]: complete replacement-bearing mode is not an element-access mode
```

Mode introspection preserves slot and access components in generic contexts. Unresolved instances trigger `E0344`.

#### Mapped Record and Tuple Types

Mapped types evaluate a comprehension clause `[Expression as Pattern]` over compile-time coordinate collections:

- Mapped records require string keys (`E0341`).
- Mapped tuples require `int` indices (`E0342`). An empty index array produces `()`; an index array of length 1 triggers `E0343` (no 1-tuples).
- `ModeModifier` defaults to immutable (`let`); a bound mode variable (e.g. `m` from `as (m, k)`) or a literal mode (`var`, `mut`, `ref`, `^mut`) applies to generated members. Incompatible value-type modes trigger `E0402`.

```ril
-- 1. Preserve MemberMode via coords:
type Clone = \T -> <.{ m [coords(<T>) as (m, k)]: T.(k) }>

-- 2. Default immutable record (Readonly):
type Readonly = \T -> <.{ [coords(<T>) as (_, k)]: T.(k) }>

type Bag = .{ mut items: []int }
type FixedFields = Readonly<Bag>        -- .{ items: []int }
type Box = .{ var tag: int, mut bag: FixedFields }
let mut box = Box.{ tag: 0, bag: FixedFields.{ items: [1] } }
box.tag = 1
-- box.bag.items |> mut Array::push(2) -- Error [E0520]: a default member blocks nested writes

-- 3. Replaceable fields:
type Slots = \T -> <.{ var [coords(<T>) as (_, k)]: T.(k) }>
type PairSlots = (var [[0, 1] as (_, i)]: int) -- (var int, var int)

-- 4. Pipeline filtering (Pick):
type Pick = \T: .{ .. }, included: []str -> {
    let filtered = coords(<T>) |> Array::filter(\(m, k) -> included |> Array::contains(k))
    <.{ m [filtered as (m, k)]: T.(k) }>
}
type SubState = Pick<State, ["id", "items"]>   -- .{ id: int, mut items: []int }

-- 5. Sum type dispatch tables:
type EventHandlerTable = \T, R -> <.{
    [variants(<T>) as k]: fn(T.(k)) -> R
}>
type UiHandlerTable = EventHandlerTable<UiEvent, ()>
-- .{ Click: fn(.{ x: int, y: int }) -> (), Focus: fn(()) -> (), Hover: fn((int, int)) -> () }

-- 6. Canonical Tuple Reversal:
type Pair = (int, str)
halt type ReverseTuple = \T -> {
    let rev_indices = coords(<T>) |> Array::map(\(m, k) -> k) |> Array::reverse
    <(
        [rev_indices as (_, i)]: T.(i)
    )>
}
type ReversedPair = ReverseTuple<Pair>         -- (str, int)
type ReversedUnit = ReverseTuple<()>           -- ()

-- Diagnostic rejection:
-- type BadRecordKeys = .{ [[0, 1] as (_, k)]: int } -- Error [E0341]: mapped record requires '[]str' keys
-- type BadTupleKeys = ( [["a", "b"] as (_, i)]: int ) -- Error [E0342]: mapped tuple requires '[]int' keys
-- type Bad1Tuple = ( [[0] as (_, i)]: int )          -- Error [E0343]: single-element tuple prohibited
```

#### Metadata and Documentation Introspection

```ril
pub type Tool(str)
pub type MinLen(int)

--| Arguments for semantic document search.
meta(Tool("search_docs"))
pub type SearchArgs(.{
    --| Search keywords.
    meta(MinLen(1))
    query: str,
    --| Maximum returned hits.
    limit: int = 10,
})

pub type FieldSchema = .{
    name: str,
    doc: ?str,
    required: bool,
    min_len: ?int,
}

pub halt meta fn describe_fields<T>(tok: Type<T>) -> []FieldSchema {
    let mut out: []FieldSchema = []
    for coords(<Unwrap<T>>) as (_, key) {
        let mins = Reflect::field_attrs<T, MinLen>(tok, key)
        out |> mut Array::push(FieldSchema.{
            name: key,
            doc: Reflect::field_doc(tok, key),
            required: !Reflect::has_default(tok, key),
            min_len: if len(mins) > 0 { Some(inner(mins[0])) } else { None },
        })
    }
    out
}

meta let SEARCH_DOC = Reflect::doc(<SearchArgs>)
-- Some("Arguments for semantic document search.")
meta let SEARCH_TOOLS = Reflect::attrs<SearchArgs, Tool>(<SearchArgs>)
-- [Tool("search_docs")]
meta let SEARCH_SCHEMA = describe_fields(<SearchArgs>)

type RawAlias = .{ x: int = 1 }
meta let _ = assert(!Reflect::has_default(<RawAlias>, "x")) -- <RawAlias> == <.{ x: int }> (structural; no declaration identity)
```

| `Reflect` operation (`ril/reflect`) | Canonical declaration | Behavior |
| :--- | :--- | :--- |
| `Reflect::attrs` | `pub halt meta fn attrs<T, A>(target: Type<T>) -> []A` | Attributes of exact type `A` on nominal, opaque, or sum `T` in source order (`[]` for structural types) |
| `Reflect::field_attrs` | `pub halt meta fn field_attrs<T, A>(target: Type<T>, meta key: str \|> Key<UnwrapOrSelf<T>>) -> []A` | Attributes of exact type `A` on root record field `key` of nominal or visible opaque `T` (`[]` for structural types) |
| `Reflect::variant_attrs` | `pub halt meta fn variant_attrs<T, A>(target: Type<T>, meta variant: str) -> []A` | Attributes of exact type `A` on variant `variant` of sum `T` (`E0301` / `E0323` if invalid) |
| `Reflect::doc` | `pub halt meta fn doc<T>(target: Type<T>) -> ?str` | Attached `--\|` outer doc text on nominal, opaque, or sum `T` (`None` if absent or structural) |
| `Reflect::field_doc` | `pub halt meta fn field_doc<T>(target: Type<T>, meta key: str \|> Key<UnwrapOrSelf<T>>) -> ?str` | Attached `--\|` doc text on root record field `key` of nominal or visible opaque `T` (`None` if absent or structural) |
| `Reflect::variant_doc` | `pub halt meta fn variant_doc<T>(target: Type<T>, meta variant: str) -> ?str` | Attached `--\|` doc text on sum variant `variant` |
| `Reflect::has_default` | `pub halt meta fn has_default<T>(target: Type<T>, meta key: str \|> Key<UnwrapOrSelf<T>>) -> bool` | `true` iff `T` is a nominal or visible opaque record declaration whose root field `key` declares `= expr` (`false` for structural types, including transparent `type` aliases) |

### Structural Type Pattern Matching

Static tokens use ordinary `MatchExpr` with any token-valued subject expression. Type patterns match the represented type. Bare literals within a type pattern are limited to const-argument positions.

```ebnf
TypePattern          ::= "<" TypePatternInner ">"
TypePatternInner     ::= "_"
                       | "let" PascalCase
                       | TypeTuplePattern
                       | TypeRecordPattern
                       | TypeArrayPattern
                       | TypeMapPattern
                       | RigidNominalPattern
                       | PrimitivePattern
                       | LiteralPattern

TypeTuplePattern     ::= "(" ")"
                       | "(" TypePatternMember "," TypePatternTupleTail ")"
TypePatternTupleTail ::= TypeRestPattern [ "," ]
                       | TypePatternMember { "," TypePatternMember } [ "," TypeRestPattern ] [ "," ]

TypePatternMember    ::= "_"
                       | [ MemberMode ] TypePatternInner
                       | "let" PascalCase TypePatternInner

TypeRecordPattern    ::= ".{" [ TypeRecordPatternList ] "}"
TypeRecordPatternList::= TypeRestPattern [ "," ]
                       | TypePatternField { "," TypePatternField } [ "," TypeRestPattern ] [ "," ]

TypePatternField     ::= [ MemberMode ] FieldLabel ":" ( TypePatternInner | "_" )
                       | "let" PascalCase FieldLabel ":" ( TypePatternInner | "_" )

TypeRestPattern      ::= ".." [ PascalCase ]
TypeArrayPattern     ::= "[" [ ElementAccessMode ] "]" TypePatternInner
TypeMapPattern       ::= "[" TypePatternInner ":" [ ElementAccessMode ] TypePatternInner "]"
RigidNominalPattern  ::= QualifiedName [ "<" TypePatternArg { "," TypePatternArg } [ "," ] ">" ]
TypePatternArg       ::= TypePatternInner | MemberModeLiteral
PrimitivePattern     ::= PrimitiveType
```

- **Scoped Pattern Variables (`let U`, `let M`)**: `let U` introduces a target-type variable; `let M` binds `MemberMode`. Bare `PascalCase` identifiers denote rigid nominal type matching.
- **Wildcards and Slices**: `_` matches any `MemberMode` or `Type`. Anonymous rest `..` matches trailing elements without binding. Named rests use `..Tail` or `..Rest`.
- **Tuple Slices and No 1-Tuple Invariant**: Ril has no 1-tuples (`()` is unit; `(T)` is scalar grouping). Anonymous `<(_, ..)>` matches tuples of arity $\ge 2$. Named `..Tail` fails if remaining components number 1.
- **Unique Pattern Binders (`E0347`)**: Each pattern branch binds an identifier at most once; multi-position equality is asserted via explicit guards (`if <A> == <B>`).
- **Rigid Application Head (`E0306`)**: Requires a known rigid type constructor; transparent aliases may expand. Primitive/structural patterns and whole-type `_`/`let U` remain legal.
- **Sorted Arguments**: A member-mode literal in a type pattern is admitted only in the corresponding constructor's member-mode argument position. It is not a whole-type pattern or an ordinary expression. Const literals retain their value-sorted argument restriction.

| Match evidence | Scope / invalidation |
| :--- | :--- |
| Subject evaluation | Evaluate once and match that token snapshot, including a variable or type-function result |
| `<User>` arm | Matched value is `Type<User>`; named source paths retain the fact only while unchanged |
| `<let U>` arm | Snapshot is `Type<U>`; U remains the original target even if a source slot is reassigned |
| Structural arm | Restore only the member/mode/identity facts actually proved by that pattern |
| Assignment / alias write | Invalidate affected source-path evidence; a fresh current static target may prove different facts |

```ril
-- User and field_size have the preceding declarations.
meta fn inspect_token<T>(token: Type<T>) -> int {
    match token {
        <User> -> field_size<User>(token, "id"),
        _      -> 0,
    }
}
meta let _ = {
    let tok: Type<User> = <User>
    match tok {
        <let U> -> {
            let snapshot = <U>
            assert(snapshot == <User>)
        },
    }
}
```

```ril
halt type RecordOnly = \T -> match <T> {
    <.{ .. }> -> <T>,
    _ -> <never>,
}
type EmptyRecord = RecordOnly<.{}>               -- .{}
type NotRecord = RecordOnly<int>                -- never

-- Deep Recursive Unwrapping of Container / Fallible Types:
type UnwrapAll = \T -> match <T> {
    <Result<let OkVal, _>> -> UnwrapAll<OkVal>,
    <Option<let SomeVal>>  -> UnwrapAll<SomeVal>,
    _                      -> <T>,
}

-- Element Extraction from Collections:
halt type ElementOf = \T -> match <T> {
    <[]let E>        -> <E>,
    <Set<let E>>     -> <E>,
    <[_: let V]>     -> <V>,
    _                -> <never>,
}

-- Tuple Destructuring:
halt type DeconstructTuple = \T -> match <T> {
    <(let Head, ..Tail)> -> <.{ head: Head, tail: Tail }>,
    _                    -> <never>,
}

-- Member Mode Pattern Destructuring:
-- A mode is a static value argument, not a field type or a literal type.
type ModeTag<M: MemberMode>
halt type DeconstructMember = \T -> match <T> {
    <(let M let Head, ..Tail)>         -> <.{ mode: ModeTag<M>, head: Head, tail: Tail }>,
    <.{ let M field: let U, ..Rest }>   -> <.{ mode: ModeTag<M>, field: U, rest: Rest }>,
    _                                  -> <never>,
}

type Nested = Option<Result<int, str>>
type Unwrapped = UnwrapAll<Nested>             -- int
-- UnwrapAll uses the evaluation budget: recursive type graphs need not have a finite wrapper depth.
type Elem = ElementOf<[]str>                   -- str
type HeadTail = DeconstructTuple<(u8, i32, f64)>-- .{ head: u8, tail: (i32, f64) }
type ExtractedTuple = DeconstructMember<(mut []int, str, bool)> -- .{ mode: ModeTag<mut>, head: []int, tail: (str, bool) }

-- Rejection of Non-Rigid Type Patterns (E0306):
-- type BadPattern = \T -> match <T> {
--     <(let M)<let U>> -> <U>,         -- Error [E0306]: rigid type pattern cannot bind constructor '(let M)' as a higher-kinded pattern variable
--     _                    -> <never>,
-- }
```

### Static Parameter Sorts and Adaptation Rules

Type functions accept the following parameter sorts and constraints:

- **Bare Types (`\T` or `\T: Type`)**: Accepts static type expressions (`E0306` on value).
- **Const Values (`\param: ValueType`)**: Accepts compile-time values (`E0814` on runtime value, `E0323` on sort mismatch), with optional pipeline constraints (`\key |> Key<T>` or `\key: str |> Key<T>`).
- **Bounded Structural Types (`\T: .{ id: int, .. }`)**: Structural bounds constrain types.
- **Higher-Kinded Constructors (`\M: Type -> Type`)**: Enforces constructor kind arity (`E0306`).
- **Default Arguments**: Follow trailing-default (`E0316`) and left-to-right scoping (`E0320`) rules.
- **Closed Type Sets (`\T: TypeSetSort`, `E0301`, `E0304`)**: Restricts the admitted domain to rigid types in the declared set (`\T: int | f64`). Incompatible rigid types trigger `E0301`. Passing an unspecialized type set triggers `E0306`. Static pattern matching covering all declared members is exhaustive; redundant `_` arms trigger `E0304`.
- **No Union Distribution (`E0306`, `E0318`)**: Type parameter `\T` accepts rigid types only (`E0306` on type set); type functions do not distribute over unions. Result must normalize to a single rigid token (`E0318`).

| Parameter | Kind / value category |
| :--- | :--- |
| `\T` / `\T: Type` | Type argument; a value expression is not admitted (`E0306`) |
| `\cap: int` | Static value argument of sort `int` |
| `\key \|> Key<T>` | Static key value argument constrained by `Key<T>` guard |
| `\M: Type -> Type` | Constructor receiving a type argument and producing a type |

```ril
type SchemaV1 = .{ id: int, name: str }
type SchemaV2 = .{ id: int, name: str, email: str }

type VersionedSchema = \version: int -> match version {
    1 -> <SchemaV1>,
    2 -> <SchemaV2>,
    _ -> <never>,
}

type ActivePayload = VersionedSchema<2>        -- SchemaV2; 2 supplies the declared const 'version'

type PickField = \T: .{ .. }, key: str |> Key<T> -> <T.(key)>
type UserName = PickField<SchemaV1, "name">    -- str

type Wrapper = \M: Type -> Type, T -> <M<T>>
type OptInt = Wrapper<Option, int>             -- Option<int>

-- Value/type argument separation:
type IntType = typeof 1024                     -- int
-- type BadValueArg = VersionedSchema<u8>      -- Error [E0323]: a type cannot supply const parameter 'version'
-- type BadTypeArg = Wrapper<1024, int>        -- Error [E0306]: a value cannot supply type parameter 'M'
-- type BadSetArg = Wrapper<Option, int | f64> -- Error [E0306]: unspecialized type set cannot supply type parameter 'T'
-- type BadUnionRet = \T -> <int | f64>        -- Error [E0318]: untagged unions cannot be quoted or returned as types
```

### Compile-Time Evaluation and Layout Queries

```ebnf
MetaLetDecl      ::= [ "pub" ] "meta" "let" ( ScreamingSnakeCase | "_" ) [ ":" TypeExpression ] "=" Expression
MetaFnDecl       ::= { MetaAttr } [ "pub" ] [ "halt" ] "meta" "fn" ValueName [ GenericParams ]
                     "(" [ ParameterList ] ")" ReturnSpec [ SignatureWhereClause ] Block
```

`meta let` and `meta fn` evaluate in the pure static domain, which permits implicit Diverge under the compiler's root budget. `halt meta fn` is an optional additional assertion of absence of Diverge; neither declarations nor roots must use it. Only ordinary results recursively free of tokens, static-only metatypes, and type-producing authority may become immutable run-time constants. Token-valued `meta let` bindings remain static. Type functions may consume static values to select shapes; arithmetic on sizes follows ordinary integer rules.

A run-time value-expression read of a module-level meta constant retains its named source obligation under [External State Tracking](#external-state-tracking). Static/type-domain reads have no such run-time obligation.

```ril
meta let ANSWER = 42
fn answer() &up(sub){ANSWER} -> int { ANSWER }
-- fn hidden_answer() -> int { ANSWER } -- Error [E0510]
meta let _ = assert(ANSWER == 42)
```

```ril
meta fn align_to(offset: int, alignment: int) -> int {
    assert(offset >= 0 && alignment > 0)
    assert((alignment & (alignment - 1)) == 0)
    (offset + alignment - 1) & ~(alignment - 1)
}
halt type BufferShape = \capacity: int ->
    if capacity <= 64 {
        <.{ inline_data: []u8, len: int }>
    } else {
        <.{ chunks: [][]u8, capacity: int, len: int }>
    }
meta let CAPACITY = align_to(60, 16)
type Buffer = BufferShape<CAPACITY>
meta let _ = assert(CAPACITY == 64)
-- meta let _ = assert(CAPACITY == 32) -- Error [E0830]: failed static assertion
```

Shape declarations promise no packed order, offsets, pointer size, or external binary layout.

```ril
-- Language-defined static declaration exposed by the prelude:
-- pub meta fn byte_size<T>(token: Type<T>) -> int
meta let BYTE_SIZE = byte_size(<u8>)
meta let _ = assert(BYTE_SIZE == 1)
-- let runtime_size = byte_size(<u8>) -- Error [E0810]: query requires static evaluation
-- let bad_bare = byte_size(u8)       -- Error [E0319]: bare type in expression context
```

| `byte_size` contract | Rule |
| :--- | :--- |
| Input | A `Type<T>` token; query its represented target, not the token implementation. Bare type names must not be passed (`E0319`) |
| Result | Nonnegative `int` size of the represented target's value/handle on the selected abstract target; not its reachable graph |
| Layout domain | Static-only metatypes such as `Type<User>`, and shapes requiring their materialization, have no ordinary run-time layout (`E0306`) |
| Phase | Static only; finite; usable by meta/type computations and other required static evaluations |
| Ordinary execution | `E0810`; a `meta let` result may be used as an ordinary constant |
| Visibility | Prelude declaration with ordinary lexical shadowing; not reserved syntax |
| Layout | May depend on the abstract target; grants no packed layout or field-offset guarantee |

## Modules, Program Execution, and Prelude

### Modules and Compilation Units

```ebnf
SubDecl ::= { MetaAttr } [ "pub" ] "sub" PascalCase "{" { SubItem Separator } [ SubItem ] "}"
SubItem ::= UseDecl | SubDecl | FunctionDecl | MetaFnDecl | MetaLetDecl
          | LetDecl | LetMutDecl | SharedMutDecl | VarDecl | VarMutDecl
          | LetRefDecl | VarRefDecl | OpaqueTypeDecl | TypeDecl | NominalDecl
          | SumTypeDecl | EffectDecl
```

```ril
-- 1. In file: math/geometry.ril (Library Implementation sub -> Geometry)
let PI = 3.141592653589793              -- Private to file sub 'Geometry'
pub let TAU = 6.283185307179586         -- Public immutable constant
var call_count = 0                      -- Private mutable state
-- pub var shared_count = 0             -- Error [E0906]: mutable static state cannot be 'pub'
-- pub let mut shared_buf: []int = []   -- Error [E0906]: mutable static handle cannot be 'pub'
-- use Super::{PI}                      -- Error [E0208]: file root has no enclosing 'Super' scope

fn record_call() &up(sub){mut call_count} -> () { call_count += 1 }

pub sub Transform {
    -- Hermetic scope: only Prelude is ambient; access enclosing scope via 'Super::'
    -- let bad = PI                     -- Error [E0204]: 'PI' is not in scope without 'Super::'
    -- fn touch() &up(Super){mut call_count} -> () { Super::call_count += 1 }
    -- Error [E0201]: parent mutable state is strictly private to its defining scope

    pub fn scale_tau(k: f64) &Super::record_call &up(Super){TAU} -> f64 {
        Super::record_call()            -- OK: 'Super::' accesses enclosing non-pub declarations
        Super::TAU * k
    }
}

-- 2. In file: platform/fs.d.ril (External Interface Declaration sub -> Fs)
pub type FileHandle
pub sub AsyncIo {
    pub fn read_file(path: str) @Fiber -> Result<[]u8, str>
}

-- 3. In file: app/main.ril (Executable Root Unit: non-sub, cannot be imported)
use math/geometry::{TAU}
use math/geometry::Transform
use platform/fs::AsyncIo::{read_file}
-- use app/main                         -- Error [E0208]: executable root is not an importable 'sub'

let APP_VERSION = 1
-- pub let EXPORTED = 1                 -- Error [E0905]: executable root cannot declare top-level 'pub'
-- pub sub Exposed {}                   -- Error [E0905]: executable root cannot declare top-level 'pub'

sub Metrics {                           -- OK: private inline sub inside executable root
    var requests = 0
    pub fn bump() &up(sub){mut requests} &up(Super){APP_VERSION} -> int {
        requests += Super::APP_VERSION  -- OK: 'Super::' reads root non-pub constant
        requests
    }
}

fn main() @Fiber &Metrics::bump -> () {
    let _ = Metrics::bump()
}
```

| Unit / Scope | `sub` Identity | Top-Level `pub` | `fn main` | Hermetic / Visibility Rules |
| :--- | :--- | :--- | :--- | :--- |
| **Executable Root (`.ril`)** | Non-`sub`; unimportable (`E0208`) | Prohibited (`E0905`; `pub fn main` is `E0904`) | Required ordinary root `fn main` (`E0903`) | Enclosing scope for its inline `sub`s via `Super::` |
| **Library File (`.ril`)** | File is `sub` (`to_pascal_case(stem)`) | Allowed on immutable/type/fn/eff/sub/use items | Prohibited (`E0904`) | Private by default (`E0201`); mutable state is never `pub` (`E0906`) |
| **External Contract (`.d.ril`)** | File is `sub` (`to_pascal_case(stem)`) | Allowed on bodyless contract items | Prohibited (`E0901` / `E0904`) | `DeclSub` enforces `.d.ril` rules recursively (`E0901`) |
| **Inline `sub` (`[pub] sub Name`)** | `PascalCase` (`E0101`/`E0102`); `Super` is `E0203` | Allowed inside `sub` (mutable state is `E0906`) | Prohibited (`E0904`) | Hermetic (Prelude only); `Super::` reaches enclosing non-mutable items; downward access requires `pub` (`E0201`) |

Inline `sub` declarations are permitted only at file top-level or directly inside another `sub` (rejected in sequential statements with `E0703`, block `where` with `E0702`, and signature `where` with `E0704`).

### Module Imports and Visibility

```ebnf
UseDecl    ::= [ "pub" ] "use" FilePath [ "as" PascalCase ]
             | [ "pub" ] "use" ModulePath "::" ( "{" ImportList "}" | "*" | ImportItem )
FilePath   ::= SnakeCase { "/" SnakeCase }
ModulePath ::= FilePath { "::" PascalCase }
             | "Super" { "::" "Super" } { "::" PascalCase }
             | PascalCase { "::" PascalCase }
ImportList ::= ImportItem { "," ImportItem } [ "," ]
ImportItem ::= Identifier [ "as" Identifier ]
```

#### Normative Module Import Rules

```ril
-- Fixture module math/numbers.ril exports ONE; math/absent does not exist.
-- use math/absent                      -- Error [E0208]: no module at this path
-- use math/numbers::{TWO}              -- Error [E0209]: no member TWO in the resolved module
use math/numbers::{ONE}                 -- OK
```

An unresolved module or `Super::` path is `E0208`. A selective import or qualified access naming an absent member is `E0209`. An inaccessible member is `E0201`; an unavailable ordinary lexical name is `E0204`. Import name collisions and protected names (`Type`, `Super`) are `E0203`.

- **File-to-`PascalCase` Mapping (`to_pascal_case`)**:
   - `use FilePath` without `::` or `as` binds `to_pascal_case(last_segment)` in the current scope (`math/geometry` $\rightarrow$ `Geometry`, `data/string_builder` $\rightarrow$ `StringBuilder`, `crypto/sha256_hash` $\rightarrow$ `Sha256Hash`).
   - Every `_`-separated segment in a module file name must begin with `[a-z]`, and the derived `PascalCase` name must satisfy acronym title-casing (`E0102`, rejecting single-letter prefixes before letters such as `a_b` $\rightarrow$ `AB` and digit-leading segments after `_` such as `sha_256`) and protected-name rules (`E0203`, rejecting `super.ril`).
- **Path Separators (`/` vs `::`) and `Super::`**:
   - `/` separates `snake_case` file-system segments (`FilePath`); `::` navigates `PascalCase` `sub` namespaces and member projections (`E0101`).
   - `Super` is valid as a leading `Super::` prefix (`use Super::...` or `Super::member`) or as a module owner in `&up(Super){...}` / `&up(Super::Child){...}`, stepping into the immediately enclosing `sub` or root file scope.
- **Scoping & Re-Exports**:
   - A `use` declaration resolves imports in its enclosing file, `sub`, or block scope. Re-exporting a parent mutable binding via `pub use Super::{...}` is rejected under `E0906`.

```ril
-- 1. Automatic PascalCase Namespace Binding & Explicit Aliasing:
use math/geometry                       -- Binds 'Geometry'
let area = Geometry::circle_area(5.0)
use ril/crypto as Hash                  -- Overrides derived name with 'Hash'
-- use ril/crypto as hash               -- Error [E0101]: alias must be PascalCase
-- use ril/crypto as Super              -- Error [E0203]: 'Super' is protected
-- use math/Geometry                    -- Error [E0101]: file path segments must be snake_case
-- use net/a_b                          -- Error [E0102]: derived 'AB' violates PascalCase acronym rule
-- use crypto/sha_256                   -- Error [E0102]: segment after '_' must start with [a-z]

-- 2. Nested Inline sub & Super:: Imports:
use math/geometry::Transform            -- Binds inline sub 'Transform' from 'math/geometry'
use math/geometry::Transform::{scale_tau as scale}
pub use ril/math::*                     -- Glob re-export of public items

sub Outer {
    type Shared = int
    var count = 0
    pub sub Sibling { pub fn ping() -> Shared { 1 } }
    pub sub Child {
        use Super::{Shared, Sibling}    -- OK: imports enclosing private type and sibling sub
        -- pub use Super::{count}       -- Error [E0906]: cannot re-export mutable binding
        pub fn run() -> Shared { Sibling::ping() }
    }
}

-- 3. Block-Scoped Import:
fn calculate() -> () {
    use ril/crypto::{sha256}
    let _ = sha256("data")
}
```

### Top-Level Initialization and Purity

- Top-level initialization in root and `sub` scopes has no observable effects (`E0202`); mutable variables require constant initializers and cannot be marked `pub` (`E0906`).
- Ordinary `let` requires immutable data. Foreign resource constants expose stable descriptors with separate operation contracts.
- Postfix `?` outside a callable is `E0205`, including module initializers.

```ril
let MAX_CONNECTIONS: int = 100
pub let DEFAULT_TITLE: str = "Ril Application"
var active_workers: int = 0            -- OK: private mutable state with constant initializer
fn start_worker() &up(sub){mut active_workers} -> () { active_workers += 1 }

-- Prohibited top-level visibility, side effects, and error propagation:
-- pub var exposed_workers: int = 0     -- Error [E0906]: mutable state cannot be declared 'pub'
-- let current_time = Clock::now()      -- Error [E0202]: top-level declaration must be a pure constant expression
-- let db = Database::connect("db.loc") -- Error [E0202]: top-level declaration cannot invoke runtime I/O or effects
-- let top_parse = parse_id("10")?      -- Error [E0205]: postfix '?' operator used outside function or closure body
```

### Test Conventions and Execution Protocol

Tests are ordinary functions. Their handlers, scoped bindings, Result inspection duties, and panic boundaries obey the same rules as other functions.

### Program Entry Point

```ril
-- Complete executable root; no root main is declared.
fn helper() -> () {}                  -- Error [E0903]: executable program lacks its root main
```

An executable program without its required root `main` declaration is `E0903`. A declaration that violates the entry contract or declares `fn main` inside a `sub` is `E0904`. Top-level `pub` on non-entry declarations in the executable root is `E0905`. Duplicate declarations of root `main` retain `E0203`.

```ril
fn main() @Fiber -> () {
    println("Hello, Ril!")
}

-- Alternative complete fallible executable root:
use ril/file
fn main() @Fiber -> Result<(), str> {
    let config = File::read("config.json")?
    if config == "" {
        Err("empty configuration")     -- Runtime halts with non-zero exit code (1)
    } else {
        Ok()                            -- Exits cleanly with status code (0)
    }
}
```

```ril
-- Separate executable-root and sub entry violations:
-- pub fn main() -> () {}                    -- Error [E0904]: entry must not be public
-- fn main(value: int) -> () {}              -- Error [E0904]: entry has a parameter
-- fn main<T>() -> () {}                     -- Error [E0904]: entry has a generic parameter
-- fn main() -> int { 0 }                    -- Error [E0904]: unsupported entry result
-- sub Inner { fn main() -> () {} }          -- Error [E0904]: 'main' cannot be declared inside a 'sub'
-- pub fn extra() -> () {}                   -- Error [E0905]: top-level 'pub' is prohibited in executable root
```

| Entry property | Requirement |
| :--- | :--- |
| Declaration | Non-public ordinary named Ril function at executable root top-level; `halt` is allowed subject to its usual checks |
| Value / generic parameters | None, including defaulted parameters |
| Result | `()` or the language's `Result<(), str>`, after transparent alias expansion |
| Effects / state | Ordinary declaration and provenance rules; undeclared residual operational effects remain `E0612`; implicit Diverge is allowed without an annotation or handler |
| Residual user-defined effect or `@Scope` | No program-environment handler; `E0612` even if listed on main |

| Completed program outcome | Environment behavior |
| :--- | :--- |
| `()` or `Ok()` after required cleanup/barriers | Exit status 0 |
| `Err(message)` | Inspect the result; write the message and one LF to standard error, then exit status 1 |
| Reporting the error fails | Exit status 1; no successful outcome or further output guarantee |
| Uncontained panic / fatal / double fault / cancellation | Non-zero exit status (exit status 1 for panic/cancellation; immediate termination for `@Fatal`); explanatory diagnostics are not fixed text |
| Declared `Fiber` / `Concurrent`, including `Async` | Supply their specified system operations on targets providing those runtime capabilities; unsupported target profiles reject them on `main` (`E0612`) |
| Implicit `Diverge` / `Panic` / `Fatal` | No operation to service; ordinary `main` need not be marked `halt` |

Environment reporting occurs outside main's invocation and adds no effect obligation to main. A normal main result produced by an outward abortive source handler follows the outcome table after cleanup. Child-local effect confinement and termination follow their defining rules.

### Prelude Scope

The prelude is an ambient lexical scope enclosing every compilation unit, including inline `sub`s.

| Binding category | Access |
| :--- | :--- |
| Built-in functions below | Bare names: `len`, `clone`, `derive`, `diverge_budget`, `absorb_panic`, `panic`, `fatal`, `assert`, etc. |
| Library modules below | Whole public namespace through `Module::member` |
| Standard types / sorts | `Option<T>`, `Result<T, E>`, `Set<T>`, `BudgetError`, `PanicError`, `MemberMode`. Constructors follow ordinary resolution |
| Effect labels / sets | Operational: `Fiber`, `Concurrent`, `Async`, `Yield<T>`; implicit non-operational (semantic interfaces only): `Diverge`, `Panic`, `Fatal` |
| Static type operations | `SharedObject`, `LenTarget`, `Tuple`, `NominalWrapper`, `Unwrap` |
| Scoped draft type | `Draft<T>` in [recipe and helper contracts](#normative-rules-for-functional-updates) |
| Language constructs | Primitive types, `Type`, `Type<T>`, `?T`, and collection syntax |
| Explicit `use` | Ordinary module aliases or selected member bindings in the declaring scope |
| Shadowing | Inner declarations may shadow prelude bindings; `Type` and `Super` retain their protected-name rules |

| Prelude module | Source |
| :--- | :--- |
| `Array` | `ril/array` |
| `Map` | `ril/map` |
| `Set` | `ril/set` |
| `String` | `ril/string` |
| `Bytes` | `ril/bytes` |
| `Numeric` | `ril/numeric` |
| `Reflect` | `ril/reflect` |

| Explicit library modules | Sources | Role |
| :--- | :--- | :--- |
| `Math`, `Crypto` | `ril/math`, `ril/crypto` | Specialized computation |
| `File`, `Io`, `Os` | `ril/file`, `ril/io`, `ril/os` | Target-runtime I/O and environment |
| `Concurrent`, `Channel` | `ril/concurrent`, `ril/concurrent/channel` | Target-runtime structured concurrency and channels |
| `Parallel` | `ril/parallel` | Deterministic data parallelism (multi-core or sequential target lowering) |
| `Platform` | `ril/platform` | Compile-time target platform constants (`OS`, `ARCH`, `ENDIAN`, `POINTER_BITS`) |

Other standard-library modules use explicit imports with their specified effect, resource, and execution contracts.

```ril
-- Canonical declarations in ril/platform:
-- pub type Os { Linux, Macos, Windows, Freebsd, Wasi, Unknown }
-- pub type Arch { X86_64, Aarch64, Riscv64, Wasm32, Unknown }
-- pub type Endian { Little, Big }
-- pub meta let OS: Os
-- pub meta let ARCH: Arch
-- pub meta let ENDIAN: Endian
-- pub meta let POINTER_BITS: int

use ril/platform
pub halt fn path_separator() &up(Platform){OS} -> str {
    match Platform::OS {
        Platform::Os::Windows -> "\\",
        _                     -> "/",
    }
}
```

```ril
type UserId(int)
assert(inner(UserId(1001)) == 1001)
let original = [1, 2, 3]
let mut detached = clone(original)
detached |> mut Array::push(4)
assert(original == [1, 2, 3] && len(ref detached) == 4)
let snapshot = clone(ref detached)
let revised = .{ theme: "dark" } |> derive \mut draft -> {
    draft.theme = "light"
}
assert(revised.theme == "light" && len(snapshot) == 4)
let count = len([1, 2, 3])
println("Count: {count}")
assert(String::scalars("Ril") == [82u32, 105u32, 108u32])
assert(Numeric::convert<int>(255u8) == Some(255))
-- let missing = scalars("Ril")        -- Error [E0204]: library members use their module name
```

```ril
use ril/parallel
halt fn squares(values: []int) -> []int {
    values |> Parallel::map(\value -> value * value)
}
fn live_squares(ref values: []int) -> []int {
    values |> ref Parallel::map(\value -> value * value)  -- Zero-copy observation; no halt
}
```

#### Built-in Foundational Operations

Ril defines the following built-in foundational operations directly in the language prelude:

```ril
assert(len("Ril") == 3 && len(bytes"RIFF") == 4)
let original = [1, 2, 3]
let mut copy = clone(original)
copy[0] = 9
assert(len(ref copy) == 3 && copy[0] == 9 && original[0] == 1)
-- len(ref "Ril")                    -- Error [E0401]: text is a value type
-- clone(42)                         -- Error [E0301]: int does not satisfy SharedObject
-- clone(ref 42)                     -- Error [E0401]: use ordinary value passage
```

The `via` inputs of `len`, `inner`, and `clone` admit ordinary reception and explicit `ref` observation as shown below. Each operation also checks its type guard and primitive eligibility.

| Input | Ordinary form | Explicit `ref` form |
| :--- | :--- | :--- |
| Value type, including `str` / `bytes` | Receive value | `E0401` |
| Immutable shared-object data | Receive immutable data | Observe same data |
| Live shared-object data | `E0535` | Observe without freezing |

Forms preserve data schemas and operation identity; resource operations require their own contracts. Operators, projections, indexing and traversal use primitive observation rules, while ordinary parameters use reception rules.

Built-in operations use the same surface signature forms as user-defined Ril functions, including access-mode templates (`via`/`infer`) and pipeline guards. Each operation has one prelude declaration. Same-scope duplicates follow `E0203`. Guards, access alternatives, and inferred contracts are static judgments and introduce no additional run-time conditions for the selected operation. Primitive eligibility, phase, and execution rules below complete the displayed signatures. Complexity describes ordinary-data work, excluding argument evaluation, automatic-memory-management overhead, and user recipe/callback work. Graph work includes regions visited or copied to preserve aliases and cycles.

| Operation | Canonical declaration | Effects | Phase | Complexity | Contract |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `len` | `pub halt fn len<T \|> LenTarget>(via item: T) -> int` | None | Dual-phase | $O(1)$ / $O(n)$ text | Count of elements, entries, bytes, or Unicode scalars |
| `inner` | `pub fn inner<W \|> NominalWrapper>(via wrapper: W) -> infer Unwrap<W>` | None | Run-time | $O(1)$ | Preserve immutable/observed payload authority; value payloads use a plain result; unit nominal yields `()` |
| `clone` | `pub fn clone<T \|> SharedObject>(via value: T) -> new T` | None | Run-time | $O(\text{visited + materialized})$ | Isolated construction `new T` for ordinary shared-object data |
| `derive` | `pub fn derive<T \|> SharedObject>(base: T, recipe: fn(mut draft: Draft<T>) @& -> ()) -> T` | Forwards recipe | Run-time | No uniform complexity guarantee | Path updates on an immutable shared-object root via a confined draft |
| `diverge_budget` | `pub fn diverge_budget<T>(limit: u64, action: fn() @& -> T) -> Result<T, BudgetError>` | Forwards action minus `Diverge` | Dual-phase | See [charging rules](#allowance-and-charging) | Covered finite evaluation; preserves other effects and state/provenance obligations |
| `absorb_panic` | `pub fn absorb_panic<T>(action: fn() @& -> T) -> Result<T, PanicError>` | Forwards action minus `Panic` | Run-time | $O(1)$ boundary + action | Unwind-safe synchronous `@Panic` containment (`E0608`); does not intercept `@Fatal` |
| `byte_size` | `pub meta fn byte_size<T>(token: Type<T>) -> int` | None | Static only | $O(1)$ | Size of the represented target's value/handle; static-only targets have no run-time layout |
| `type_name` | `pub meta fn type_name<T>(token: Type<T>) -> str` | None | Static only | $O(\text{len})$ | Diagnostic description of the token's target, including static metatypes; spelling does not determine type identity |
| `coords` | `pub meta fn coords<T>(token: Type<T>) -> [](MemberMode, CoordKey<T>)` | None | Static only | $O(\text{members})$ | Enumerate member modes and coordinates for record or tuple product types; non-product targets trigger `E0358` |
| `variants` | `pub meta fn variants<T>(token: Type<T>) -> []str` | None | Static only | $O(\text{variants})$ | Enumerate variant constructor names for sum types; non-sum targets trigger `E0301` |
| `Key` | `pub halt type Key = \key: CoordKey<T>, T -> match <T> { <.{ .. }> -> if coords(<T>) \|> Array::any(\(m, k) -> k == key) { <()> } else { <never> }, <()> \| <(_, ..)> -> if coords(<T>) \|> Array::any(\(m, k) -> k == key) { <()> } else { <never> }, _ -> <never> }` | None | Static only | $O(\text{members})$ | Pipeline constraint guard verifying coordinate `key` belongs to product target `T`; invalid key yields `<never>`, intercepted by `E0323` |
| `panic` | `pub halt fn panic(message: str) -> never` | Implicit `@Panic` | Dual-phase | Finite | Initiates LIFO panic unwinding at run time; stops static evaluation with `E0831` |
| `fatal` | `pub halt fn fatal(message: str) -> never` | Implicit `@Fatal` | Dual-phase | Finite | Terminates the OS process immediately without unwinding at run time; stops static evaluation with `E0831` |
| `assert` | `pub halt fn assert(condition: bool, message: str = "assertion failed") -> ()` | Implicit `@Panic` unless `condition` is statically `true` | Dual-phase | $O(1)$ | Panics on false condition; static failure is `E0830` |
| `print` | `pub fn print(text: str) @Fiber -> ()` | `@Fiber` | Run-time | $O(\text{len})$ | Writes UTF-8 text to standard output without trailing newline |
| `println` | `pub fn println(text: str) @Fiber -> ()` | `@Fiber` | Run-time | $O(\text{len})$ | Writes UTF-8 text followed by one LF byte (`\n`) to standard output |

#### Normative Rules for Built-in Operations

`SharedObject`, `LenTarget`, `Tuple`, and `NominalWrapper` are pure type guards of kind `Type -> Type`. Each produces `<T>` on an admitted input `T` and `<never>` otherwise. Transparent aliases follow the ordinary type identity rules. The guards inspect types during checking and preserve the admitted input's identity and member modes.

| Guard | Admitted input |
| :--- | :--- |
| `SharedObject` | Ordinary record, nonempty tuple, array, map, set, or sum roots with any legal member or storage modes, including nominal or opaque types with an ordinary shared-object representation. Value, callable, resource, and scoped-authority roots are excluded. Across an opaque boundary the guard uses the checked representation category and preserves the sealed identity. Graph eligibility and actual access are separate checks |
| `LenTarget` | `str`, `bytes`, arrays, maps, sets, and `Parallel::Slice` views with any legal storage or member modes. A nominal wrapper requires explicit unwrapping. An opaque representation is available only in its exact defining scope |
| `Tuple` | Visible tuple types of arity zero or at least two, with any legal member modes |
| `NominalWrapper` | Visible nominal wrapper declarations, including unit nominal declarations. Sum and opaque declarations introduce no such wrapper |

The following definition gives the `Tuple` guard's behavior under the [structural type-pattern rules](#structural-type-pattern-matching). The `<(_, ..)>` pattern covers all tuples with arity $\ge 2$, while `<()>` matches the empty unit tuple:

```ril
halt type Tuple = \T -> match <T> {
    <()>      -> <T>,
    <(_, ..)> -> <T>,
    _         -> <never>,
}
meta let _ = assert(<Tuple<(var int, str)>> == <(var int, str)>)
meta let _ = assert(<Tuple<(int, str, bool)>> == <(int, str, bool)>)
meta let _ = assert(<Tuple<(int)>> == <never>)
meta let _ = assert(<Tuple<()>> == <()>)
meta let _ = assert(<SharedObject<()>> == <never>)
```

```ril
type Cell = .{ var count: int }
meta let _ = assert(<SharedObject<[mut]Cell>> == <[mut]Cell>)
meta let _ = assert(<LenTarget<[str: ref Cell]>> == <[str: ref Cell]>)
```

`Unwrap<W>` is a static type operation on `W |> NominalWrapper`. It produces the wrapper's immediate payload type with its declared member modes, or `()` for a unit nominal. `inner` uses this type and derives the result access and provenance separately. `Draft<T>` follows the [scoped draft rules](#normative-rules-for-functional-updates). `CoordKey<T>` is the associated coordinate key sort: `str` for record product types and `int` for tuple product types.

An ineligible type argument normally fails its guard with `E0301`. At the built-in call boundary, apply the specific diagnostics for value-type argument modes (`E0401`), opaque unwrapping (`E0308`), non-clonable authority (`E0530`), and invalid `derive` inputs (`E0536`) under their defining rules.

- **Length Invariant (`len`)**:
  - `len` is a pure, dual-phase built-in operation admitted in both runtime and static contexts.
  - `len(ref value)` observes shared-object data; `len(value)` receives immutable data.
  - For `str`, returns the total number of Unicode scalar values, matching `s[a..b]` scalar indexing.
  - For `bytes`, returns the byte count in $O(1)$ time.
  - For arrays (`[]T`), returns the element count in $O(1)$ time.
  - For maps (`[K: V]`), returns the number of key-value pairs in $O(1)$ time.
  - For sets (`Set<T>`), returns the number of unique elements in $O(1)$ time.
  - For parallel views (`Parallel::Slice<T, M>`), returns the slice length in $O(1)$ time at run time.
  - Counts and string UTF-8 byte extents obey the [collection extent limit](#collection-extents-and-index-types); `len` returns the exact count.
- **Unwrapping Invariant (`inner`)**:
  - Unwraps nominal type wrappers to their underlying declared representation ([Nominal Type Wrappers](#nominal-type-wrappers)).
  - `inner(ref wrapper)` preserves observed payload provenance; ordinary `inner(wrapper)` receives immutable data.
  - Single-payload nominal wrapper `type UserId(int)` unwraps to its payload (`int`). Unit nominal wrapper `type Marker` unwraps to `()`.
  - The defining scope's opaque representation boundary remains enforced; `inner` does not unwrap opaque types or expose an inaccessible representation.
- **Copying** follows [deep immutability](#deep-immutability). Channel sender duplication uses [`Channel::clone_sender`](#structured-concurrency-channels).
- **Functional updates** follow the [draft rules](#normative-rules-for-functional-updates).
- **Static Layout Query (`byte_size`)**:
  - `pub meta fn byte_size<T>(token: Type<T>) -> int` queries the represented target's nonnegative value/handle size ([Compile-Time Evaluation and Layout Queries](#compile-time-evaluation-and-layout-queries)). Static-only metatypes have no ordinary layout (`E0306`).
  - Static-only: permitted during compile-time static evaluation (`meta let`, type functions); calling `byte_size` in runtime code is `E0810`. Bare type names cannot be passed directly (`E0319`); pass `<T>`.
  - Grants no packed layout, field offset, or external ABI alignment guarantees.
- **Defect Initiation, Panic Absorption, and Process Termination (`panic`, `assert`, `absorb_panic`, `fatal`)**:
  - `panic(message: str) -> never` introduces implicit `@Panic`: at run time it initiates LIFO stack unwinding; in static evaluation it aborts with `E0831: StaticEvaluationPanicError`.
  - `assert(condition: bool, message: str = "assertion failed") -> ()` evaluates its arguments eagerly before the call; if `condition` is false, it panics (`E0830` in static evaluation).
  - `absorb_panic<T>(action: fn() @& -> T) -> Result<T, PanicError>` is run-time only (`E0810` in static evaluation) and requires an unwind-safe `action` (`E0608`); it converts `@Panic` unwinding inside `action` into `Err(PanicError::Panicked(message))` after `action`'s local LIFO cleanups ([Panic Absorption with absorb_panic](#panic-absorption-with-absorb_panic)).
  - `fatal(message: str) -> never` introduces implicit `@Fatal`: at run time it writes `message` to standard error and terminates the OS process immediately without unwinding or cleanup, bypassing `absorb_panic`, `diverge_budget`, handlers, and `scope`; in static evaluation it aborts with `E0831`.
- **Standard Output Invariants (`print`, `println`)**:
  - `print` and `println` write UTF-8 encoded text to host standard output under the `@Fiber` system effect.
  - `println` appends exactly one LF byte (`0x0A`, `\n`) without host-specific newline conversions (e.g. no CRLF translation).
  - Both convenience operations panic on unrecoverable host I/O failure; fallible streaming I/O is provided separately by `ril/io`.
  - Concurrent writes across tasks may interleave at arbitrary byte boundaries without synchronization.
- **Prelude Shadowing and Integrity**:
  - Lexical declarations in inner scopes may shadow ordinary prelude names such as `clone`, `len`, and `assert`; protected `Type` is excluded.

```ril
type UserId(int)
type Marker
let id: int = inner(UserId(7))       -- OK: immediate value payload
let unit: () = inner(Marker)        -- OK: unit nominal
-- inner(7)                         -- Error [E0301]: int does not satisfy NominalWrapper
```

### Mandatory Inspection of Fallible Results

```ril
fn save_profile(user_id: int) -> Result<(), str> {
    if user_id <= 0 { Err("invalid id") } else { Ok() }
}

fn process_request(id: int) @Fiber -> Result<(), str> {
    -- Prohibited: discarding fallible Result without inspection
    -- save_profile(id)                 -- Error [E0720]: unused fallible Result must be handled

    -- Compliant Alternative 1: Postfix '?' error propagation
    save_profile(id)?

    -- Compliant Alternative 2: Explicit pattern matching
    match save_profile(id) {
        Ok() -> println("Profile saved"),
        Err(e) -> println("Save failed: {e}"),
    }

    -- Compliant Alternative 3: Fallback error closure
    save_profile(id) ?? \err -> println("Handled fallback: {err}")

    Ok()
}
```

```ril
let result: Result<int, str> = Ok(1)
let alias = result
assert(alias is Ok(_))                 -- OK: discharges the same result's obligation
```

Every produced Result carries an obligation to inspect, propagate, unpack, or return it (`E0720`). Track obligations by production independently of storage sharing.

| Operation / exit | Inspection duty |
| :--- | :--- |
| Actual success/error tag test | Inspected; any alias discharges the same produced Result |
| `is` wildcard / expected-value equality | No Result inspection by itself; only reached constructor/tag tests discharge their Results |
| Binding, alias, wrapping, aggregate, Task / Channel | Preserve one obligation, not one per name ([task handles](#task-handles-movable-guard-and-combinators), [channels](#structured-concurrency-channels)) |
| Deep copy | Preserve copied Results' obligations; copying is not inspection |
| `_`, overwrite, removal, lost last path | Do not discharge |
| Outer tag test | Does not inspect an inner Result |
| `?` | Propagates failure to the enclosing callable |
| Normal completion, including `Err` return | Cannot abandon other outstanding Results |
| Abnormal unwinding | May discard; [structured cancellation](#structured-cancellation-and-fault-precedence) keeps its specified rules |

---

## Diagnostic Error Codes Summary

This index assigns each code its diagnostic name and points to its defining rules; it introduces no additional rejection conditions. Codes are not reused for unrelated conditions. Specificity and multiple-error reporting follow [diagnostic classification](#diagnostic-classification).

### Source Text, Identifiers, and Syntax

| Code | Diagnostic and defining rule |
| :---: | :--- |
| **`E0101`** | [`InvalidIdentifierCasingError`](#identifiers-and-casing-invariants) |
| **`E0102`** | [`MalformedIdentifierSyntaxError`](#identifiers-and-casing-invariants) |
| **`E0103`** | [`PatternCasingCollisionError`](#identifiers-and-casing-invariants) |
| **`E0104`** | [`InvalidSourceEncodingError`](#character-set-and-encoding) |
| **`E0105`** | [`InvalidSourceCharacterError`](#character-set-and-encoding) |
| **`E0106`** | [`UnterminatedCommentError`](#comments) |
| **`E0107`** | [`UnterminatedStringLiteralError`](#text-and-byte-literals) |
| **`E0108`** | [`InvalidEscapeSequenceError`](#text-and-byte-literals) |
| **`E0109`** | [`InvalidUnicodeScalarError`](#text-and-byte-literals) |
| **`E0110`** | [`InvalidByteLiteralError`](#text-and-byte-literals) |
| **`E0111`** | [`MalformedNumericLiteralError`](#numeric-literals) |
| **`E0112`** | [`MalformedInterpolationError`](#text-and-byte-literals) |
| **`E0113`** | [`ReservedIdentifierError`](#keywords) |
| **`E0120`** | [`UnexpectedTokenError`](#syntactic-diagnostic-conditions) |
| **`E0121`** | [`UnexpectedEndOfSourceError`](#syntactic-diagnostic-conditions) |
| **`E0122`** | [`UnclosedDelimiterError`](#syntactic-diagnostic-conditions) |
| **`E0123`** | [`MismatchedDelimiterError`](#syntactic-diagnostic-conditions) |
| **`E0124`** | [`MissingTokenError`](#syntactic-diagnostic-conditions) |

### Names, Initialization, and Field Identity

| Code | Diagnostic and defining rule |
| :---: | :--- |
| **`E0201`** | [`PrivateItemAccessError`](#module-imports-and-visibility) |
| **`E0202`** | [`TopLevelSideEffectError`](#top-level-initialization-and-purity) |
| **`E0203`** | [`DuplicateDeclarationError`](#identifiers-and-casing-invariants) |
| **`E0204`** | [`UnresolvedIdentifierError`](#identifiers-and-casing-invariants) |
| **`E0205`** | [`QuestionMarkOutsideFunctionError`](#error-and-fallback-operators) |
| **`E0206`** | [`AmbiguousConstructorError`](#identifiers-and-casing-invariants) |
| **`E0207`** | [`UseBeforeInitializationError`](#block-expressions-tail-values-and-hoisted-declarations) |
| **`E0208`** | [`ModuleNotFoundError`](#module-imports-and-visibility) |
| **`E0209`** | [`UnresolvedModuleMemberError`](#module-imports-and-visibility) |
| **`E0210`** | [`DuplicateFieldError`](#record-construction-and-spread-update); [Record Types and Row Polymorphism](#record-types-and-row-polymorphism) |
| **`E0211`** | [`ConflictingSpreadFieldsError`](#record-construction-and-spread-update) |
| **`E0212`** | [`OverlappingRowFieldError`](#record-types-and-row-polymorphism) |

### Types, Expressions, Generics, and Patterns

| Code | Diagnostic and defining rule |
| :---: | :--- |
| **`E0301`** | [`TypeMismatchError`](#diagnostic-classification), including [pipeline type constraints](#generic-parameters-defaults-and-value-sorts) and [unproved generic typing](#generic-evidence-and-definition-checking) |
| **`E0302`** | [`UnexpectedFieldError`](#record-types-and-row-polymorphism) |
| **`E0303`** | [`NonExhaustiveMatchError`](#pattern-matching) |
| **`E0304`** | [`UnreachableMatchArmError`](#pattern-matching); [Sum Types and GADTs](#sum-types-and-gadts) |
| **`E0305`** | [`NominalTypeMismatchError`](#nominal-type-wrappers) |
| **`E0306`** | [`KindMismatchError`](#structural-type-pattern-matching); [Generic Parameters](#generic-parameters-defaults-and-value-sorts); [Static Parameter Sorts](#static-parameter-sorts-and-adaptation-rules); [Record Rows](#record-types-and-row-polymorphism); [Static Layout](#compile-time-evaluation-and-layout-queries) |
| **`E0307`** | [`MissingFieldError`](#record-types-and-row-polymorphism) |
| **`E0308`** | [`OpaqueBoundaryViolationError`](#type-declarations-and-opaque-types) |
| **`E0309`** | [`VacuousBindingError`](#guarded-bindings-and-non-vacuous-invariant) |
| **`E0310`** | [`InvalidatedNarrowingAccessError`](#flow-sensitive-type-narrowing) |
| **`E0311`** | [`ContradictoryNarrowingError`](#flow-sensitive-type-narrowing) |
| **`E0312`** | [`TupleIndexOutOfBoundsError`](#array-map-and-tuple-types) |
| **`E0313`** | [`CyclicTypeAliasError`](#definitional-equality-and-recursive-types); [type declarations](#type-declarations-and-opaque-types) |
| **`E0314`** | [`ArityMismatchError`](#pattern-matching); [Default Parameters and Named Arguments](#default-parameters-and-named-arguments) |
| **`E0315`** | [`EscapingLocalNominalTypeError`](#block-expressions-tail-values-and-hoisted-declarations) |
| **`E0316`** | [`NonTrailingDefaultGenericParamError`](#generic-parameters-defaults-and-value-sorts) |
| **`E0317`** | [`FunctionDefaultGenericProhibitedError`](#generic-parameters-defaults-and-value-sorts) |
| **`E0318`** | [`LiteralTypeProhibitedError`](#generic-parameters-defaults-and-value-sorts); [Static Type Values](#static-type-values-and-type-quotation) |
| **`E0319`** | [`BareTypeInExpressionContextError`](#static-type-values-and-type-quotation) |
| **`E0320`** | [`ForwardTypeDefaultReferenceError`](#generic-parameters-defaults-and-value-sorts) |
| **`E0321`** | [`NormallyCompletingElseError`](#guarded-bindings-and-non-vacuous-invariant) |
| **`E0322`** | [`WildcardExpressionError`](#identifiers-and-casing-invariants) |
| **`E0323`** | [`ConstGenericSortMismatchError`](#generic-parameters-defaults-and-value-sorts); [Static Parameter Sorts](#static-parameter-sorts-and-adaptation-rules) |
| **`E0324`** | [`DynamicRecordIndexProhibitedError`](#record-types-and-row-polymorphism) |
| **`E0325`** | [`DuplicateArgumentError`](#default-parameters-and-named-arguments) |
| **`E0326`** | [`LiteralOutOfRangeError`](#numeric-literals) |
| **`E0327`** | [`UnsupportedOperandTypeError`](#bitwise-and-shift-operators) |
| **`E0328`** | [`InvalidCollectionKeyTypeError`](#relational-and-equality-operators) |
| **`E0329`** | [`IncompatibleFormatSpecifierError`](#text-and-byte-literals) |
| **`E0330`** | [`BareEffectTypeAliasError`](#type-definition-boundaries) |
| **`E0331`** | [`BareStateAnnotationTypeAliasError`](#type-definition-boundaries) |
| **`E0332`** | [`VariantComputationAnnotationError`](#type-definition-boundaries) |
| **`E0333`** | [`FieldComputationAnnotationError`](#type-definition-boundaries) |
| **`E0334`** | [`GenericComputationConstraintError`](#type-definition-boundaries) |
| **`E0335`** | [`TypeFunctionComputationAnnotationError`](#type-definition-boundaries) |
| **`E0336`** | [`UnknownFieldError`](#record-types-and-row-polymorphism) |
| **`E0337`** | [`NonProductProjectionError`](#record-types-and-row-polymorphism); [Anonymous Functions, Trailing Closures, and Projection Accessors](#anonymous-functions-trailing-closures-and-projection-accessors) |
| **`E0338`** | [`NonCallableInvocationError`](#default-parameters-and-named-arguments) |
| **`E0339`** | [`UnknownNamedArgumentError`](#default-parameters-and-named-arguments) |
| **`E0340`** | [`GenericArityMismatchError`](#generic-parameters-defaults-and-value-sorts) |
| **`E0341`** | [`InvalidRecordKeySortError`](#mapped-record-and-tuple-types) |
| **`E0342`** | [`InvalidTupleKeySortError`](#mapped-record-and-tuple-types) |
| **`E0343`** | [`SingleElementTupleProhibitedError`](#mapped-record-and-tuple-types) |
| **`E0344`** | [`InsufficientTypeInformationError`](#generic-parameters-defaults-and-value-sorts); [Array, Map, and Tuple Types](#array-map-and-tuple-types) |
| **`E0345`** | [`RefutablePatternError`](#pattern-matching) |
| **`E0346`** | [`OrPatternBindingMismatchError`](#pattern-matching) |
| **`E0347`** | [`DuplicatePatternBindingError`](#pattern-matching) |
| **`E0348`** | [`InvalidRangePatternError`](#pattern-matching) |
| **`E0349`** | [`InvalidPatternExpressionError`](#pattern-matching) |
| **`E0350`** | [`NonBooleanConditionError`](#conditional-expressions); [Logical Operators](#logical-operators) |
| **`E0351`** | [`IncompatibleBranchTypesError`](#structural-joins-and-normal-continuations); [conditionals](#conditional-expressions); [pattern matching](#pattern-matching) |
| **`E0352`** | [`InvalidIndexTargetError`](#array-map-and-tuple-types) |
| **`E0353`** | [`NullaryVariantCallError`](#constructor-tuple-equivalence-invariant) |
| **`E0354`** | [`InvalidVariantContractError`](#sum-types-and-gadts) |
| **`E0355`** | [`NonIterableValueError`](#loop-expressions) |
| **`E0356`** | [`InvalidModeSortError`](#generic-parameters-defaults-and-value-sorts); [Mapped Record and Tuple Types](#mapped-record-and-tuple-types) |
| **`E0357`** | [`IncompatibleMemberModeError`](#mapped-record-and-tuple-types); [Record Types and Row Polymorphism](#record-types-and-row-polymorphism) |
| **`E0358`** | [`InvalidModeProjectionTargetError`](#coordinate-and-variant-introspection-coords-variants); [Member Mode Introspection and Retention](#member-mode-introspection-and-retention) |
| **`E0359`** | [`InvalidFieldDefaultPlacementError`](#record-construction-and-spread-update) |
| **`E0360`** | [`UnfinishedExpressionHoleError`](#expression-holes) |
| **`E0361`** | [`DivisionByZeroError`](#arithmetic-operators) |

### Parameters, Argument Modes, and Defaults

| Code | Diagnostic and defining rule |
| :---: | :--- |
| **`E0401`** | [`ValueTypeReferenceParameterError`](#parameter-modes-caller-obligations-and-defaults) |
| **`E0402`** | [`ValueTypeReferenceModeError`](#value-types) |
| **`E0403`** | [`VarParameterProhibitedError`](#parameter-modes-caller-obligations-and-defaults); [Effect Handlers](#effect-handlers) |
| **`E0404`** | [`MutableParameterDefaultProhibitedError`](#default-parameters-and-named-arguments); [Record Construction and Spread Update](#record-construction-and-spread-update) |
| **`E0405`** | [`MissingArgumentModeMarkerError`](#parameter-modes-caller-obligations-and-defaults) |
| **`E0406`** | [`InvalidArgumentModeError`](#parameter-modes-caller-obligations-and-defaults); [Effect Handlers](#effect-handlers) |
| **`E0407`** | [`CallableParameterModeMismatchError`](#parameter-modes-caller-obligations-and-defaults) |
| **`E0408`** | [`InvalidDefaultParameterReferenceError`](#default-parameters-and-named-arguments); [Record Construction and Spread Update](#record-construction-and-spread-update) |
| **`E0409`** | [`ImpureParameterDefaultError`](#default-parameters-and-named-arguments); [Signature Value Contracts](#signature-value-contracts); [Record Construction and Spread Update](#record-construction-and-spread-update) |
| **`E0410`** | [`InvalidMutableArgumentTargetError`](#parameter-modes-caller-obligations-and-defaults) |
| **`E0411`** | [`InvalidConstructionParameterError`](#fresh-construction-parameters) |
| **`E0412`** | [`InvalidModeInferencePlacementError`](#access-mode-inference-with-via-and-infer) |

### Bindings, State, Access Modes, and Resource Contracts

| Code | Diagnostic and defining rule |
| :---: | :--- |
| **`E0501`** | [`ImmutableReassignmentError`](#immutable-bindings) |
| **`E0502`** | [`PinnedHandleReassignmentError`](#pinned-mutable-handles) |
| **`E0503`** | [`InvalidAssignmentTargetError`](#assignments-and-compound-assignments) |
| **`E0510`** | [`MissingStateAnnotationError`](#callable-contracts); [Retained Mutable Sharing](#retained-mutable-sharing) |
| **`E0520`** | [`MutabilityLaunderingError`](#monotonic-mode-degradation-and-anti-laundering-matrix) |
| **`E0521`** | [`DestructureMutabilityLaunderingError`](#monotonic-mode-degradation-and-anti-laundering-matrix) |
| **`E0522`** | [`ContainerMutabilityLaunderingError`](#monotonic-mode-degradation-and-anti-laundering-matrix) |
| **`E0523`** | [`MutMutAliasingConflictError`](#law-of-exclusivity-and-cross-argument-disjointness) |
| **`E0524`** | [`ReadMutAliasingHazardError`](#law-of-exclusivity-and-cross-argument-disjointness) |
| **`E0525`** | [`SpreadLaunderingError`](#monotonic-mode-degradation-and-anti-laundering-matrix) |
| **`E0526`** | [`CollectionMutationDuringIterationError`](#monotonic-mode-degradation-and-anti-laundering-matrix) |
| **`E0527`** | [`UnusedAuthorityError`](#reachable-authority-use); absent required use or redundant executable sharing marker |
| **`E0528`** | [`ReturnMutabilityLaunderingError`](#monotonic-mode-degradation-and-anti-laundering-matrix) |
| **`E0529`** | [`ExcessiveStateAnnotationError`](#retained-mutable-sharing); [Named Function State Contract References](#named-function-state-contract-references) |
| **`E0530`** | [`IllegalNonClonableAuthorityError`](#deep-immutability) |
| **`E0531`** | [`InvalidRefOriginError`](#read-only-reference-bindings) |
| **`E0532`** | [`ReassignableScopedResourceError`](#scoped-resource-bindings) |
| **`E0533`** | [`AliasedNarrowingHazardError`](#flow-sensitive-type-narrowing) |
| **`E0534`** | [`CallableContractMismatchError`](#callable-contracts); [Closures, Factory Signatures, and Lexical Environments](#closures-factory-signatures-and-lexical-environments) |
| **`E0535`** | [`NonImmutableBindingError`](#immutable-bindings) |
| **`E0536`** | [`InvalidDeriveInputError`](#functional-updates-via-derive) |
| **`E0537`** | [`LiveArrayInvalidationError`](#range-and-sequence-indexing-expressions) |
| **`E0538`** | [`InvalidStateSourceGroupError`](#state-groups-and-captured-layers) |
| **`E0539`** | [`InvalidStateContractReferenceError`](#named-function-state-contract-references) |
| **`E0540`** | [`EndedOperationAuthorityAccessError`](#effect-handlers) |
| **`E0541`** | [`InvalidScopedCleanupContractError`](#scoped-resource-bindings) |
| **`E0543`** | [`NewTargetRefError`](#read-only-reference-bindings) |
| **`E0544`** | [`MissingInferredFunctionAnnotationError`](#mandatory-contract-inference-and-completion); [Signature Value Contracts](#signature-value-contracts) |
| **`E0545`** | [`InvalidReturnSourceContractError`](#return-construction-access-modes-and-sources) |
| **`E0546`** | [`InvalidNewReturnContractError`](#return-construction-access-modes-and-sources) |
| **`E0547`** | [`InvalidOpenRowPlacementError`](#closed-and-open-callable-rows) |
| **`E0548`** | [`InvalidConstructionInputError`](#fresh-construction-parameters) |
| **`E0549`** | [`EndedConstructionAuthorityAccessError`](#fresh-construction-parameters) |
| **`E0550`** | [`RedundantModeViaError`](#inference-domains-and-contract-completion) |
| **`E0551`** | [`InvalidPatternDecompositionError`](#pattern-reception-and-decomposition) |
| **`E0552`** | [`IncompatibleInferredInterfaceError`](#inferred-interfaces-and-callable-families) |

### Effects, Resumption, Concurrency, and Escape

| Code | Diagnostic and defining rule |
| :---: | :--- |
| **`E0601`** | [`CrossTaskAuthorityError`](#structured-concurrency-and-panic-containment) |
| **`E0602`** | [`IllegalChannelPayloadAuthorityError`](#structured-concurrency-channels) |
| **`E0603`** | [`ChannelEndpointAliasingConflictError`](#structured-concurrency-channels) |
| **`E0604`** | [`ScopedResourceEscapeError`](#scoped-resource-bindings) |
| **`E0605`** | [`InvalidParallelDependencyError`](#deterministic-data-parallelism-and-divide-and-conquer-primitives) |
| **`E0606`** | [`ScopedTaskEscapeError`](#structured-concurrency-and-panic-containment); [Task Handles](#task-handles-movable-guard-and-combinators); [Structured Concurrency Channels](#structured-concurrency-channels) |
| **`E0607`** | [`DeriveDraftEscapeError`](#functional-updates-via-derive) |
| **`E0608`** | [`UnwindUnsafePanicBoundaryError`](#panic-absorption-with-absorb_panic) |
| **`E0609`** | [`DuplicateTaskConsumptionError`](#task-handles-movable-guard-and-combinators) |
| **`E0610`** | [`DuplicateResumeInvocationError`](#affine-resumption-and-delimited-early-abort) |
| **`E0611`** | [`EscapingResumeError`](#affine-resumption-and-delimited-early-abort) |
| **`E0612`** | [`UnhandledEffectError`](#callable-contracts); [Built-in System Effects](#built-in-system-effects); [Structured Concurrency](#structured-concurrency-and-panic-containment) |
| **`E0613`** | [`ValueEffectAnnotationError`](#type-definition-boundaries) |
| **`E0614`** | [`UnstableHandlerCaptureError`](#effect-handlers) |
| **`E0615`** | [`CrossTaskUnhandledEffectError`](#structured-concurrency-and-panic-containment); [Effect Handlers](#effect-handlers) |
| **`E0616`** | [`ScopedCleanupEffectError`](#scoped-resource-bindings) |
| **`E0617`** | [`ScopedCleanupFinitenessError`](#scoped-resource-bindings) |
| **`E0618`** | [`UndischargedLocalEffectError`](#block-expressions-tail-values-and-hoisted-declarations) |
| **`E0619`** | [`ParallelDisjointAccessConflictError`](#deterministic-data-parallelism-and-divide-and-conquer-primitives) |
| **`E0620`** | [`PseudoEffectAnnotationError`](#built-in-system-effects); [Deterministic Data Parallelism and Divide-and-Conquer Primitives](#deterministic-data-parallelism-and-divide-and-conquer-primitives) |
| **`E0621`** | [`InvalidHandlerTargetError`](#effect-handlers); [Built-in System Effects](#built-in-system-effects) |
| **`E0622`** | [`DuplicateHandlerOperationError`](#effect-handlers) |
| **`E0623`** | [`ResumeOutsideHandlerError`](#affine-resumption-and-delimited-early-abort) |
| **`E0624`** | [`ResumeValueTypeMismatchError`](#effect-handlers) |
| **`E0625`** | [`HandlerAnswerTypeMismatchError`](#effect-handlers) |

### Declaration Contexts, Control Flow, and Fallible Values

| Code | Diagnostic and defining rule |
| :---: | :--- |
| **`E0701`** | [`ChainedAssignmentProhibitedError`](#assignments-and-compound-assignments) |
| **`E0702`** | [`InvalidWhereItemError`](#block-expressions-tail-values-and-hoisted-declarations); [Dual-Tier Where Invariants](#dual-tier-where-invariants) |
| **`E0703`** | [`IllegalSequentialDeclarationError`](#block-expressions-tail-values-and-hoisted-declarations) |
| **`E0704`** | [`InvalidSignatureWhereItemError`](#dual-tier-where-invariants) |
| **`E0705`** | [`DownwardScopeReferenceError`](#dual-tier-where-invariants) |
| **`E0706`** | [`SignatureTypeNotInSignatureWhereError`](#dual-tier-where-invariants) |
| **`E0707`** | [`InvalidControlTransferContextError`](#control-transfers) |
| **`E0708`** | [`InvalidMetadataPlacementError`](#comments); [Declaration Metadata Attributes](#declaration-metadata-attributes) |
| **`E0710`** | [`IllegalControlTransferInFallbackError`](#error-and-fallback-operators) |
| **`E0711`** | [`InvalidResultFallbackError`](#error-and-fallback-operators) |
| **`E0712`** | [`InvalidPropagationOperandError`](#error-and-fallback-operators); [Signature Value Contracts](#signature-value-contracts) |
| **`E0713`** | [`IncompatiblePropagationTargetError`](#error-and-fallback-operators); [Signature Value Contracts](#signature-value-contracts) |
| **`E0714`** | [`InvalidFallbackOperandError`](#error-and-fallback-operators) |
| **`E0715`** | [`InvalidSafeAccessReceiverError`](#error-and-fallback-operators) |
| **`E0720`** | [`UnusedFallibleResultError`](#mandatory-inspection-of-fallible-results); [Task Handles](#task-handles-movable-guard-and-combinators); [Structured Concurrency Channels](#structured-concurrency-channels) |

### Static Computation and Finiteness

| Code | Diagnostic and defining rule |
| :---: | :--- |
| **`E0810`** | [`CallFamilyViolationError`](#disjoint-call-families-evaluation-budgets-and-branch-pruning) |
| **`E0811`** | [`CompileTimeBudgetExceededError`](#pure-type-functions-and-result-restrictions) |
| **`E0812`** | [`MetaTypeReturnProhibitedError`](#pure-type-functions-and-result-restrictions) |
| **`E0813`** | [`MetaComputationAnnotationError`](#pure-type-functions-and-result-restrictions) |
| **`E0814`** | [`StaticValueRequiredError`](#disjoint-call-families-evaluation-budgets-and-branch-pruning) |
| **`E0815`** | [`InvalidStaticValueError`](#disjoint-call-families-evaluation-budgets-and-branch-pruning) |
| **`E0816`** | [`RuntimeTypeTokenProhibitedError`](#pure-type-functions-and-result-restrictions) |
| **`E0820`** | [`HaltFinitenessViolationError`](#termination-and-halt-contracts); [Deterministic Data Parallelism and Divide-and-Conquer Primitives](#deterministic-data-parallelism-and-divide-and-conquer-primitives) |
| **`E0821`** | [`HaltPurityViolationError`](#termination-and-halt-contracts) |
| **`E0822`** | [`InvalidBudgetBoundaryError`](#finite-evaluation-with-diverge) |
| **`E0830`** | [`MetaAssertionFailedError`](#pure-type-functions-and-result-restrictions) |
| **`E0831`** | [`StaticEvaluationPanicError`](#pure-type-functions-and-result-restrictions) |

### Module Forms, Entry Points, and External Contracts

| Code | Diagnostic and defining rule |
| :---: | :--- |
| **`E0901`** | [`BodyInDeclModuleError`](#external-interface-declarations) |
| **`E0902`** | [`MissingBodyInStandardModuleError`](#external-interface-declarations); [Built-in Declarations](#named-function-declarations-and-contrast-matrix) |
| **`E0903`** | [`MissingEntryPointError`](#program-entry-point) |
| **`E0904`** | [`InvalidEntryPointError`](#program-entry-point) |
| **`E0905`** | [`RootUnitExportProhibitedError`](#modules-and-compilation-units) |
| **`E0906`** | [`PublicMutableStateProhibitedError`](#modules-and-compilation-units); [Top-Level Initialization and Purity](#top-level-initialization-and-purity) |
| **`E0907`** | [`ForeignStructuralFieldPenetrationError`](#external-interface-declarations) |
| **`E0908`** | [`UnsupportedExternalAuthorityContractError`](#external-interface-declarations) |
| **`E0909`** | [`BuiltinSignatureMismatchError`](#named-function-declarations-and-contrast-matrix) |
