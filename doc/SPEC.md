# The Ril Language Specification

**Version:** 0.1.0  
**Status:** Canonical Reference Specification  
**Format:** Code-First Normative Document  

---


## Document Conventions

This document defines Ril grammar, typing, permissions, effects, abstract-machine behavior, and diagnostics.

- **Normative Invariants**: Language guarantees and type safety rules are formally declared under titled normative invariants. All conforming Ril implementations must enforce these invariants unconditionally.
- **Grammar Productions**: Syntactic grammar is formally specified in Extended Backus-Naur Form (EBNF).
- **Normative Code Annotations**: Code examples define normative verification cases in the stated fixture context:
  - `-- OK`: Syntactically and semantically valid Ril programs.
  - `-- Error [EXXXX]`: Programs that must be statically rejected by the compiler with the indicated diagnostic error code.
  - `-- Panics`: Programs that raise deterministic runtime panics under defect conditions.
- **Diagnostic Text**: Error codes and their triggering conditions are normative. Example message text, source highlighting, notes, and suggested repairs are illustrative.
- **Examples**: Blocks are independent fixtures unless marked as complete source files.
- Local statements run in an enclosing callable; displayed declarations belong to its enclosing declaration scope. Free names are typed fixture inputs or supplied contracts.
- Fixtures handle their local expressions' effects. Except for examples testing missing named-function annotations, abbreviated named callable declarations in independent fixtures denote their compiler-completed signatures under [mandatory contract completion](#mandatory-contract-inference-and-completion). `-- OK` checks that completed form; complete source files must spell the annotations required for named definitions. Anonymous functions retain their full compiler-inferred contracts without mandatory source completion in either kind of fixture. Inference and completion never repair a permission violation or change evaluation, allocation, or sharing.
- Negative statements are checked individually with valid setup. Blocks containing `...` are schematic.
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
    - [Reference Types](#reference-types)
    - [Record Types and Row Polymorphism](#record-types-and-row-polymorphism)
    - [Array, Map, and Tuple Types](#array-map-and-tuple-types)
    - [Sum Types and GADTs](#sum-types-and-gadts)
      - [Constructor-Tuple Equivalence Invariant](#constructor-tuple-equivalence-invariant)
    - [Nominal Type Wrappers](#nominal-type-wrappers)
    - [Deep Immutability](#deep-immutability)
    - [Type Identity and Subtyping](#type-identity-and-subtyping)
    - [Complete Provenance and Required Annotations](#complete-provenance-and-required-annotations)
    - [Functional Updates via Derive](#functional-updates-via-derive)
      - [Normative Rules for Functional Updates](#normative-rules-for-functional-updates)
    - [Generic Parameters, Defaults, and Value Sorts](#generic-parameters-defaults-and-value-sorts)
    - [Type Definition Boundaries](#type-definition-boundaries)
  - [Declarations and Bindings](#declarations-and-bindings)
    - [Binding Permissions and Storage Matrix](#binding-permissions-and-storage-matrix)
    - [Shared Writable Reception](#shared-writable-reception)
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
    - [External Interface Declarations](#external-interface-declarations)
      - [Normative Rules for External Interface Modules](#normative-rules-for-external-interface-modules)
  - [Expressions and Operators](#expressions-and-operators)
    - [Expression Grammar](#expression-grammar)
    - [Operator Precedence and Associativity](#operator-precedence-and-associativity)
    - [Arithmetic and Wrapping Operators](#arithmetic-and-wrapping-operators)
    - [Bitwise and Shift Operators](#bitwise-and-shift-operators)
    - [Relational, Equality, and Containment Operators](#relational-equality-and-containment-operators)
      - [Value Tests with is](#value-tests-with-is)
    - [Logical Operators](#logical-operators)
    - [Range and Sequence Indexing Expressions](#range-and-sequence-indexing-expressions)
    - [Pipeline Operators](#pipeline-operators)
    - [Error and Fallback Operators](#error-and-fallback-operators)
    - [Record Construction and Functional Update](#record-construction-and-functional-update)
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
    - [Flow-Sensitive Type Narrowing](#flow-sensitive-type-narrowing)
      - [Flow-Sensitive Type Narrowing Rules and Invariants](#flow-sensitive-type-narrowing-rules-and-invariants)
  - [Functions, Closures, and Callables](#functions-closures-and-callables)
    - [Named Function Declarations and Contrast Matrix](#named-function-declarations-and-contrast-matrix)
      - [Dual-Tier Where Invariants](#dual-tier-where-invariants)
    - [Callable Contracts](#callable-contracts)
      - [Mandatory Contract Inference and Completion](#mandatory-contract-inference-and-completion)
      - [Closed and Open Callable Rows](#closed-and-open-callable-rows)
      - [Callable Contract Matching](#callable-contract-matching)
      - [Higher-Order Calls](#higher-order-calls)
    - [Return Construction, Permissions, and Sources](#return-construction-permissions-and-sources)
    - [Termination and halt Contracts](#termination-and-halt-contracts)
    - [Parameter Modes, Caller Obligations, and Defaults](#parameter-modes-caller-obligations-and-defaults)
      - [Fresh Construction Parameters](#fresh-construction-parameters)
      - [Fresh Values in Storage Calls](#fresh-values-in-storage-calls)
      - [Default Parameters and Named Arguments](#default-parameters-and-named-arguments)
    - [Anonymous Functions, Trailing Closures, and Projection Accessors](#anonymous-functions-trailing-closures-and-projection-accessors)
    - [Closures, Factory Signatures, and Lexical Environments](#closures-factory-signatures-and-lexical-environments)
  - [State and Capability Tracking](#state-and-capability-tracking)
    - [Local Mutation Purity and Local Capability Discharge](#local-mutation-purity-and-local-capability-discharge)
    - [Parameter Mutation](#parameter-mutation)
    - [Retained Mutable Sharing](#retained-mutable-sharing)
    - [External State Tracking](#external-state-tracking)
    - [State Groups and Captured Layers](#state-groups-and-captured-layers)
    - [Named Function State Contract References](#named-function-state-contract-references)
    - [Closure Capabilities and Handle Permissions](#closure-capabilities-and-handle-permissions)
    - [Law of Exclusivity and Cross-Argument Disjointness](#law-of-exclusivity-and-cross-argument-disjointness)
    - [Monotonic Permission Degradation and Anti-Laundering Matrix](#monotonic-permission-degradation-and-anti-laundering-matrix)
  - [Algebraic Effects and Concurrency](#algebraic-effects-and-concurrency)
    - [Effect Declarations and Operation Signatures](#effect-declarations-and-operation-signatures)
    - [Effect Handlers](#effect-handlers)
    - [Parameterized Handler Applications](#parameterized-handler-applications)
    - [Affine Resumption and Delimited Early Abort](#affine-resumption-and-delimited-early-abort)
    - [Built-in System Effects](#built-in-system-effects)
      - [Normative Rules for Built-in System Effects](#normative-rules-for-built-in-system-effects)
    - [Finite Evaluation with Div](#finite-evaluation-with-div)
      - [Coverage and Finite Outcomes](#coverage-and-finite-outcomes)
      - [Allowance and Charging](#allowance-and-charging)
    - [Structured Concurrency and Panic Containment](#structured-concurrency-and-panic-containment)
    - [Deterministic Data Parallelism and Divide-and-Conquer Primitives](#deterministic-data-parallelism-and-divide-and-conquer-primitives)
    - [Structured Concurrency Channels](#structured-concurrency-channels)
  - [Compile-Time Computation and Totality](#compile-time-computation-and-totality)
    - [Static Type Values and Type Quotation](#static-type-values-and-type-quotation)
    - [Pure Type Functions and Type Return Privilege](#pure-type-functions-and-type-return-privilege)
    - [Disjoint Call Families, Evaluation Budgets, and Branch Pruning](#disjoint-call-families-evaluation-budgets-and-branch-pruning)
    - [Unified Tripartite Introspection](#unified-tripartite-introspection)
      - [Universal Coordinate Indexing](#universal-coordinate-indexing)
      - [Static Key Parameters and Computed Value Projection](#static-key-parameters-and-computed-value-projection)
      - [Universal Constituent Projection](#universal-constituent-projection)
      - [Symmetrical Mapped Comprehensions](#symmetrical-mapped-comprehensions)
    - [Structural Type Pattern Matching](#structural-type-pattern-matching)
    - [Static Parameter Sorts and Adaptation Rules](#static-parameter-sorts-and-adaptation-rules)
    - [Compile-Time Execution and Layout Cooperation](#compile-time-execution-and-layout-cooperation)
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
    - [Bindings, State, Permissions, and Resource Contracts](#bindings-state-permissions-and-resource-contracts)
    - [Effects, Resumption, Concurrency, and Escape](#effects-resumption-concurrency-and-escape)
    - [Declaration Contexts, Control Flow, and Fallible Values](#declaration-contexts-control-flow-and-fallible-values)
    - [Static Computation and Totality](#static-computation-and-totality)
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
let z = 10 / 0                         -- Panics: division by zero
```

### Program Conformance

A conforming Ril implementation MUST:
- Accept all syntactically and semantically valid Ril programs defined herein.
- Statically reject all invalid programs with the exact diagnostic conditions specified herein.
- Emit artifacts adhering strictly to the abstract machine semantics, memory model, and determinism invariants.
- Infer complete provenance and callable contracts for every function, require the prescribed source annotations on named definitions, and expose diagnostic explanations and complete inferred contracts, including those of anonymous functions without source annotations. Static validity is determined by the specified conservative judgments, not by an assumption that arbitrary run-time behavior can be decided exactly.

### Diagnostic Classification

```ril
let value: str = 1                    -- Error [E0301]: incompatible expression type
let unused_value = 1                  -- OK: valid unused read-only binding
let quotient = 1 / 0                  -- Panics: integer division by zero
meta let QUOTIENT = 1 / 0             -- Error [E0831]: panic during static evaluation
```

An `E` diagnostic rejects a program under a specified syntactic or semantic rule. A panic is an execution outcome, not a static diagnostic or an algebraic effect. Recoverable `Result` and `Option` values are ordinary data, not diagnostic categories.

An expression incompatible with its required type is `E0301` when no more specific condition applies. For an isolated violation, the diagnostic assigned by its defining rule is required. A specific applicable condition takes precedence over a general condition such as `E0301`; for example, an absent record member is `E0336`, not an arbitrary type mismatch. Dedicated placement restrictions, such as declarations in the sequential statement stream, retain their specific codes instead of a general syntax diagnostic. Independent violations may produce multiple diagnostics; their reporting order and the number of secondary diagnostics are unspecified. These rules do not prescribe error recovery or permit an invalid program to be accepted.

Diagnostic explanations should identify the violated requirement and the relevant source construct. When applicable, they should distinguish expected and actual types, identify the declaration or authority responsible for a restriction, or identify an uncovered case. Suggested changes are advisory and must not claim to preserve intent when they change effects, sharing, ownership of resources, or error handling. Exact wording and presentation are not conformance requirements.

### Abstract Machine and Memory Semantics

Ril executes on an abstract machine with automatic memory management (tracing garbage collection). Evaluation order is strictly left-to-right. Numeric operations on fixed-width types are strictly deterministic across all target architectures.

```ril
-- Strict left-to-right evaluation order across operands and arguments:
let mut trace: []int = []
let mut log = \n -> { trace !> Array::push(n); n }
let result = log(1) + log(2) * log(3)  -- Evaluates log(1), then log(2), then log(3)
-- trace is guaranteed to be [1, 2, 3]
```

### Failure Model and Error Categories

```ril
-- Recoverable error handling via Result and '?':
fn parse_id(s: str) -> Result<int, str> {
    if s == "" { Err("empty input") } else { Ok(42) }
}

fn init_session() -> Result<int, str> {
    let id = parse_id("10")?           -- OK: propagated via postfix '?' within function frame
    Ok(id)
}
assert(init_session() is Ok(42))
assert(parse_id("") is Err("empty input"))
-- let top_id = parse_id("10")?        -- Error [E0205]: postfix '?' operator used outside function or closure body; no enclosing activation frame to receive early return
-- parse_id("10")                       -- Error [E0720]: unused fallible Result must be handled via '?', 'match', or fallback '??'

-- Deterministic runtime panic on defect:
let arr = [1, 2, 3]
let safe_item = arr?[5]                -- OK: safe index evaluates to Option<int> (None)
assert(safe_item == None)
-- arr[5]                             -- Panics: index 5 is outside length 3
```

```ril
fn faulty_frame() -> int {
    let _ = 10 / 0                    -- Panics: synchronous evaluation stops here
    100                               -- Unreachable
}
faulty_frame()                        -- Panics; no Result is produced
```

```ril
use ril/concurrent::{scope, TaskFault}
let scope_outcome: Result<int, TaskFault> = scope(\mut s -> {
    s.fork(\-> panic("worker failure"))
    Ok(42)
})
assert(scope_outcome is Err(TaskFault::Panicked(_))) -- Child failure defeats Ok(42)
```

```ril
use ril/concurrent::{scope, TaskFault}
fn parent_fault() @Concurrent -> Result<int, TaskFault> {
    scope \mut s -> {
        let child = s.fork(\-> 42)
        let value = child.join()?
        assert(value == 42)
        panic("parent failure")
    }
}
parent_fault() ?? \_fault -> 0         -- Panics; the Result fallback cannot catch the parent
```

Each block is an independent fixture. Panic isolation and child faults follow [structured boundaries](#structured-concurrency-and-panic-containment).

- **Recoverable Errors**: Ordinary `Result<T, E>` and `Option<T>` / `?T` values. Unused Results are statically rejected.
- **Defects (Panics)**: Invariant violations raise deterministic run-time panics.
- **Synchronous Isolation**: A synchronous frame cannot catch a panic.
- **Boundary Containment**: A child panic fails its owning scope with `TaskFault::Panicked`; a panic in the scope body propagates outward.

### Run-Time Failure Conditions

```ril
let smallest: i8 = -128i8              -- OK: representable signed literal
-- let too_large = 128i8              -- Error [E0326]: unrepresentable literal
-- let overflow = 127i8 + 1i8         -- Panics: checked arithmetic overflow
let wrapped = 127i8 +% 1i8            -- OK: -128i8
let safe = 1 /? 0                     -- OK: None
let ieee = 1.0 / 0.0                  -- OK: positive infinity
-- meta let OVERFLOW = 127i8 + 1i8    -- Error [E0831]: static evaluation panic
-- meta let CHECK = assert(false)    -- Error [E0830]: static assertion failure
```

| Condition when evaluated | Outcome |
| :--- | :--- |
| `panic(message)` | Begin panic unwinding with the supplied message |
| False `assert` condition | Assertion panic |
| Integer `/` or `%` with zero divisor | Division-by-zero panic |
| Negative `Div::budget` limit | Panic before invoking the protected action |
| Unrepresentable checked fixed-width integer result, including negation and `MIN / -1` | Integer-overflow panic; `MIN % -1` remains zero |
| Fixed-width shift count negative or at least the bit width; negative `bigint` shift count | Invalid-shift panic |
| Ordinary array element index outside its bounds | Index-bounds panic |
| Negative, reversed, or out-of-bounds range index | Range bounds panic under the [range indexing rules](#range-and-sequence-indexing-expressions) |
| External fault whose declared boundary contract maps it to a defect | Panic under that contract; a domain failure remains a `Result` value |

Panic categories describe conditions, not additional types, effect tags, or `PanicInfo` fields. Message spelling is unspecified. `PanicInfo.index` denotes a parallel source index, not a general bounds-error index.

Ordinary execution retains these outcomes even when a defect is statically predictable. Only evaluation required in the static domain turns a failed assertion into `E0830` or another panic into `E0831`. Safe division/remainder and safe lookup preserve their specified `None` outcomes; a missing map key and channel closure retain their ordinary fallible values. Floating-point overflow and division by zero retain their IEEE results.

| Abnormal control or cleanup condition | Consequence |
| :--- | :--- |
| Effect arm completes without resumption | Delimited abort; prior writes remain committed and scoped cleanup runs |
| Structured cancellation | Non-resumable exit under the scope/channel rules; not a fabricated panic or business error |
| Cleanup panics during normal exit | Begin panic unwinding through the remaining resources |
| Cleanup panics during panic, cancellation, or effect abort | Record both causes and abandon remaining cleanup in the failed frame; `DoubleFaultFatal` |

Scoped cleanup is LIFO. A task boundary contains child faults, not a panic from its own parent frame. Parallel evaluation exposes only faults visible in its specified reference order, including double faults; a skipped branch cannot fail a successful result.

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

Ill-formed UTF-8 is `E0104`. A decoded character that cannot occur in any token at its source position is `E0105`. Admissible string, raw-string, and comment contents are determined by their own rules; identifier casing and spelling use `E0101`/`E0102` instead.

### Comments

```ebnf
LineComment  ::= "--" { SourceChar } ( Newline | EOF )
BlockComment ::= "{-" { SourceChar | BlockComment } "-}"
```

```ril
-- Single-line comment to end of line
{- Block comment {- nested block comment -} continues -}
```

```ril
-- Error [E0106]: nested block comment remains open at end of this source fragment
{- outer {- inner -}
```

Every opened block comment requires a matching `-}`; reaching the end of source with an open comment is `E0106`.

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
| Callable declaration/type head through its contract clauses, return contract, signature `where`, and required body | Remain one head across newlines; the first body brace follows the complete head |
| Required declaration body, `else`, `where` | Stay attached to the preceding construct |
| Leading `\|>`, `!>`, `??` | Continue the preceding expression |
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
Identifier         ::= PascalCase | SnakeCase | ScreamingSnakeCase | UnderscoreName
PascalCase         ::= [A-Z] { [a-zA-Z0-9] }
SnakeCase          ::= [a-z] [a-z0-9]* { "_" [a-z0-9]+ }
ScreamingSnakeCase ::= [A-Z] [A-Z0-9]* { "_" [A-Z0-9]+ }
UnderscoreName     ::= "_" [a-z] [a-z0-9]* { "_" [a-z0-9]+ }
Wildcard           ::= "_"
QualifiedName    ::= Identifier { "::" Identifier }
```

Identifier grammatical roles obey the **Closed Casing Invariant**:

- **`PascalCase`**: Strictly reserved for types (`type`), ADT variant constructors, nominal wrappers, algebraic effects (`eff`), generic type parameters (`T`, `ItemType`), and module namespace identifiers (`Array`, `Channel`, `Geometry`).
   - **Acronym Title-Casing Rule**: Acronyms within `PascalCase` MUST be title-cased as regular words (`HttpServer`, `UserId`, `JsonParser`, NOT `HTTPServer`, `UserID`, `JSONParser`) (`E0102`).
- **`snake_case`**: Strictly used for runtime variables (local bindings, function parameters, reassignable variables `var`, and pinned mutable handles `let mut`), const generic parameters (`cap: int`), named functions (`fn`, `meta fn`), record fields, and module path segments (`ril/array`, `math/geometry`).
- **`SCREAMING_SNAKE_CASE`**: Strictly reserved for compile-time constants (`meta let`) and top-level immutable constants (`let`). Top-level mutable variables (`var`, `let mut`, including `let ^mut` / `var ^mut` reception sugar) MUST use `snake_case`.
- **Static Keys and Field Labels**: Static key binders (`K: keyof T`) and mapped-key binders (`[K in ...]`) use PascalCase. Ordinary field labels use snake_case, optionally with one leading underscore. A mapped record may expose valid PascalCase constructor labels; construction and projection against that mapped schema use those generated labels verbatim. This does not permit uppercase run-time variable bindings.
- **Wildcard and Leading Underscores**: A single underscore `_` is strictly the wildcard discard pattern, not an identifier (`E0322`). An identifier with a leading underscore, such as `_snake_case`, follows the same binding and mutable-authority use requirements as other identifiers (`E0527`).

```ril
type First { Shared }
type Second { Shared }
let first: First = First::Shared       -- OK: qualified constructor
-- let ambiguous: First = Shared      -- Error [E0206]: expected type does not resolve the abbreviation
type Maybe<T> = Option<T>
let value: Maybe<int> = Some(1)        -- OK: an alias adds no constructor candidate
```

Declarations and imports share one namespace. Same-scope duplicates are `E0203`; inner declarations may shadow outer ones, including the enclosing prelude. The intrinsic static type family `Type` is protected against user declarations, type binders, and type/namespace import aliases that would redefine or shadow it (`E0203`). It is not a new keyword.

| Name | Resolution |
| :--- | :--- |
| Nominal type/constructor; predefined `Set<T>`/`Set::from` | Roles of one declaration; separate user declarations cannot merge |
| `S::V` | Variant member of S; no second enclosing-scope declaration |
| Unqualified constructor name | Ordinary lexical binding first; otherwise require one variant candidate (`E0206` if ambiguous) |
| Candidate set | Directly visible sum types; a module import alone does not expose its internal sums |
| Aliases and re-exports | Deduplicate candidates by variant declaration identity |
| Expected type / generic arguments | Expected types never choose a declaration; infer/check arguments after selection |

```ril
-- PascalCase: Types, Constructors, Effects, and Generic Parameters
type UserAccount = { id: int }         -- OK: type identifier
type Result<T, E = str> { Ok(T), Err(E) } -- OK: generic parameters and constructors
eff FileIo { read() -> str }           -- OK: effect identifier
type HttpServerConfig = { port: int }  -- OK: title-cased acronym

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
-- type user_doc = { id: int }         -- Error [E0101]: type identifier must be PascalCase, found 'user_doc'
-- fn Calculate() -> () {}             -- Error [E0101]: function identifier must be snake_case, found 'Calculate'
-- let UserCount = 10                  -- Error [E0101]: variable identifier must be snake_case, found 'UserCount'
-- meta let max_size = 100             -- Error [E0101]: compile-time constant must be SCREAMING_SNAKE_CASE, found 'max_size'
-- var ACTIVE_FLAG = true              -- Error [E0101]: top-level mutable variable must be snake_case, found 'ACTIVE_FLAG'
-- type HTTPServer = { port: int }     -- Error [E0102]: acronym in PascalCase must be title-cased, expected 'HttpServer', found 'HTTPServer'
-- let user__name = "Alice"            -- Error [E0102]: consecutive underscores are prohibited, found 'user__name'
-- let Some(USER_ID) = opt             -- Error [E0103]: pattern binding position cannot use uppercase identifier 'USER_ID'
-- let _ = 10; println(_)              -- Error [E0322]: wildcard '_' cannot be evaluated as an expression
```

### Keywords

The following 35 tokens are reserved; they cannot be ordinary identifiers or field labels:

```
as       eff      else     false    fn
for      halt     if       in       is
keyof    last     let      loop     match
meta     module   mut      never    new
next     opaque   pub      ref      resume
return   scoped   true     type     typeof
use      var      where    while    with
```

```ril
-- let while = 1                     -- Error [E0113]: reserved keyword in a binding position
-- let new = 1                       -- Error [E0113]: new is reserved for return contracts
-- type Record = { if: int }         -- Error [E0113]: reserved keyword as a field label
let while_count = 1                   -- OK
let capture = 1                       -- OK: capture is an ordinary identifier
let closure = 1                       -- OK: closure is an ordinary identifier
let up = 1                            -- OK: up is an ordinary identifier
let sub = 1                           -- OK: sub is an ordinary identifier
type Config = { capture: bool }       -- OK: capture is an ordinary field label
```

A reserved keyword used as an ordinary identifier or field label is `E0113`.

`capture`, `up`, and `sub` remain ordinary identifiers. They have contextual roles in capability annotations: `&capture` is a capability annotation, bare `&up` is a callable-type environment abstraction, `&up{...}` is a captured-source group, and `&up(sub){...}` is a module-storage group. In `&up(owner){...}`, an owner other than the literal `sub` identifies an enclosing callable layer. Within these parentheses, the literal `sub` selects module storage before name resolution; it is never interpreted as a capture owner or a state item. See [State Groups and Captured Layers](#state-groups-and-captured-layers).

```ril
-- Reserved keywords in action:
pub opaque type Token = int            -- 'pub', 'opaque', 'type'
meta let COMPILE_ID = 101              -- 'meta', 'let'
eff Logger { log(str) -> () }          -- 'eff'
use ril/array::{push}                  -- 'use'
halt fn total_step() -> bool { true }  -- 'halt', 'true', 'fn'
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
    let in_bounds = bound in 1..=10    -- 'in'
    var sum = 0                        -- 'var'
    for [1, 2, 3] as n {               -- 'for', 'as'
        sum += n
        if sum > 10 { last }           -- 'last'
        else { next }                  -- 'else', 'next'
    }
    while false { loop {} }            -- 'while', 'false', 'loop'
    bound                              -- tail expression
where                                  -- 'where' inside block
    type Dummy = never                 -- 'never'
}
```

### Numeric Literals

```ebnf
IntLiteral     ::= DecimalLiteral | HexLiteral | OctalLiteral | BinaryLiteral
DecimalLiteral ::= Digit { [ "_" ] Digit } [ [ "_" ] IntSuffix ]
HexLiteral     ::= "0" ( "x" | "X" ) HexDigit { [ "_" ] HexDigit } [ [ "_" ] IntSuffix ]
OctalLiteral   ::= "0" ( "o" | "O" ) OctalDigit { [ "_" ] OctalDigit } [ [ "_" ] IntSuffix ]
BinaryLiteral  ::= "0" ( "b" | "B" ) BinaryDigit { [ "_" ] BinaryDigit } [ [ "_" ] IntSuffix ]
IntSuffix      ::= "i8" | "i16" | "i32" | "i64" | "u8" | "u16" | "u32" | "u64" | "int" | "bigint"
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
let explicit_u8 = 255u8                -- Type: u8
let explicit_i16 = -32_i16             -- Type: i16
let float_val = 3.14159_f64            -- Type: f64
let float_f32 = 2.5f32                 -- Type: f32
let scientific = 1.25e-4               -- Type: f64 (exponent)
let big_num = 12345678901234567890bigint -- Type: bigint
let smallest: i8 = -128i8               -- OK: signed literal is checked as a whole
-- let too_large: i8 = 128i8            -- Error [E0326]: literal is outside its selected type's range
-- let mixed = 1u8 + 1u16               -- Error [E0301]: no implicit numeric promotion
```

| Form | Type / check |
| :--- | :--- |
| Suffixed literal | Suffix fixes the type |
| Unsuffixed integer | Compatible numeric context, otherwise `int`; round once if selected as floating-point |
| Unsuffixed float | Contextual `f32`/`f64`, otherwise `f64` |
| Integer-typed literal | Must fit its type (`E0326`); an immediately applied `-` is included in the range check |
| Negating an evaluated fixed-width minimum | Panic; the literal exception does not apply |
| Numeric arithmetic/comparison | Same operand type (`E0301`); no conversion of already typed values |
| Shift count | Integer; need not have the left operand's width |

### Text and Byte Literals

```ebnf
StringLiteral     ::= '"' { StringCharacter | EscapeSequence | Interpolation } '"'
RawStringLiteral  ::= '`' { RawCharacter } '`'
ByteStringLiteral ::= 'b"' { ByteCharacter | ByteEscape } '"'
Interpolation     ::= "{" Expression [ ":" FormatSpec ] "}"
FormatSpec        ::= [ FillAlign ] [ Width ] [ "." Precision ] [ FormatType ]
FillAlign         ::= [ SourceChar ] ( "<" | "^" | ">" )
Width             ::= Digit { Digit }
Precision         ::= Digit { Digit }
FormatType        ::= "x" | "X" | "b" | "o" | "e" | "f" | "s"
```

```ril
-- let escape = "\q"                 -- Error [E0108]: unsupported escape
-- let scalar = "\u{D800}"           -- Error [E0109]: surrogate is not a Unicode scalar
-- let byte_value = b"\xG0"          -- Error [E0110]: byte escape requires two hex digits
-- let non_ascii = b"é"              -- Error [E0110]: non-ASCII byte-literal character
-- let empty = "value: {}"           -- Error [E0112]: interpolation requires an expression
-- let format = "{1:04q}"            -- Error [E0112]: malformed format specifier
-- let open = "value: {1"            -- Error [E0112]: interpolation lacks its closing brace
let braces = "{{value}}"              -- OK: literal braces
let scalar = "\u{1F642}"              -- OK: Unicode scalar
```

```ril
-- Error [E0107]: string delimiter remains open at end of this source fragment
let text = "unfinished
```

An unclosed ordinary, raw, or byte string is `E0107`. Unsupported or malformed ordinary-string escapes are `E0108`; a syntactically well-formed Unicode escape outside the scalar range, including surrogates, is `E0109`. Invalid byte-literal contents or escapes are `E0110`. These conditions are not malformed identifiers. A recognized interpolation's malformed braces, absent expression, or malformed format syntax is `E0112`; a valid format incompatible with the interpolated type is `E0329`.

```ril
let word = "Ada"
-- let text = "{word:x}"             -- Error [E0329]: integer format applied to str
let text = "{42:x}"                   -- OK
```

```ril
let greeting = "Hello, world!\n"       -- Type: str
let name = "Alice"
let pi = 3.1415926
let count = 42

-- String interpolation with format specifiers:
let msg1 = "User: {name:>10}"          -- "User:      Alice" (right-aligned, width 10)
let msg2 = "Pi: {pi:.2f}"              -- "Pi: 3.14" (floating-point precision 2)
let msg3 = "Hex: 0x{count:04x}"        -- "Hex: 0x002a" (zero-padded 4-digit hex)
let raw_path = `C:\new\folder\test`    -- Raw string: backslashes not escaped
let binary_data = b"RIFF\x00\x01\xFF"  -- Type: bytes with byte hex escapes
```


- Strings contain Unicode scalars. Escapes: `\n`, `\r`, `\t`, `\0`, `\\`, `\"`, `\u{hex_digits}`. Malformed escapes are `E0108`; non-scalar Unicode escapes are `E0109`.
- Interpolated strings use `{{` and `}}` for literal braces.
- Raw strings have no escapes/interpolation and cannot contain their closing backtick.
- Byte literals contain ASCII or `\xHH` with exactly two hex digits.

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
| Width / precision bounds | Nonnegative decimal values representable as `int`; otherwise malformed format (`E0112`) |
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
PrimitiveType    ::= "bool" | "i8" | "i16" | "i32" | "i64" | "int"
                  | "u8" | "u16" | "u32" | "u64" | "bigint"
                  | "f32" | "f64" | "str" | "bytes" | "(" ")" | "never"
```

Value types have copy-by-value semantics, regardless of their implementation representation.

| Category | Types | Description |
| :--- | :--- | :--- |
| Boolean | `bool` | Truth value (`true` or `false`) |
| Signed Integers | `i8`, `i16`, `i32`, `i64`, `int` | Fixed-width signed integers; `int` is target pointer width |
| Unsigned Integers | `u8`, `u16`, `u32`, `u64` | Fixed-width unsigned integers |
| Arbitrary Precision | `bigint` | Arbitrary-precision integer |
| Floating-Point | `f32`, `f64` | IEEE 754 floating-point numbers |
| Text & Data | `str`, `bytes` | Immutable UTF-8 text string, immutable raw byte sequence |
| Integer ranges | `typeof (0..0)` | Immutable integer interval bounds |
| Unit & Bottom | `()`, `never` | Singleton unit value `()`, empty uninhabited type |

```ril
let a: int = 42
var b = a
b += 1
assert(a == 42 && b == 43)

-- let mut bad = a                    -- Error [E0402]: use var for value updates
-- let ref bad = a                   -- Error [E0402]: values have no reference target
-- fn bad(ref x: int) -> () {}             -- Error [E0401]: pass values normally
```

`mut` and `ref` require reference data or callable environments. The following exclusions include `str`, `bytes`, and integer ranges:

| Value-type use | Valid forms | Rejected forms | Diagnostic |
| :--- | :--- | :--- | :--- |
| Binding | `let`, `var` | `let mut`, `var mut`, `let ^mut`, `var ^mut`, `let ref`, `var ref` | `E0402` |
| Member / pattern target | Default immutable, `var` | `mut`, `var mut`, `ref`, `var ref` | `E0402` |
| Parameter / argument | Ordinary value | `mut`, `^mut`, `ref`, `new` | `E0401` for reference modes; `E0411` for construction mode |
| Result | `-> T` | `-> new T`; `-> ref(x) T` / `-> ^mut(x) T` | `E0546`; `E0402` |

### Reference Types

Reference types are allocated on the managed garbage-collected heap: arrays (`[]T`), maps (`[K: V]`), records, tuples, sets, and sum type instances.

```ril
-- Reference types: shared heap aliasing:
type Node = { var val: int }
let mut n1 = Node.{ val: 10 }
let ref n2 = n1                       -- 'n2' aliases the exact same heap record as a live ref
let copied = n2.val                    -- Independent value copied through a ref
n1.val = 99                            -- Mutate through 'n1'
assert(n2.val == 99 && copied == 10)

-- n2.val = 100                       -- Error [E0520]: ref grants no writes
-- let ref bad = n2.val              -- Error [E0402]: the member is a value
```

### Record Types and Row Polymorphism

- Record fields and tuple components use the same binding modes. Omitted mode means `let`; an explicit `let` member modifier is not admitted. `var` permits slot replacement, `mut` permits interior/environment writes, and `ref` permits live observation. Every access also requires the enclosing path's permission.
- Named rows contain the fields not explicitly declared. Overlapping labels between an explicit field and its named row are `E0212`.

Records have structural named fields. Closed records reject width subtyping; open records use declared or structurally bound `..R`, never anonymous `..`.

```ril
type User = { id: int, name: str }
let user = User.{ id: 1, name: "Ada" }
-- let missing: User = .{ id: 1 }     -- Error [E0307]: required field 'name' is absent
-- let unknown = user.age            -- Error [E0336]: this product has no field 'age'
-- type Repeated = { id: int, id: int } -- Error [E0210]: field label declared twice
type WithId<R> = { id: int, ..R }
-- type Overlap = WithId<{ id: int }> -- Error [E0212]: row tail overlaps explicit 'id'
type Extended = WithId<{ name: str }> -- OK: disjoint row labels
```

Missing required construction fields use `E0307`. Unknown labels projected or matched against a known product schema use `E0336`. Repeated declared, explicit, or generated field labels use `E0210`; overlap between an explicit type field and a named row uses `E0212`. Projection on a type that does not admit that product projection uses `E0337`, rather than reporting a missing field. Existing opacity restrictions take precedence when the representation is inaccessible.

Use `r.field` or a statically known `r.(key)`. Types use the corresponding `T.field`/`T.(key)`. Record bracket indexing and run-time keys are `E0324`.

Named row tail polymorphism (`..R`) allows generic functions to accept and preserve additional caller fields across pipelines. Pattern destructuring with `..rest` extracts a concrete, statically typed sub-record containing the remaining known fields.

```ebnf
RecordType       ::= "{" [ RecordFieldList ] "}"
MemberMode       ::= "var" [ "mut" | "ref" ] | "mut" | "ref"
RecordField      ::= [ MemberMode ] FieldLabel ":" TypeExpression
TypeProjection ::= PrimaryType "." ( Identifier | TupleIndex | "(" Expression ")" )
TupleIndex     ::= Digit { Digit }
RecordFieldList  ::= ".." PascalCase | RecordField { "," RecordField } [ "," [ ".." PascalCase ] ]
FieldLabel       ::= SnakeCase | UnderscoreName | PascalCase
```

```ril
type Cell = { var count: int }
type State = {
    id: int,                         -- Implicit let: fixed, deeply immutable
    var title: str,                  -- Replaceable immutable value
    mut items: []int,                 -- Fixed writable array
    var mut current: Cell,            -- Replaceable writable reference
    ref source: Cell,               -- Fixed live observation
    var ref cursor: Cell,           -- Replaceable live observation
}
let mut first = Cell.{ count: 0 }
let mut second = Cell.{ count: 0 }
first.count = 1; second.count = 2
let mut state = State.{
    id: 7, title: "draft", items: [1], current: Cell.{ count: 0 },
    source: first, cursor: first,
}
state.title = "ready"
state.items !> Array::push(2)
state.current.count += 1
state.current = Cell.{ count: 3 }
state.cursor = second
assert(state.source.count == 1 && state.cursor.count == 2)
-- state.id = 8                      -- Error [E0520]: default member is immutable
-- state.items = []                  -- Error [E0502]: mut pins the member's reference
-- let hidden = state               -- Error [E0535]: writable/live origins survive
```

```ril
type Counter = { var count: int }
let immutable = Counter.{ count: 0 }
let repeated = (mut immutable, mut immutable) -- OK: outer let suppresses member permissions
-- let mut bad = repeated.0                  -- Error [E0520]: no writer was created
-- type Bad = { ref count: int }           -- Error [E0402]: invalid even under outer let
```

| Member rule | Requirement |
| :--- | :--- |
| Outer immutable reception | Suppress effective permissions before reception; preserve the declaration schema |
| Default member | Deeply immutable data; surviving writers fail with `E0535` |
| Value-type member | Default immutable or `var` only (`E0402`); outer immutability cannot validate another mode |
| Authority use (`E0527`) | Check executable bindings/parameters, not each declared member |
| Immutable/writable aliases | Reject with `E0535`; copying must preserve aliases rather than split them |

```ril
type User = { id: int, name: str }
let u: User = .{ id: 1, name: "Alice" } -- OK: exact closed record match

-- Closed record rejects unexpected fields (E0302):
-- let bad_u: User = .{ id: 1, name: "Alice", age: 30 } -- Error [E0302]: unexpected field 'age' in closed record 'User'

-- Field access is strictly compile-time identifier dot-access:
let user_id = u.id                     -- OK: static field projection
-- let bad_index = u["name"]           -- Error [E0324]: records do not support dynamic index lookup
let static_accessor = u.("name")       -- OK: a statically known key, not a dynamic lookup

-- Type-level field projection:
type IdType = User.id                  -- OK: direct static field type extraction (int)
-- type BadIndex = User["id"]          -- Error [E0324]: record types do not support bracket indexing, use User.id

-- Named row tail polymorphism (generic type preservation):
fn with_timestamp<R>(r: { ..R }) -> { timestamp: int, ..R } {
    .{ timestamp: 1600000000, ..r }
}
let stamped = with_timestamp(.{ id: 1, tag: "audit" })
assert(stamped.tag == "audit" && stamped.timestamp == 1600000000)

-- Type-precise rest destructuring:
type Account = { id: int, username: str, email: str, role: str }
let acc: Account = .{ id: 42, username: "admin", email: "adm@ril.org", role: "root" }

let .{ id, ..rest } = acc
-- 'rest' has static inferred type: { username: str, email: str, role: str }
assert(rest.username == "admin")
assert(rest.email == "adm@ril.org")
assert(rest.role == "root")
```

### Array, Map, and Tuple Types

Bracket syntax defines arrays (`[]T`) and maps (`[K: V]`); tuples use `(T1, T2)`. Range results remain ordinary arrays. `let ref` / `var ref` are binding modes, not array types. `Set<T>` and collection type extractors are standard-library declarations.

```ebnf
ArrayType   ::= "[]" TypeExpression
MapType     ::= "[" TypeExpression ":" TypeExpression "]"
TupleType   ::= "(" TupleMember "," TupleMember { "," TupleMember } [ "," ] ")"
TupleMember ::= [ MemberMode ] TypeExpression
TupleExpr   ::= "(" TupleValue "," TupleValue { "," TupleValue } [ "," ] ")"
TupleValue  ::= [ MemberMode ] Expression
ArrayExpr   ::= "[" [ Expression { "," Expression } [ "," ] ] "]"
MapExpr     ::= "[" ":" "]" | "[" MapEntry { "," MapEntry } [ "," ] "]"
MapEntry    ::= Expression ":" Expression
```

```ril
let mut pair: (var int, mut []int) = (0, [1])
pair.0 = 1
pair.1 !> Array::push(2)
-- pair.1 = []                       -- Error [E0502]: fixed mutable member
let frozen = clone(ref pair)
-- frozen.0 = 2                      -- Error [E0520]: outer let removes member writes
-- frozen.1 !> Array::push(3)         -- Error [E0520]: removal is recursive
assert(frozen.0 == 1 && frozen.1 == [1, 2])
```

Typed product constructors inherit declared member modes; untyped literals default omitted modes to `let`. Explicit literal modes must match the expected schema (`E0301`). Arrays/maps keep their element-storage contracts; these member declarations do not introduce new collection types.

```ril
-- Linear Array ([]T):
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

Empty array literals without contextual expected types require explicit annotation (`E0344`). Invalid index types on an otherwise indexable receiver use `E0301`. An index outside an array's bounds panics at run time.

Map lookups must use safe bracket navigation (`m?[k]`), evaluating to `?V` (`Option<V>`). Plain bracket lookup expressions (`m[k]`) and compound assignments (`m[k] += v`) are prohibited (`E0352`). In-place slot assignment `m[k] = v` inserts or replaces an entry for `k` (requiring deeply immutable `k` under `E0535`).

### Sum Types and GADTs

Sum types represent tagged disjoint unions. Constructor equations allow generalized algebraic data types (GADTs).

```ebnf
SumTypeDecl         ::= [ "pub" ] "type" Identifier [ GenericParams ] [ WhereClause ]
                        "{" VariantDecl { "," VariantDecl } [ "," ] "}"
VariantDecl      ::= PascalCase [ GenericParams ] [ VariantPayload ] [ "->" TypeExpression ]
VariantFields       ::= VariantField { "," VariantField } [ "," ]
VariantField        ::= [ MemberMode ] [ Identifier ":" ] TypeExpression
RecordVariantFields ::= RecordField { "," RecordField } [ "," ]
VariantDeclList  ::= VariantDecl { "," VariantDecl } [ "," ]
VariantPayload   ::= "(" [ VariantFields ] ")" | "{" [ RecordFieldList ] "}"
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

| Variant contract | Requirement |
| :--- | :--- |
| Omitted result equation | The enclosing sum applied to its enclosing parameters |
| Explicit result equation | An instance of that same sum declaration (`E0354` otherwise) |
| Variant-local parameter | Recoverable from the result arguments; no hidden existential parameter (`E0354`) |
| Recovery | After transparent expansion, the parameter occurs as a bare argument or beneath rigid nominal, sum, or structural type constructors |
| Computed static argument / type-function inversion | Does not establish recovery of a parameter |
| Matching | Result equations supply arm-local equalities; recovered parameters do not introduce escaping existential types |

Substitution must satisfy every occurrence of a recovered parameter and its declared sort. These declaration checks do not perform inverse evaluation of arbitrary type functions.

#### Constructor-Tuple Equivalence Invariant

Data constructors (algebraic sum type variants and nominal type wrappers) establish a definitional equivalence between comma-separated multi-field declarations and single-tuple payloads:
$$\text{Variant}(T_1, T_2, \dots, T_n) \equiv \text{Variant}((T_1, T_2, \dots, T_n)) \quad (n \ge 0)$$

For multiple payload members this equivalence preserves every member mode. A single unnamed payload forwards its value's checked reception/retention contract; it does not add a default immutable member around that payload. Named and tuple payload members retain their own declared modes.

Ril strictly possesses no 1-element tuples `(T,)` (`(x)` denotes parenthesized grouping; tuples require $\ge 2$ elements; `()` denotes unit). Constructor arity $n$ in expressions and patterns is strictly deterministic:
- **Scope Restriction (Strict Constructor Boundary)**: Equivalence is confined strictly to Data Constructors. Ordinary functions (`fn`), closures, and methods maintain strictly separate parameter lists (`E0314` for an arity mismatch).
- **Positional Tuple Expansion & Literal Compatibility ($n \ge 2$)**: In expression construction and pattern matching, $C(e_1, \dots, e_n)$ and explicit tuple literals $C((e_1, \dots, e_n))$ are definitionally equivalent: outer constructor parentheses absorb inner tuple parentheses.
- **Whole-Tuple Binding or Single Argument ($n = 1$)**: $C(val)$ constructs or matches the scalar payload or whole-tuple object.
- **Unit Payload Constructor ($n = 0$)**: When a variant's payload type is `()`, $C()$ constructs or matches the unit payload directly ($C() \equiv C(())$ ). Bare constructor identifiers without parentheses (e.g. bare `Ok`) are strictly first-class constructor functions (`fn(T) -> Result<T, E>`), and can be bound or passed as function values. Constructing a payload-bearing result still requires a call.
- **Nullary Variant Tag Invariant**: Variants declared without a payload (e.g. `None` in `type Option<T> { Some(T), None }`) are pure zero-field tags: they MUST be written without parentheses (`None`). Supplying argument parentheses to a nullary variant (`None()`) is statically rejected (`E0353`).
- **Non-Transitivity (Single-Layer Invariant)**: Equivalence applies strictly to the outermost constructor argument boundary. Nested tuples (e.g. `Variant((A, B), C)`) require explicit grouping and do NOT flatten recursively (`Variant(a, b, c)` is rejected with `E0314`).
- **Rigid Type Variable Invariant**: Deconstructing $C(p_1, \dots, p_n)$ ($n \ge 2$) against an unconstrained generic type parameter $T$ is statically rejected with `E0301`.
- **First-Class Constructor Canonical Type**: A constructor $C$ carrying a tuple payload $(T_1, \dots, T_n)$ possesses the canonical unary first-class callable type $\text{fn}((T_1, \dots, T_n)) \to S$. In Check Mode expecting a multi-parameter callable ($\Gamma \vdash C \Leftarrow \text{fn}(T_1, \dots, T_n) \to S$), context-directed $\eta$-expansion ($\backslash x_1, \dots, x_n \to C(x_1, \dots, x_n)$ ) applies.

```ril
-- Result construction and matching with unit payload (n = 0):
let unit_res: Result<(), str> = Ok()             -- OK: n = 0 constructs () payload directly
let auto_unit: Result<(), str> = Ok()            -- OK: the zero-argument constructor supplies ()
assert(auto_unit is Ok())
let make_ok: fn(int) -> Result<int, str> = Ok     -- OK: first-class constructor function

match unit_res {
    Ok() -> println("success"),                  -- OK: n = 0 matches () unit payload
    Err(e) -> println(e),
}

-- Nullary variant tags vs. Data constructors:
let opt: Option<int> = None                      -- OK: nullary tag without parentheses
-- let bad_none = None()                         -- Error [E0353]: variant 'None' has no payload; remove call parentheses

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

-- Functions do NOT auto-tuple (Strict Scope Boundary):
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

Nominal wrappers encapsulate an underlying type into an isolated nominal identity with zero runtime overhead.

```ebnf
NominalDecl      ::= [ "pub" ] "type" PascalCase [ GenericParams ] [ "(" [ TypeList ] ")" ] [ WhereClause ]
```

When `(TypeExpression)` is omitted, `NominalDecl` defines a **Unit Nominal Type** (e.g. `type Marker`).
- **Value Construction**: The bare identifier `Marker` denotes its canonical singleton value (`let m = Marker`).
- **Pattern Matching**: `Marker` acts as a nullary constructor pattern in multi-variant `match` expressions (`match event { Marker -> ... }`). In `let` statements, patterns introducing zero variable bindings (such as `let Marker = m`) are strictly prohibited under the **Non-Vacuous Binding Invariant (`E0309: VacuousBindingError`)**.
- **Prelude Unwrapping**: Unwrapping via `inner(Marker)` evaluates to `()`.
- **Nominal Isolation**: A unit nominal type is an isolated nominal identity, strictly distinct from structural `()`. For example, `Result<Marker, E>` strictly requires `Ok(Marker)` and does NOT permit `Ok()`.

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
type Point2D({ x: f64, y: f64 })       -- Nominal wrapper over structural record

let uid = UserId(1001)
let aid = AccountId(1001)
let c = Coord(10, 20)                  -- OK: positional tuple expansion (n = 2)
let c_compat = Coord((10, 20))         -- OK: explicit tuple literal (n = 1)
let pt = Point2D(.{ x: 10.0, y: 20.0 })

-- uid == aid                          -- Error [E0305]: mismatched nominal types 'UserId' and 'AccountId'
let raw_id: int = inner(uid)           -- OK: unwrap nominal wrapper via prelude 'inner()' (1001)
let raw_coord: (int, int) = inner(c)   -- OK: unwrap nominal wrapper to underlying tuple (10, 20)
let raw_pt: { x: f64, y: f64 } = inner(pt) -- OK: unwrap underlying record via 'inner()'
let UserId(unwrapped_id) = uid         -- OK: pattern-matching unwrap
let Point2D(.{ x, y }) = pt            -- OK: structural record pattern unwrap
let Coord(cx, cy) = c                  -- OK: positional tuple pattern unwrap
let Coord(pair) = c                    -- OK: whole-tuple pattern unwrap
let make_user_id: fn(int) -> UserId = UserId -- OK: constructor function value
```

### Deep Immutability

```ril
type Cell = { var count: int }
let mut source = Cell.{ count: 1 }
let ref observed = source
let mut independent = clone(ref observed)
let immutable = clone(ref observed)   -- let recursively removes all member permissions
independent.count = 2
source.count = 3
assert(observed.count == 3)
assert(independent.count == 2)
assert(immutable.count == 1)
-- let mut bad = immutable                -- Error [E0520]: immutable data cannot acquire write permission
```

- **Default Immutability**: Plain `let`, plain `var` data, unmodified parameters, and default members receive deeply immutable ordinary data. Plain `var` may replace its slot; it does not permit live or writable referenced data.
- **Recursive Permission Removal**: Outer `let` removes effective `var`, `mut`, and `ref` permissions throughout the ordinary reachable graph. This is idempotent, including cycles; it preserves declaration schemas, nominal/opaque identities, and callable parameter/effect/state contracts. It cannot copy, freeze, consume, or revoke an existing writer. Surviving writable/live origins fail with `E0535`.
- **Ordinary Clone**: `clone` preserves declaration schemas, aliases, and cycles in an isolated new graph. A lawful writable receiver may activate the new copy's declared writable members; default members remain immutable. Existing source permissions never increase. Internal writable aliases require the local `^mut` marker; conflicting immutable/writable member aliases remain `E0535`.
- **Copy Isolation**: Ordinary deep copying does not suspend, invoke user callbacks, or permit an overlapping write during the copy. The source is preserved.
- **Eligibility (`E0530`)**: Check every reachable ordinary constituent. Retained closure environments, scoped resources, tasks, unique receivers, and other non-clonable values cannot be hidden by wrapping or `ref` handles.
- Immutable environment-free function values are copyable. Opaque resources use only their explicit contracts.

```ril
type Cell = { var count: int }
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

Ascription never grants permissions or makes a resource ordinary data. Value results use `-> T`; plain reference results require deep immutability. `new T` proves a newly constructed or validly transferred construction root with preserved write authority, not whole-graph publication or fresh-storage eligibility. Parameter-root returns and contained dependencies follow the [return contracts](#return-construction-permissions-and-sources).

### Type Identity and Subtyping

```ril
type Animal = { name: str }
type Dog = { name: str, breed: str }
type Getter<T> = fn() -> T
fn make_dog() -> Dog { .{ name: "Fido", breed: "Collie" } }
let get_dog: Getter<Dog> = make_dog       -- OK
-- let get_animal: Getter<Animal> = make_dog -- Error [E0301]: closed records reject width subtyping
```

| Type position | Subtyping |
| :--- | :--- |
| Closed record | No width subtyping; extra fields require an open row |
| Record member | Writable/`ref` schemas retain matching modes; immutable reception compares permission-suppressed data shapes. Writable/replaceable data is invariant; immutable data covariant |
| Callable with identical parameter modes | Parameters contravariant; result shape covariant; independently check return construction/mode/source guarantees; closed normalized effect/capability contracts match exactly, while explicit open markers admit additional actual obligations only in their selected dimension |
| `&^mut` capability contract | Includes its prescribed write/retention implications during normalization; a closed `&^mut` row does not match an actual `&mut`-only row, and openness never changes parameter modes or handle permissions |
| Array / map | Element and key/value types invariant |
| Tuple | Components invariant; immutable reception suppresses modes, otherwise modes match; only `var` members permit slot replacement |
| Sum / nominal arguments | Invariant; transparent aliases retain the expanded type's identity |

Member modes participate in structural schemas. Outer immutable reception suppresses permissions without changing those declaration identities or introducing container subtyping.



### Complete Provenance and Required Annotations

```ril
fn identity<T>(ref value: T) -> ref(value) T { value }
type Cell = { var count: int }
let mut source = Cell.{ count: 0 }
let ref packet = .{ ref item: identity(ref source) }
let ref observed = identity(ref packet.item)
source.count += 1
assert(observed.count == 1)
-- let hidden = identity(ref packet.item) -- Error [E0535]: source still has a surviving writer
-- let mut stolen = identity(ref observed) -- Error [E0528]: a ref return cannot grant writes
```

- **Complete Static Provenance**: Track possible origins, permissions, immutable/live facts, aliases, retention/escape dependencies, and scope/task ownership for all storage, references, environments, and resources. Conservative judgments may overapproximate execution; obligations cannot be erased.
- **Propagation**: Preserve these facts through aggregates, projections, branches, recursion, returns, calls, opaque boundaries, handlers, cleanup, and modules. Every handle, member mode, and stored constituent limits the resulting authority. A default member imposes deep immutability; `mut` permits interior writes without slot replacement. Independent scalar copies carry no reference authority; capturing a scalar cell retains its origin.
- **No Semantic Erasure**: An omitted annotation, abbreviated callable type, or ordinary call spelling never discards these facts. The compiler infers the full contract of every function. Public, private, local, and test named definitions require their prescribed source spelling under [mandatory contract completion](#mandatory-contract-inference-and-completion); anonymous functions have no mandatory source-annotation completion. Private implementation names need not become public identifiers; their semantic dependencies and internal alias relations remain in verified contract metadata. A plain data return `-> T` establishes immutability; it cannot conceal a live or writable alias.
- **Conservative Alternatives**: Retain the union of possible origins, accesses, retention, and escape obligations, and only permissions common to all alternatives. Preserve origin relations between inputs and outputs and between output components: a relation established in every retained alternative remains established after the join. Prune only branches excluded by the specified static computations and typing rules. An unproved run-time condition is not evidence of uniqueness or impossible escape. Unknown overlap remains possible overlap; an incomplete proof cannot authorize mutable access, immutable publication, or task crossing that requires it.
- **Recursive Dependencies**: Loop and recursive call dependencies retain possible origins and unresolved relationships, including termination conditions and finite-budget coverage. A cycle is not evidence of freshness, disjointness, non-escape, termination, or an empty callable row. An obligation may be discharged only by an established fact; unresolved dependencies remain obligations at every affected use. Apply the use's existing diagnostic when its required proof is absent.
- **Authority and Discharge**: Prove each permission from a declaration, a traced source, a fresh-data rule, or an explicitly specified resource contract. Local discharge requires all relevant authority roots and environments to be confined; a local variable name or locally handled effect is not evidence of confinement. Minimal concrete capabilities (`E0529`) are calculated under these conservative rules, not arbitrary run-time equivalence.
- **Source Annotations**: Infer and check binding/parameter modes, argument markers, local writable-sharing markers, return construction/modes/sources, effects, captures, and concrete invocation capabilities. Named definitions must complete their required annotations. Anonymous functions may leave type, result, effect, state, capture, and returned-source contract annotations to inference; written annotations and contextual callable types remain checked constraints. Parameter modes, argument markers, binding modes, and shared-reception markers retain their permission semantics: omitting a contract annotation supplies no absent authority. Neither inference nor completion may change sharing, object identity, evaluation order, allocation, or resource ownership.
- **Diagnostic Provenance**: Semantic diagnostics MUST make the derived access, sharing, escape, and effect obligations and their source explanations available, including facts omitted from source. An explanation identifies the relevant origin or contract, propagation steps, involved use or boundary, and the rule that accepts or rejects it. Multiple possible origins and an unproved disjointness condition must be reported as such, not replaced with a fabricated exact origin. Explanations also apply to accepted programs and inferred obligations; their presentation is optional and cannot change validity.

For `hidden`, connect `source`'s writer through the `ref` argument, `ref` member, return, and prohibited immutable reception. For `stolen`, identify the return's `ref` permission.

```ril
type Cell = { var count: int }
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

- **Local Construction**: A fresh ordinary result may enter `let` when its construction scope or call ends and no relevant outside writer, live dependency, or active environment survives. `new` records root freshness and write authority; complete provenance separately decides publication and initial-reception eligibility. Parameter/external aliases retain their restrictions (`E0528`). Ordinary writable bindings retain their authority until lexical scope ends; last textual use does not revoke it. Reassigning `var mut` replaces its path without revoking other paths.

- **Fresh Evaluation**: Each successful ordinary allocation creates new storage distinct from pre-existing storage. A newly constructed aggregate may still contain references to pre-existing objects; freshness of its outer slots does not establish disjointness of its reachable graph. Each ordinary deep clone creates new writable regions isolated from the source and all pre-existing writable regions, preserving aliases within that one copy. Repeated evaluations of one expression do not denote one shared allocation. Calling an arbitrary function twice does not establish freshness; the function's actual return relation must supply it.

- **Initial Writable Reception**: [Fresh storage inputs](#fresh-values-in-storage-calls) may receive unpublished construction authority. Read-only bindings and parameters end this eligibility; allocation identity or last use cannot restore it.

```ril
-- Cell and swap have the preceding contracts; choose_order is a run-time bool input.
fn permute(flag: bool, ^mut a: Cell, ^mut b: Cell) &^mut &return{^mut a, ^mut b}
    -> new (mut Cell, mut Cell) {
    if flag { (^mut a, ^mut b) } else { (^mut b, ^mut a) }
}
let mut left = Cell.{ count: 1 }
let mut right = Cell.{ count: 2 }
let ^mut pair = permute(choose_order, ^mut left, ^mut right)
swap(mut pair.0, mut pair.1)           -- OK: either ordering preserves the inputs' proven disjointness

let mut cells = [Cell.{ count: 0 }, Cell.{ count: 1 }]
cells[0].count += 1
-- i and j are unconstrained run-time integer inputs:
-- swap(mut cells[i], mut cells[j])   -- Error [E0523]: the indices may select the same writable origin
```

The two components returned by `permute` may each originate in either argument, but are disjoint whenever the two actual inputs are disjoint. That common relation survives the branch and return. Distinct parameter names alone establish no such relation. Unrelated run-time selections retain possible overlap unless an applicable rule proves otherwise.

```ril
type Cell = { var count: int }
let mut source = Cell.{ count: 0 }
source.count += 1
-- let frozen = source               -- Error [E0535]: source's scope has not ended, even without later use
let finished = {
    let mut builder = Cell.{ count: 0 }
    builder.count += 1
    builder
}
assert(finished.count == 1)           -- OK: construction scope ended without an outside writer
-- let hidden = { let mut alias = ^mut source; alias.count += 1; alias }
-- Error [E0535]: ending the alias's scope does not end source's authority
```

Escaped environments and stored writable paths survive their creating scope and still prevent immutable publication. Last-use rules for temporary mutable access or `ref` handles do not implicitly consume an ordinary writable binding. Resource consumption follows only its listed contracts.

### Functional Updates via Derive

```ril
type Cell = { var count: int }
type Pair = { left: Cell, right: Cell }
let shared = Cell.{ count: 1 }
let base = Pair.{ left: shared, right: shared }
let updated = base |> derive \mut draft -> {
    draft.left.count += 1
}
assert(base.left.count == 1 && shared.count == 1)
assert(updated.left.count == 2 && updated.right.count == 2)

let external = Cell.{ count: 10 }
let inserted = base |> derive \mut draft -> {
    draft.left = external
    draft.left.count += 1
}
assert(external.count == 10)
assert(inserted.left.count == 11)
```

#### Normative Rules for Functional Updates

- **Input (`E0536`)**: `derive` accepts immutable ordinary data; publish a live source's copy with `let snapshot = clone(ref live)` first. The result is immutable data of the same declaration schema.
- **Draft**: The recipe receives `mut draft`, returns `()`, and may temporarily replace or modify any data member regardless of its declared mode. This confined privilege ends before immutable publication; declaration schemas remain unchanged.
- **Identity**: Each source object has one draft counterpart, including newly inserted immutable references. Repeated references and cycles are preserved; all draft aliases see the same changes.
- **Sharing**: Copy every affected value/reference region, including changes needed to preserve graph identity. Unaffected immutable regions may be shared. Neither unique ownership nor a new root for a no-op recipe is guaranteed.
- **Insertion (`E0535`)**: Accept immutable references or recipe-local fresh data without outside writers. Inserted immutable objects enter the same draft correspondence before later writes; existing draft aliases retain their identity.
- **Confinement (`E0607`)**: Draft references cannot escape through returns, assignments, containers, or published closures. Non-escaping helper calls are allowed. Publish the immutable result only after normal recipe completion.
- **Abort**: Forward recipe effects and external-state obligations; discharge draft-local writes. Panic/abort publishes no result and preserves all immutable inputs. Unrelated external writes remain committed.

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

### Generic Parameters, Defaults, and Value Sorts

```ril
fn log_id<T: { id: int, ..R }>(item: T) -> int { item.id }
```

Generics admit type, const-value, and [static-key](#static-key-parameters-and-computed-value-projection) parameters. They apply to data, wrapper, sum, and callable declarations.

```ebnf
GenericParams         ::= "<" GenericParamDecl { "," GenericParamDecl } [ "," ] ">"
GenericParamDecl      ::= TypeParamDecl | ConstParamDecl | StaticKeyParamDecl
TypeParamDecl         ::= PascalCase [ TypeConstraint ] [ "=" TypeExpression ]
TypeConstraint        ::= [ ":" TypeSort ] { "|>" PipelineConstraint }
TypeSort              ::= TypeSetSort | "Type" | KindSignature | RecordConstraint
TypeSetSort           ::= TypeReference "|" TypeReference { "|" TypeReference }
PipelineConstraint    ::= QualifiedName [ GenericArgs ]
ConstParamDecl        ::= SnakeCase ":" ValueType [ "=" Expression ]
KindSignature         ::= "Type" "->" ( "Type" | KindSignature )
RecordConstraint      ::= "{" [ RecordConstraintField { "," RecordConstraintField } "," ] ".." PascalCase "}"
RecordConstraintField ::= [ MemberMode ] Identifier ":" TypeExpression
KeyofConstraint       ::= "keyof" TypeExpression
GenericArgs           ::= "<" GenericArg { "," GenericArg } [ "," ] ">"
GenericArg            ::= TypeExpression | Expression
StaticKeyParamDecl    ::= PascalCase ":" KeyofConstraint [ "=" Expression ]
ValueType             ::= TypeExpression
```

- **Trailing Defaults Invariant (`E0316`)**: If a generic parameter declares a default argument (`= Default`), all subsequent generic parameters in the same parameter list MUST declare default arguments.
- **Telescopic Left-to-Right Scoping Invariant (`E0320`)**: A default argument expression $D_i$ may reference generic parameters declared to its left ($X_1, \dots, X_{i-1}$). Forward references and direct/indirect circular dependencies are statically rejected (`E0320`).
- **Generic Closed Type Sets (`TypeSetSort`, `E0301`)**: A generic parameter may constrain its admitted domain to a finite union of types (`T: int | f64`). Unlike value-level untagged unions (`E0318`), a type set constraint does not create an untagged runtime union type; monomorphization specializes $T$ to each concrete member. The compiler performs definition-site polyvariant type checking across all member types $\tau \in \{T_1, \dots, T_n\}$, verifying that the generic body's operations are well-typed for every alternative. Supplying a type outside the set triggers `E0301: TypeMismatchError`.
- **Pipeline Type Constraints (`T |> Guard`, `E0301`, `E0306`)**: A type parameter may pipe into one or more pure type functions (`T |> Numeric`). The guard must be a compile-time pure `type` function of kind `Type -> Type` (`E0306`). An argument type $T_{arg}$ satisfies the guard if and only if:
  $$\text{Valid}(T_{arg}) \iff T_{arg} \not\equiv \text{never} \quad \wedge \quad \text{Guard}\langle T_{arg} \rangle \equiv T_{arg}$$
  The bottom type `never` is statically rejected before guard evaluation, preventing vacuous satisfaction. If $\text{Guard}\langle T_{arg} \rangle$ does not produce definitional identity with $T_{arg}$, the argument is rejected under `E0301`. Multiple guards pipe from left to right: `T |> Guard1 |> Guard2` $\equiv \text{Guard2}\langle \text{Guard1}\langle T \rangle \rangle$.
- **Orthogonal Constraint Composition**: Structural row polymorphism and pipeline guards compose naturally: `T: { id: int, ..R } |> AuditGuard` verifies that $T$ satisfies the open record structure and conforms to `AuditGuard`.
- **Static Value Sorts**: Const parameters admit scalar values, atomic type tokens, and finite immutable aggregates without resource or callable authority. `token: Type` is a static value parameter, distinct from a type parameter `T: Type`. Admission of static-only token values never permits their run-time materialization.
- **Const Generic Evaluation & Purity Invariant (`E0814`, `E0323`)**: Const generic arguments evaluate at compile time within the pure symbolic domain ($\mathbf{Eff} = \emptyset, \mathbf{Cap} = \emptyset$). Non-constant runtime expressions passed to const parameters trigger `E0814`. Arguments failing sort constraints trigger `E0323`.
- **No Untagged Literal or Storage Union Types (`E0318`)**: Concrete values (strings, integers, booleans) and untagged value unions (`int | str`) cannot serve as storage, variable, or binding types (`E0318`). Discrete domain states MUST be modeled via tagged sum types (`type HttpMethod { Get, Post }`). Concrete values enter the type system strictly as compile-time arguments to const parameters (`Buffer<u8, 1024>`, `Matrix<f64, 4>`). Finite type sets (`T: int | f64`) are permitted exclusively as static domain constraints on generic parameters (`TypeSetSort`), which are monomorphized to single rigid types.
- **Function Generic Default Prohibition (`E0317`)**: Function generic parameters cannot declare defaults (`fn f<T = int>` is rejected); function types are inferred bidirectionally at call sites.

Generic arguments are checked against the declaration's parameter category: type syntax for a type parameter, a static token/value expression for a value parameter. Quoting a type does not implicitly turn that value back into a type argument (`E0306`). `Type<T>` is an exact static metatype, not a literal storage type; `<42>` remains invalid and const arguments such as `Buffer<u8, 42>` keep their existing meaning.

```ril
-- Closed Type Set Constraint:
fn add<T: int | f64>(a: T, b: T) -> T { a + b }
assert(add(1, 2) == 3)
assert(add(1.5, 2.5) == 4.0)
-- let bad_add = add("a", "b")          -- Error [E0301]: type 'str' does not satisfy constraint 'int | f64'

-- Pipeline Type Function Constraint:
type Numeric = \T -> match <T> {
    <int> | <i64> | <f64> -> <T>,
    _ -> <never>,
}
fn multiply<T |> Numeric>(a: T, b: T) -> T { a * b }
assert(multiply(3, 4) == 12)
-- let bad_mul = multiply("x", "y")     -- Error [E0301]: type 'str' does not satisfy constraint 'Numeric'

-- Composed Structural and Pipeline Constraint:
type NonZero = \T -> match <T> {
    <{ val: int, ..let _ }> -> <T>,
    _ -> <never>,
}
fn get_val<T: { val: int, ..R } |> NonZero>(item: T) -> int { item.val }
assert(get_val(.{ val: 42, label: "ok" }) == 42)

type Token<value: f64>(int)
meta let _ = assert(<Token<0.0>> != <Token<-0.0>>)
meta let _ = assert(<Token<0.0 / 0.0>> == <Token<0.0 / 0.0>>)

type Choose = \entries: [str: int] ->
    if Map::keys(entries)[0] == "a" { <int> } else { <str> }
type FirstOrder = Choose<["a": 1, "b": 2]>  -- int
type OtherOrder = Choose<["b": 2, "a": 1]>  -- str
```

Static argument equivalence determines type and effect instantiation identity. It is distinct from run-time `==`. Arguments must first have the same admitted sort.

| Static value | Equivalence |
| :--- | :--- |
| Booleans, integers, strings, bytes, unit | Exact value; strings are exact scalar sequences |
| Floating values | Canonical IEEE bit representation; signed zeros differ, canonical NaNs agree |
| Type tokens, after adaptation to the formal value sort | Represented target types are definitionally equal, preserving nominal/opaque identity and full schemas; not token address, variable name, or display spelling |
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

An inactive constructor alternative does not determine an otherwise unconstrained function type argument. After applying declared defaults, an ordinary generic call with an `Ok` argument still needs information choosing the error type; a result context choosing only the success type is insufficient. For example, `Results::expect(Ok(1), "missing")` and `Test::assert_ok(Ok(1))` require an explicit `Result<int, str>` input context or explicit function type arguments. Without such information they use `E0344`; an inactive argument does not become a hidden existential variable or acquire an implicit `never` or `str` default.

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
pub type Buffer<T = u8, cap: int = 1024>({
    data: []T,
    len: int,
})

let b1: Buffer = Buffer.{ data: [], len: 0 }    -- OK: resolves to Buffer<u8, 1024>
let b2: Buffer<u8, 2048> = Buffer.{ data: [], len: 0 } -- OK: explicit capacity override
let b3: Buffer<i32> = Buffer.{ data: [], len: 0 } -- OK: resolves to Buffer<i32, 1024>

-- Dependent default arguments (Telescopic Left-to-Right):
pub type Matrix<T, rows: int, cols: int = rows> = {
    data: []T,
}

let m_sq: Matrix<f64, 4> = .{ data: [] }        -- OK: square matrix, cols defaults to rows (4)
let m_rect: Matrix<f64, 4, 2> = .{ data: [] }   -- OK: explicit rectangular override

pub type Pair<First, Second = First> = {
    first: First,
    second: Second,
}
let p1: Pair<int> = .{ first: 1, second: 2 }    -- OK: Second defaults to First (int)

-- Rejection: Non-trailing default generic parameter (E0316):
-- type BadOrder<T = int, U> = { a: T, b: U }
-- Error [E0316]: generic parameter without default 'U' cannot follow generic parameter with default 'T'

-- Rejection: Forward reference in default argument (E0320):
-- type BadForward<T = U, U = int> = { a: T }
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
eff AsyncIo { Io, Fiber }
type StateNode = { var count: int, tag: str }
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
    Suspended({ duration_ms: int }),
    Completed(int),
}
let status: TaskStatus = Running(\-> Fiber::yield())
assert(status is Running)

type ValidChannel = {
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
    writer: \mut buf -> { buf !> Array::push(0) },
}
ch.buffer !> Array::push(42)
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
-- type BadGlobal = &up(sub){mut app_cache}   -- Error [E0331]
-- type BadClosure = &up              -- Error [E0331]

-- type BadVariant { Running @Async } -- Error [E0332]: tag annotation
-- type BadMutableVariant { Mutating &mut } -- Error [E0332]: capability on a tag
-- type BadPayload { Suspended(int) @Fiber } -- Error [E0332]: payload does not permit a suffix
-- type BadField = { value: str @Io } -- Error [E0333]
-- type BadMutableField = { buffer: []u8 &mut } -- Error [E0333]: field type is not a callable
-- type BadNamedField = { value: int &up(sub){mut app_cache} } -- Error [E0333]
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
PrimaryType      ::= PrimitiveType | NominalRef | "(" TypeExpression ")"
NominalRef       ::= QualifiedName [ GenericArgs ]
```

| Position | Rule |
| :--- | :--- |
| Data types | Inert shapes: structural products/collections, sums and GADTs, nominal wrappers, opaque types, or pure type-function results |
| Record/tuple member mode | Binding permission bound; `var` controls replacement, `mut` interior writes, `ref` observation; no ambient capability |
| Callable arrow | Carries a complete latent contract; closed rows match exactly, explicit open markers preserve additional actual obligations, and callable values may be stored, passed, returned, and nested in data |
| Bare `@Eff` / `&Cap`, or open markers `@` / `&` / `@&`, as a data type | `E0330` / `E0331`; effects use `eff` declarations, capabilities and callable-row markers are not standalone values or data types |
| Direct effect/capability suffix on a variant | `E0332`, with or without a payload |
| Direct effect/capability suffix on a record field or tuple component | `E0333`; a callable constituent may carry its own suffix |
| Effect/capability constraint on a generic parameter | `E0334`; shape, kind, const, and static-key constraints remain allowed |
| Effect/capability annotation on a type function | `E0335` |
| Effect annotation on a value binding or non-callable array expression | `E0613` |

Binding and origin permissions govern access. Effects govern evaluation and handler dispatch; completed passive values have no direct effect annotation. Stored callables retain invocation obligations. Termination and finite-budget coverage remain separate invocation judgments, not types, capabilities, or effect labels.

## Declarations and Bindings

### Binding Permissions and Storage Matrix

`let` / `var` control slot replacement; default / `mut` / `ref` control data access. Interior operations also require the member's permission. Shared-reception declarations desugar before these permission and authority-use checks.

| Binding | `x = other` | Interior writes | Received data |
| :--- | :---: | :---: | :--- |
| `let` | No (`E0501`) | No (`E0520`) | Deeply immutable, freely shareable across tasks |
| `var` | Yes | No (`E0520`) | Deeply immutable; slot may select another value |
| `let mut` / `let ^mut` | No (`E0502`) | Yes | Fixed writable target; `^mut` explicitly acknowledges initializer sharing |
| `var mut` / `var ^mut` | Yes | Yes | Writable target; `^mut` covers initialization only, and replacement rechecks reception |
| `let ref` | No (`E0502`) | No (`E0520`) | Fixed read-only reference; may observe live data |
| `var ref` | Yes | No (`E0520`) | Read-only reference cursor; immutable or live target |

For direct initialization and `var` replacement, unlisted combinations are allowed subject to ordinary typing, provenance, scope, and authority-use checks. Values copy; references share the selected object, not its source slot.

| Source / condition | Prohibited receiver | Diagnostic |
| :--- | :--- | :--- |
| Value type | Any `mut`, `^mut`, or `ref` binding | `E0402` |
| Immutable reference data or any `ref` | `let mut` / `var mut`, including `^mut` reception | `E0520` |
| Reference graph with a surviving writer or live dependency | Plain `let` / `var` | `E0535` |
| Writable aliases, including internal aliases in a fresh copy, without `^mut` acknowledgment | `let mut` / `var mut` | `E0510` |
| Reassignable writable `var mut` | Persistent `let ref` / `var ref` | `E0531` |
| Independent reference allocation / clone or new writable environment | Persistent `let ref` / `var ref` | `E0543` |

Aliases retain all source restrictions; fresh immutable publication requires no surviving outside writer.

```ril
let initial = 1
var number = initial                   -- let -> var
let saved_number = number              -- var -> let
number = 2
assert(initial == 1 && saved_number == 1 && number == 2)

type Document = { var title: str }
let doc1 = Document.{ title: "Doc 1" }
let doc2 = Document.{ title: "Doc 2" }

var selected = doc1                    -- let -> var
let saved = selected                   -- var -> let
selected = doc2                        -- saved still shares doc1
assert(saved.title == "Doc 1" && selected.title == "Doc 2")

let mut draft = clone(doc1)
let ^mut alias = draft                 -- Explicit writable sharing; no copy
let ref observed = draft
alias.title = "Revised"
assert(draft.title == "Revised" && observed.title == "Revised")
-- let hidden = draft                 -- Error [E0535]: surviving writer
-- let mut stolen = observed          -- Error [E0520]: ref cannot grant writes

var mut active = clone(doc1)
active.title = "Active"
active = clone(doc2)                   -- Slot replacement and interior writes are both used

let mut other = clone(doc2)
other.title = "Selected"
var ref cursor = draft
cursor = other
assert(cursor.title == "Selected")
```

| Authority use (`E0527`) | Required on a statically possible path |
| :--- | :--- |
| `var`, `var ref` | Slot reassignment |
| `let mut`, ordinary `mut` parameter | Interior write, mutable call, or authorized transfer |
| `var mut` | Both reassignment and interior writes |
| `^mut` parameter | Actual retention |

### Shared Writable Reception

```ebnf
SharedMutDecl ::= [ "pub" ] ( "let" | "var" ) "^mut" Identifier
                  [ ":" TypeExpression ] "=" Expression
```

| Declaration | Exact desugaring | Slot behavior |
| :--- | :--- | :--- |
| `let ^mut x: T = expr` | `let mut x: T = ^mut (expr)` | Fixed target |
| `var ^mut x: T = expr` | `var mut x: T = ^mut (expr)` | Reassignable target |

Types are optional in either spelling. The marker covers the complete initializer, including a pipeline or conditional, evaluated once in its original order. This sugar supplies the existing reception acknowledgment, not another permission, publication, or permanent sharing property. Both spellings retain identical origin, write-authority, lifetime, resource, and `E0527` checks.

```ril
type Cell = { var count: int }
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
-- let ^mut bad = immutable           -- Error [E0520]: sugar cannot grant write authority
-- let ^mut bad = observed            -- Error [E0520]: a ref cannot become writable
-- let ^mut bad = 1                   -- Error [E0402]: value types use ordinary let/var
```

Only single identifier declarations admit this sugar. Patterns, member declarations, and scoped forms keep their existing grammar. A pattern's members retain their own modes:

```ril
type Cell = { var count: int }
let mut packet = .{ count: 7, mut item: Cell.{ count: 0 } }
let .{ count, mut item } = ^mut packet -- Explicit expression marker for mixed destructuring
item.count += 1
assert(count == 7 && packet.item.count == 1)
```

### Immutable Bindings

```ebnf
LetDecl ::= [ "pub" ] "let" Pattern [ ":" TypeExpression ] "=" Expression [ "else" Block ]
```

- **Reassignment (`E0501`)**: Pinned slot; identifier cannot be rebound.
- **Authority (`E0520`, `E0521`)**: Deeply immutable; no writes permitted through binding or destructured paths.
- **Origin Requirement (`E0535`)**: Accepts fresh graphs without surviving writers or proven immutable origins, including through `ref` handles; rejects `ref` handles with possible live origins and mutable environments.

```ril
type Counter = { var count: int }
let x = 10
-- x = 20                              -- Error [E0501]: cannot reassign immutable binding 'x'

let mut source = Counter.{ count: 0 }
let ref observer = source
source.count += 1
-- let bad = source                    -- Error [E0535]: a surviving writer prevents immutable publication
-- let bad_ref = observer             -- Error [E0535]: wrapping or aliasing a live ref is not immutable

fn make_items() -> new []int {
    let mut items: []int = []
    items !> Array::push(1)
    items
}
let items = make_items()               -- OK: construction authority ended; immutable publication
let alias = items                     -- OK: multiple references to immutable data
-- let mut stolen = items             -- Error [E0520]: ordinary aliasing cannot recover write permission

-- Pattern destructuring:
let (a, b) = (1, 2)
type Config = { capacity: int, items: []int }
let cfg = Config.{ capacity: 64, items: [] }
let .{ var capacity, items: _ } = cfg
capacity += 1                         -- OK: independent scalar copy
-- let .{ capacity: _, mut bad } = cfg -- Error [E0521]: immutable reference cannot acquire write permission
```

### Pinned Mutable Handles

```ebnf
LetMutDecl ::= [ "pub" ] "let" "mut" Pattern [ ":" TypeExpression ] "=" Expression [ "else" Block ]
```

#### Normative Rules for Pinned Handles

- **Pinned Handle (`E0502`)**: Identifier permanently pinned to initial allocation; cannot be rebound (`use 'var mut'`).
- **Value Types (`E0402`)**: Scalars have no interior mutability; `let mut` is statically rejected (use `var`).
- **Roots for `ref` handles**: Pinned handles provide guaranteed reference stability as roots for `let ref` and `var ref`.
- **Authority Use (`E0527`)**: Must perform an interior write, mutable call, or authorized transfer on a possible path.

```ril
type Buffer = { mut items: []int }
let mut buf = Buffer.{ items: [1, 2] }
buf.items !> Array::push(3)            -- OK: in-place write to pinned buffer
-- buf = Buffer.{ items: [] }          -- Error [E0502]: use 'var mut' for both reassignment and interior writes
-- let mut count: int = 0              -- Error [E0402]: value type 'int' has no interior mutability; use 'var'

-- Pattern-level pinned mutable destructuring:
type NodePair = { mut left: Buffer, mut right: Buffer }
let mut pair = NodePair.{ left: Buffer.{ items: [] }, right: Buffer.{ items: [] } }
let .{ mut left, mut right } = ^mut pair
left.items !> Array::push(10)          -- OK: pinned mutable handle
right.items !> Array::push(20)         -- Both destructured authorities are exercised
-- left = Buffer.{ items: [] }        -- Error [E0502]: cannot reassign pinned handle 'left'

-- Definite Mutation Invariant:
-- let mut unused = Buffer.{ items: [] } -- Error [E0527]: variable 'unused' declared 'let mut' but never modified in-place
```

### Reassignable Mutable Variables

```ebnf
VarDecl    ::= [ "pub" ] "var" Pattern [ ":" TypeExpression ] "=" Expression [ "else" Block ]
VarMutDecl ::= [ "pub" ] "var" "mut" Pattern [ ":" TypeExpression ] "=" Expression [ "else" Block ]
```

#### Normative Rules for Reassignable Variables

- **Plain `var` (`E0520`, `E0535`)**: Reassignable slot receiving deeply immutable values/graphs. Live observation requires `var ref`; receiving existing writable data without copying fails with `E0535`.
- **`var mut` (`E0520`, `E0402`)**: Reassignable slot AND interior write authority. Scalars rejected (use plain `var`).
- **`ref` Origins (`E0531`)**: Plain `var` supplies its current immutable reference; later reassignment does not retarget a `ref`. A `var mut` root cannot supply a persistent live `ref`.
- **Authority Use (`E0527`)**: Plain `var` must exercise reassignment; `var mut` must exercise both reassignment and interior writes.

```ril
-- 1. Plain var: reassignable scalar
var counter = 0
counter += 1                           -- OK: reassignable scalar
counter = 10                           -- OK: direct reassignment
assert(counter == 10)

-- 2. Plain var: reassignable read-only cursor over reference data
type Node = { val: int, following: ?Node }
let ro_node2 = Node.{ val: 2, following: None }
let ro_node1 = Node.{ val: 1, following: Some(ro_node2) }
var cursor = ro_node1                  -- OK: reassignable slot containing immutable data
assert(cursor.val == 1)
cursor = ro_node2                      -- OK: another immutable Node
-- cursor.val = 99                     -- Error [E0520]: cannot mutate field 'val' through read-only handle 'cursor'

-- 3. Fully mutable reference variable:
type Buffer = { mut items: []int }
var mut active_buf = Buffer.{ items: [1] }
active_buf.items !> Array::push(2)     -- OK: in-place mutation
active_buf = Buffer.{ items: [10, 20] } -- OK: handle reassignment permitted on 'var mut'
assert(len(ref active_buf.items) == 2)
-- var mut scalar = 0                  -- Error [E0402]: scalar mutation uses plain var

-- 4. Reassignable writable root cannot supply a persistent live ref:
-- let ref bad_ref = active_buf       -- Error [E0531]: var mut is not a pinned mutable root

-- 5. Pattern-level var destructuring:
var (start_idx, end_idx) = (0, 10)
start_idx += 1; end_idx -= 1           -- OK: both variables reassignable

-- 6. Definite Mutation Invariant:
-- var unused_var = 100                -- Error [E0527]: variable 'unused_var' declared 'var' but never modified or reassigned
```

### Scoped Resource Bindings

```ril
type Resource = { var name: str, var mut on_close: fn() & -> () }
let mut events: []str = []
{
    let scoped mut first = Resource.{
        name: "first", on_close: \-> { events !> Array::push("first") },
    }
    let scoped mut second = Resource.{
        name: "second", on_close: \-> { events !> Array::push("second") },
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
        name: "r", on_close: \-> { events !> Array::push("old") },
    }
    resource.on_close = \-> { events !> Array::push("new") }
}
assert(events == ["new"])
-- let scoped scalar = 42              -- Error [E0541]: no cleanup contract
```

#### Normative Rules for Scoped Bindings

| Concern | Rule |
| :--- | :--- |
| Ordinary resource | Accessible unit-result cleanup callable required (`E0541`); `on_close: fn() & -> ()` preserves actual capabilities, while cleanup effects, finiteness, and invocation authority retain their separate checks |
| Opaque resource | Requires an explicit scoped-cleanup contract; opacity alone supplies none (`E0541`) |
| Registration | After successful initialization; per binding and per loop activation; failed initialization registers nothing |
| Exit | Invoke once in reverse registration order, including cancellation/abort; double-fault exception below |
| Callback selection | Read the current `on_close` at exit; retain no earlier snapshot. Opaque resources use their specified action |
| Initialization/replacement | Preserve cleanup eligibility and permissions; no residual effects (`E0616`), and prove finite cleanup (`E0617`) |
| Mutable cleanup environment | Requires `let scoped mut` and `mut`/`var mut on_close`; replacement also needs `var`; cleanup invocation satisfies `E0527` |
| Other binding modes | Plain `let scoped` requires immutable data; rebinding: `E0502`; `var`/`var mut`: `E0532` |
| Invocation | Internal handlers and permitted writes allowed; check exclusivity then, not as continuous registration access |
| Escape | `ref` handles, closures, containers, and transfer cannot carry scoped authority out (`E0604`); detached ordinary-data copies are exempt |
| Children | Finish before cleanup of resources they could access |

```ril
type WrongCleanup = { on_close: int }
-- let scoped bad = WrongCleanup.{ on_close: 0 } -- Error [E0541]: on_close is not fn() -> ()
type Cleanup = { on_close: fn() -> () }
{ let scoped good = Cleanup.{ on_close: \-> () } } -- OK: implicit cleanup uses the binding
```

Missing, inaccessible, or shape-incompatible scoped cleanup contracts are `E0541`. A shape-compatible cleanup's residual effects, divergence, or insufficient authority retain `E0616`, `E0617`, or the applicable permission diagnostic. An opaque resource requires its explicit contract; no structural access through opacity is implied.

| Cleanup panic occurs during | Outcome |
| :--- | :--- |
| Normal exit | Begin panic unwinding of remaining resources |
| Panic, cancellation, or abort | Record both causes; abandon remaining cleanup in the failed frame |

Abandoned computations cannot resume. A double fault fatally fails its task or an unsupervised program. A pure parallel branch exposes the double fault only when that branch is visible in reference evaluation.

```ebnf
ScopedDecl ::= [ "pub" ] "let" "scoped" [ "mut" ] Pattern [ ":" TypeExpression ] "=" Expression [ "else" Block ]
```

### Read-Only Reference Bindings

```ebnf
LetRefDecl ::= [ "pub" ] "let" "ref" Pattern [ ":" TypeExpression ] "=" Expression [ "else" Block ]
VarRefDecl ::= [ "pub" ] "var" "ref" Pattern [ ":" TypeExpression ] "=" Expression [ "else" Block ]
```

```ril
type Cell = { var count: int }
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
-- let mut bad = ^mut fixed           -- Error [E0520]: immutable-backed refs grant no writes
-- let hidden = chosen                -- Error [E0535]: a possible live origin remains live
```

#### Normative Rules for Read-Only References

`ref` grants read-only reference access. Immutable targets stay constant; writable targets remain live. Persistent `ref` handles trace each origin through projections, `ref` handles, and verified calls.

| Target / operation | Rule |
| :--- | :--- |
| Value-type target | Reject with `E0402`; reading a value member copies its current value |
| Immutable reference / existing immutable callable environment | Accept from `let`, ordinary `var`, or a verified result; preserve immutable provenance |
| Live reference | Require a pinned `let mut` origin; a `var mut` root fails with `E0531` |
| Branch / cursor / forwarded `ref` | Every possible origin must be immutable or an eligible live origin; preserve all alternatives |
| Independent allocation, clone, or new writable environment | No established observation origin by itself (`E0543`); publish immutable or bind a lawful writable root first |
| Passive aggregate / observer closure | May combine existing immutable reference origins, eligible live origins, and immutable values; wrappers cannot repair origins |
| Interior write or `mut` / `^mut` upgrade | Reject with `E0520` |
| Ordinary immutable reception | Require every possible origin to be deeply immutable; any possible live origin fails with `E0535` |
| `ref` handle task crossing | Reject with `E0601` |
| Initializer / projection | Evaluate once; keep the selected object alive; source-slot or member replacement does not retarget it |
| Observer closure invocation | Read captures when invoked |
| `let ref` reassignment | Reject with `E0502` |
| `var ref` reassignment | Recheck origins; a reachable reassignment is required (`E0527`) |

The same origin rules apply to `ref` members and reference pattern targets. [`ref` parameters](#parameter-modes-caller-obligations-and-defaults) use call-time observation rules.

```ril
type Cell = { var count: int }
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
-- let mut stolen = ^mut observed     -- Error [E0520]: no permission upgrade
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

-- Single evaluation and GC root preservation:
type Parent = { var mut child: Cell }
let mut parent = Parent.{ child: Cell.{ count: 1 } }
let ref child = parent.child
parent.child = Cell.{ count: 9 }
assert(child.count == 1)                -- Keeps the original child, not a reactive projection

type TaskStatus { Pending(str), Finished(int) }
let mut tasks: []TaskStatus = [TaskStatus::Pending("waiting")]
let ref v = tasks[0]                   -- 'v' holds a read-only ref of the Pending object
tasks[0] = TaskStatus::Finished(42)     -- Slot 0 is updated; 'v' safely keeps the original object

-- Pattern-level ref destructuring:
type NodePair = { mut left: Cell, mut right: Cell }
let mut pair = NodePair.{ left: Cell.{ count: 10 }, right: Cell.{ count: 20 } }
pair.left.count += 1
let ref .{ left: v_left, right: v_right } = pair
assert(v_left.count == 11 && v_right.count == 20)
```

### Type Declarations and Opaque Types

```ebnf
TypeDecl         ::= [ "pub" ] [ "halt" ] "type" PascalCase [ GenericParams ] [ WhereClause ] "=" TypeExpression
OpaqueTypeDecl   ::= [ "pub" ] "opaque" "type" PascalCase [ GenericParams ] [ WhereClause ] "=" TypeExpression
LocalTypeDecl    ::= TypeDecl | OpaqueTypeDecl | NominalDecl | SumTypeDecl
WhereClause      ::= SignatureWhereClause
TypeList         ::= TupleMember { "," TupleMember } [ "," ]
TypeReference    ::= QualifiedName [ GenericArgs ]
```

```ril
-- Transparent Type Declarations:
pub type AccountId = int              -- Direct type alias, transparent across module boundaries
type Point = { x: int, y: int }        -- Local record type alias

-- Cyclic structural type alias rejection (E0313):
-- type BadCyclicA = { following: BadCyclicB }
-- type BadCyclicB = { prev: BadCyclicA } -- Error [E0313]: structural type aliases 'BadCyclicA' and 'BadCyclicB' form a cyclic dependency without nominal or sum indirection

-- Opaque Type Declarations:
-- In file: auth/session.ril

-- Declares a zero-cost opaque type representation over 'str':
pub opaque type SessionToken = str

-- Inside defining file 'auth/session.ril': SessionToken and 'str' are bidirectionally equivalent:
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

-- Inside defining file, underlying operations work natively:
fn validate_token(token: SessionToken) -> bool {
    token == "admin_override"          -- OK: underlying string operations available inside file
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



### External Interface Declarations

External interface declarations are contract-only modules defined in `.d.ril` files, specifying host signatures, opaque nominal types, and exchange contracts without implementation bodies.

```ebnf
DeclUnitItem     ::= [ "pub" ] ( DeclFunction | DeclType | DeclLet | DeclOpaqueType )

DeclFunction     ::= "fn" Identifier [ GenericParams ]
                     "(" [ ParameterList ] ")" [ EffectAnnot ] [ StateAnnot ]
                     [ ReturnType ]
                     [ SignatureWhereClause ]

DeclType         ::= SumTypeDecl | NominalDecl | TypeDecl
DeclOpaqueType   ::= "type" Identifier [ GenericParams ]
DeclLet          ::= "let" Identifier ":" TypeExpression
```

#### Normative Rules for External Interface Modules
- **Body Prohibition Invariant (`E0901`)**: Functions declared in `.d.ril` MUST NOT contain implementation bodies (`{ ... }`). Top-level constants MUST NOT declare initialization expressions (`= expr`). Supplying an implementation body or initializer in a `.d.ril` file is statically rejected under `E0901: BodyInDeclModuleError`.
- **Missing Body Invariant (`E0902`)**: Omitting an implementation body from a function in a standard `.ril` module is statically rejected under `E0902: MissingBodyInStandardModuleError`. External signatures must reside in `.d.ril` modules.
- **Opaque Nominal External Types**: A type declaration in `.d.ril` without a definition body (`pub type DomWindow`) defines an uninterpreted opaque nominal type. Direct field access (`x.field`), bracket indexing (`x[0]`), nominal unwrapping (`inner(x)`), pattern deconstruction, and direct value instantiation are statically rejected under `E0907: ForeignStructuralFieldPenetrationError`.
- **Exchange Contract Types**: Transparent type aliases, records, and tagged sum types MAY provide full shape definitions in `.d.ril` to define exchange data contracts.
- **Top-Level Immutability**: Top-level variables in `.d.ril` are restricted to immutable handles (`let`). Declaring `var` or `let mut` is statically rejected under `E0901`.
- **Dual-Tier `where` Compatibility**: `DeclFunction` supports waist `where` (`SignatureWhereClause`) for aliasing signature callback types; block-level `where` is not permitted in foreign declarations.
- **Hard Safety Membrane Invariant**: Invocations across `.d.ril` external boundaries are strictly sealed against unhandled host faults. External traps or host exceptions never corrupt caller execution state; they resolve either to domain error variants (`Result<T, E>`) or deterministic runtime panics contained at `scope` boundaries.
- **Ordinary Exchange**: Ordinary inputs, outputs, and constants must be scalars or deeply immutable ordinary data with no surviving foreign writer. They cannot contain live `ref` handles, callables, tasks, or resources. This excludes even immutable environment-free function values: only a separate callback parameter receives the temporary callback contract below. An immutable returned graph may share immutable storage; a plain return type does not establish freshness or write permission (`E0528`).
- **Temporary Callbacks**: Invoke only during the current foreign call, on the current task. Preserve actual effects, origins, environment permissions, and exclusivity; mutable invocation requires `mut` on parameter and argument. No environment inspection, retention, return, or cross-task transfer is permitted. Arguments/results must satisfy ordinary exchange or explicit resource contracts; mutable data and nested callables gain no exemption.
- **Listed Resource Contracts (`E0908`)**: Only an explicit resource contract may extend ordinary exchange. Opaque declarations and `@Fiber`/`mut`/`^mut` alone grant no resource mutation, callback retention, copying, closing, or transfer. Reject unsupported requests. Ordinary opaque data retains its actual provenance.
- **Trusted Boundary**: An external entity's conformance to its declared exchange and effect contracts is a trusted premise. Static checking establishes the Ril program's compliance with those contracts, not the truth of an implementation whose body is absent. Diagnostic explanations identify the foreign contract as the origin of such facts; missing authority is never replaced by an assumption of freshness or safety.
- **Termination Boundary**: A bodyless external function is possibly non-terminating, even when its omitted effect/capability rows are closed by the external-declaration contract. Its declaration cannot assert termination or budget coverage; `halt` is not admitted on a bodyless function declaration. A reachable external call prevents ordinary termination certification and is inadmissible within `Div::budget` (`E0822`). Language-defined built-ins follow their normative computation contracts; verified ordinary Ril definitions retain their termination facts across module boundaries.

```ril
-- In file: platform/dom.d.ril

-- Opaque nominal external types:
pub type DomWindow
pub type DomElement

-- Ambient external handle:
pub let WINDOW: DomWindow

-- Transparent contract data types:
pub type QueryOptions = {
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

The DOM contract above admits read-only `DomWindow`/`DomElement` resource descriptors, the `WINDOW` constant, and the two displayed operations. Repeated queries may designate the same external object; a stable descriptor does not make that object immutable. These operations grant no ordinary write authority, clone/transfer permission, or permission to pass a descriptor to another task. Attribute results are ordinary immutable data. Mutation and retained listener registration have no contract in this list.

```ril
-- In file: platform/text.d.ril; default ordinary exchange and temporary callback contracts:
pub fn get_data() -> []int
pub fn transform_text(text: str, transform: Transformer) @{} &{} -> str
where
    type Transformer = fn(str) -> str

-- pub fn edit(mut items: []int) @Fiber &mut -> ()
-- Error [E0908]: no listed contract grants ordinary mutable-data exchange
-- pub fn keep(^mut callback: fn() &up -> ()) &^mut -> ()
-- Error [E0908]: default callback authority cannot be retained
-- pub fn hidden_callback() -> { action: fn() -> () }
-- Error [E0908]: ordinary returned data cannot conceal callable authority
-- pub fn use_writer(callback: fn(mut []int) &mut -> ()) -> ()
-- Error [E0908]: a callback cannot receive a foreign ordinary writer under the default exchange rules
```

```ril
-- Invocation fixture using the preceding Text module:
let data = Text::get_data()            -- Immutable; not necessarily fresh
-- let mut stolen = Text::get_data()  -- Error [E0528]: the foreign return grants no writer
let mut copy = clone(data)
copy !> Array::push(1)
let text = Text::transform_text("hello", \value -> value)
```

The spelling of a function name does not prove retention or any other behavior. A foreign body that secretly retains a temporary callback violates its trusted contract; it is not a behavior established by its declaration or licensed by omitted annotations.

---

## Expressions and Operators

### Expression Grammar

```ebnf
Literal         ::= IntLiteral | FloatLiteral | StringLiteral | RawStringLiteral
                  | ByteStringLiteral | "true" | "false" | "(" ")"
Expression      ::= Literal | QualifiedName [ GenericArgs ] | EffectOperationRef | "(" Expression ")"
                  | TupleExpr | RecordExpr | ArrayExpr | MapExpr | Block
                  | CallExpr | AnonFnExpr | AccessorExpr | MatchExpr
                  | IfExpr | LoopExpr | WhileExpr | ForExpr | ControlTransfer
                  | ResumeExpr | AssignmentExpr | UnaryExpr | BinaryExpr | SharingExpr | ConstructionTransferExpr
                  | MemberExpr | IndexExpr | RangeExpr | IsExpr
                  | Expression "?" | TypeQuoteExpr | "keyof" TypeExpression
UnaryExpr       ::= ( "-" | "!" | "~" ) Expression
ConstructionTransferExpr ::= "new" Expression
BinaryExpr      ::= Expression BinaryOperator Expression
BinaryOperator  ::= "*" | "/" | "%" | "/?" | "%?" | "*%" | "+" | "-" | "+%" | "-%"
                  | "<<" | ">>" | "&" | "^" | "|" | "==" | "!=" | "<" | "<=" | ">" | ">="
                  | "in" | "&&" | "||" | "??" | "|>" | "!>"
MemberExpr      ::= Expression ( "." | "?." ) ( FieldLabel | TupleIndex )
                  | Expression "." "(" Expression ")"
IndexExpr       ::= Expression ( "[" | "?[" ) Expression "]"
```

### Operator Precedence and Associativity

| Level | Operators | Associativity | Description |
| :---: | :--- | :---: | :--- |
| **1** | `.` `?.` `?[` `[]` `()` `::` postfix `?` | Left | Member access, safe navigation, indexing, invocation, postfix `?`; a type quote is a primary operand |
| **2** | `-` `!` `~` `typeof` `^mut` | Unary Prefix | Arithmetic negation, logical NOT, bitwise NOT, static type introspection, explicit local writable sharing |
| **3** | `*` `/` `%` `/?` `%?` `*%` | Left | Multiplication, division, remainder, safe division/remainder, wrapping mul |
| **4** | `+` `-` `+%` `-%` | Left | Addition, subtraction, wrapping add/sub |
| **5** | `<<` `>>` | Left | Bitwise shift left, bitwise shift right |
| **6** | `&` | Left | Bitwise AND |
| **7** | `^` | Left | Bitwise XOR |
| **8** | `\|` | Left | Bitwise OR |
| **9** | `..` `..=` | Non-associative | Half-open range, closed range |
| **10** | `==` `!=` `<` `<=` `>` `>=` `is` `in` | Non-associative | Relational, equality, pattern match `is`, containment `in` |
| **11** | `&&` | Left | Logical AND (short-circuiting) |
| **12** | `\|\|` | Left | Logical OR (short-circuiting) |
| **13** | `??` | Right | Fallback coalescing operator |
| **14** | `\|>` `!>` | Left | Linear pipeline `\|>`, mutating pipeline `!>` |
| **15** | `let ... else` | Non-associative | Guarded destructuring binding |
| **16** | `=` `+=` `-=` `*=` `/=` `%=` `+%=` `-%=` `*%=` `&=` `\|=` `^=` `<<=` `>>=` | Non-associative | Assignment and compound assignment |
| **17** | `where` | Non-associative | Block-level trailing hoisted declaration clause |

### Arithmetic and Wrapping Operators

```ril
let a = 10 + 20                        -- 30
let b = 100 - 45                       -- 55
let c = 6 * 7                          -- 42
let d = 10 / 3                         -- 3 (integer division)
let e = 10 % 3                         -- 1 (remainder)

-- Standard division/remainder panics on division by zero:
-- let bad_div = 10 / 0                -- Panics: division by zero

-- Safe division and remainder: evaluate to Option<T> instead of panicking:
let safe_div_ok = 10 /? 2              -- Some(5)
let safe_div_zero = 10 /? 0            -- None (safe division by zero)
let safe_rem_ok = 10 %? 3              -- Some(1)
let safe_rem_zero = 10 %? 0            -- None

-- Explicit two's-complement wrapping arithmetic:
let overflow_u8: u8 = 255u8 +% 1u8     -- 0u8 (wrapping addition)
let underflow_u8: u8 = 0u8 -% 1u8      -- 255u8 (wrapping subtraction)
let wrap_mul: u8 = 128u8 *% 2u8        -- 0u8 (wrapping multiplication)
```


| Integer operation | Rule |
| :--- | :--- |
| Signed `/`, `%` | Quotient truncates toward zero; nonzero remainder has the dividend's sign; `a = (a / b) * b + a % b` |
| Checked fixed-width arithmetic | Panic on an unrepresentable result, including negation and `MIN / -1`; `MIN % -1` is zero |
| Safe division/remainder | `None` for a zero divisor or invalid result |
| Wrapping arithmetic | Fixed-width integers only (`E0327` otherwise); reduce modulo their representation |
| Fixed-width shifts | Panic for count < 0 or >= bit width; left discards high bits, signed right extends sign, unsigned right is logical |
| `bigint` | No arithmetic overflow; negative shift counts panic; bitwise operations use unbounded two's complement |

| Floating-point property | Rule |
| :--- | :--- |
| Precision | IEEE 754 widths; round each operation to nearest, ties to even; no implicit fusion |
| Special values | Preserve subnormals and signed zero; every NaN result uses the canonical quiet-NaN bits below |
| Overflow / division by zero | Infinity or NaN, without panic |
| Decimal literals | Round once to the contextual floating type |
| Safe division/remainder | `None` for a zero divisor; otherwise retain the IEEE result |
| Remainder | Truncating remainder |

The pointer-sized `int` has target-dependent range; fixed-width guarantees do not fix its overflow boundary.

| Floating type | Canonical NaN bits |
| :--- | :--- |
| `f32` | `0x7fc00000` |
| `f64` | `0x7ff8000000000000` |

Arithmetic, unary operations, conversions, and binary decoding/encoding use these same positive-sign NaN patterns. NaN sign and payload from an input are not preserved. These bit rules do not change NaN equality or ordering.

### Bitwise and Shift Operators

```ril
-- let text_sum = "a" + "b"           -- Error [E0327]: arithmetic does not concatenate strings
-- let wrapped_float = 1.0 +% 2.0     -- Error [E0327]: wrapping arithmetic requires fixed-width integers
let left = "a"
let right = "b"
let text = "{left}{right}"            -- OK: interpolation
```

An operator applied to a type for which that operation is not defined is `E0327`, including unsupported equality constituents and ordering operands. Different otherwise admissible operand types still use `E0301`; there is no implicit numeric promotion. Boolean conditions and logical operands use the more specific `E0350`.

```ril
let and_val = 0b1100 & 0b1010          -- 0b1000 (8)
let or_val  = 0b1100 | 0b1010          -- 0b1110 (14)
let xor_val = 0b1100 ^ 0b1010          -- 0b0110 (6)
let not_val = ~0b1100                  -- Bitwise NOT
let shl_val = 1 << 4                   -- 16
let shr_val = 64 >> 2                  -- 16
```

### Relational, Equality, and Containment Operators

```ril
let eq = (10 == 10)                    -- true
let ne = (10 != 20)                    -- true
let lt = (5 < 10)                      -- true
let lte = (10 <= 10)                   -- true
let gt = (20 > 10)                     -- true
let gte = (20 >= 20)                   -- true

-- Containment check via 'in':
let in_array = 3 in [1, 2, 3]          -- true
let in_range = 5 in 1..=10             -- true
let in_map   = "key" in user_map       -- true (checks key containment)
let in_set   = 42 in visited_set       -- true

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
ordered !> Map::set("b", 3)
let snapshot = clone(ref ordered)
assert(Map::keys(snapshot) == ["b", "a"]) -- Replacing a value preserves its key's position
-- let bad_keys: [f64: int] = [nan: 1] -- Error [E0328]: floating-point keys are not admitted
-- let graph_key = [.{ id: 1 }: 0]    -- Error [E0328]: immutable records are still reference-type keys
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

For finite cyclic graphs, equality is the greatest binary relation satisfying these structural rules; allocation identity and sharing count are irrelevant. Comparison terminates without user code or overlapping writes; provenance and exclusivity still govern reads.

| Map key / set element type | Eligibility |
| :--- | :--- |
| `bool`, integers including `bigint`, `str`, `bytes`, `()` | Allowed |
| Nominal / ordinary opaque wrappers | Allowed when recursively preserving one of those value representations |
| Floats, reference graphs (including immutable ones), callables, resources | `E0328` |

Eligibility depends on the concrete type, not equality support alone. Keys are copied by value: source reassignment cannot change them. No freezing, graph cloning, or user equality/order/hash callbacks occur.

| Collection operation | Order |
| :--- | :--- |
| Array iteration | Increasing index |
| Map/set iteration; `Map::keys`/`values` | First insertion |
| Replace map value / reinsert present set member | Keep position |
| Remove, then insert | Append |
| Duplicate map literal key | Last value, first position; operands still evaluate left-to-right |

#### Value Tests with is

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
let mut mark = \n -> { trace !> Array::push(n); n }
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
IsAlternative   ::= "_" | IsConstructor | IsTuple | IsRecord | RangePattern | IsValueExpr
IsConstructor   ::= QualifiedName [ "(" [ IsTestList ] ")" ]
IsTestList      ::= IsTest { "," IsTest } [ "," ]
IsTuple         ::= "(" ")" | "(" IsTest "," IsTest { "," IsTest } [ "," ] ")"
IsRecord        ::= [ TypeReference ] ".{" [ IsField { "," IsField } [ "," ] ] "}"
IsField         ::= FieldLabel [ ":" IsTest ]
IsValueExpr     ::= Expression
```

| Form / boundary | Meaning |
| :--- | :--- |
| Resolved constructor head | Structural test; tag first, then payload. Ordinary callable heads are value expressions. Constructor arity, tuple equivalence and opacity rules apply |
| Existing name / other expression | Evaluate and compare with `==`; E0301/E0305 for incompatible types, E0327 for unsupported equality. No binders or binding modifiers |
| Tuple / record test | Test components / listed known fields in written order; omitted record fields are unconstrained. Shorthand `.{ field }` means `.{ field: field }`, reading the outer name |
| Arrays / maps | Ordinary value expressions, including their normal evaluation order; no array-pattern rest or wildcard syntax is added |
| `_` / literal range / `\|` | Ignore constituent / existing integer range-pattern rules / try alternatives left-to-right until one succeeds |
| Parse boundary | Structural test forms take precedence over value expressions. A parenthesized single expression selects whole-value equality; tuples keep their structural form. At test level `\|` separates alternatives; use `(a \| b)` for bitwise OR |
| Outer operators | Undelimited value expressions bind more tightly than `is`; `&&`, `\|\|`, and lower-precedence operators follow the completed test. Parentheses or argument/field delimiters admit a full value expression |
| Execution | Evaluate subject once. At each reached leaf, obtain that constituent, evaluate the expected expression once, then compare. Shape/tag mismatch or an earlier failed component skips later tests; no snapshot or rollback |
| Static checks | Check every test's names, types, modes and ordinary effects/state, including potentially skipped expressions. Expressions inherit ordinary phase, provenance and exclusivity rules |
| Removed / binding syntax | A trailing `if` or a binding modifier in a test is E0120. Binding patterns and guards remain available in `match` |
| Flow / Results | Preserve only refinements still valid after expected-expression evaluation. Constructor tests inspect the reached Result tags; wildcard and value-equality tests alone do not discharge an outstanding Result |

```ril
let number = 3
assert(number is 1 + 2)
assert(number is 1 | 3)               -- Alternatives
assert(number is (1 | 2))             -- One expected value: bitwise OR
assert(number is 3 && number > 0)     -- Logical continuation outside the test
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
RangeExpr       ::= [ Expression ] ( ".." | "..=" ) [ Expression ]
```

```ril
let r1 = 0..5                          -- Half-open range [0, 5)
let r2 = 0..=5                         -- Closed range [0, 5]

type IntRange = typeof (0..0)
let reversed: IntRange = 5..1
assert(!(3 in reversed))              -- Reversed ranges are empty
var visited = 0
for 254u8..=255u8 as value {
    assert(value >= 254u8)
    visited += 1
}
assert(visited == 2)                  -- No increment beyond u8's maximum

let arr = [10, 20, 30, 40, 50]
let sub: []int = arr[1..4]            -- New ordinary array containing [20, 30, 40]
let prefix = arr[..3]                 -- [10, 20, 30]
let suffix = arr[2..]                 -- [30, 40, 50]
let empty = arr[len(arr)..len(arr)]   -- OK: empty array at the end
-- arr[2..1]                          -- Panics: reversed half-open bounds
-- arr[-1..2]                         -- Panics: negative lower bound
-- arr[0..=len(arr)]                  -- Panics: a written inclusive upper bound must index an element
```

| Standalone range | Rule |
| :--- | :--- |
| Endpoints | Same integer type, including `bigint`; ordinary contextual literal typing applies |
| Non-integer / mismatched endpoint types | `E0327` / `E0301` |
| Evaluation | Evaluate lower then upper once; retain both values and the inclusive/exclusive flag |
| Value type | Immutable, copy-by-value integer range of the endpoint type; both spellings have the same type |
| Public shape | Nameable via `typeof`; no product projections, mutable authority, or additional prelude name |
| `lower > upper` | Empty for either spelling |
| Equal endpoints | Half-open: empty; inclusive: one element |
| Iteration | Ascending by one; stop after the last included value without an overflowing extra increment |
| `value in range` | Value has the endpoint type; test the selected bounds, without iterating |
| Other operations | Equality as specified above; no ordering, indexing, `len`, or map-key eligibility |

Ranges are finite even when their integer cardinality exceeds `int`. Their value representation does not allocate one element per member. Range indexing instead uses `int` endpoints (`E0301` for another type) and the bounds below; reversed bounds panic.

```ril
-- 1. Value elements are cloned (copied by value):
let mut source: []int = [1, 2, 3]
let sub: []int = source[0..2]         -- New ordinary array containing [1, 2]
source !> Array::push(4)              -- Modifying source length does not affect sub
source[0] = 99
assert(sub[0] == 1)                   -- Scalar value was cloned; sub is unaffected!
assert(len(ref source) == 4 && len(sub) == 2)

-- 2. Reference elements are NOT cloned (references shallow-copied):
type Cell = { var count: int }
let mut cells: []Cell = [Cell.{ count: 1 }, Cell.{ count: 2 }]
cells[1].count += 1
let ^mut sub_cells = cells[0..1]      -- OK: '^mut' acknowledges duplicated writable paths
sub_cells[0].count = 42
assert(cells[0].count == 42)          -- Reference NOT cloned: points to same heap Cell!
sub_cells[0] = Cell.{ count: 9 }
sub_cells !> Array::push(Cell.{ count: 10 })
assert(cells[0].count == 42 && len(ref cells) == 2) -- Slots and length are independent
-- let mut bad = cells[0..1]          -- Error [E0510]: new local writable alias needs '^mut'

-- 3. Whole-array observation vs new array:
let ref observer = source            -- Read-only ref directly over pinned mutable array
-- source !> Array::push(5)           -- Error [E0537]: observer is used below
assert(observer[0] == 99)
-- observer[0] = 9                    -- Error [E0520]: a ref grants no write authority
-- let ref bad_new = source[0..2]    -- Error [E0543]: new array cannot bind to ref
-- let ref bad_all = source[..]      -- Error [E0543]: new array cannot bind to ref
source !> Array::push(5)              -- OK: observer's last use has ended
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

let b: bytes = b"RIFF\x00\x01"
let b_sub: bytes = b[0..4]            -- b"RIFF" (byte sub-sequence)
-- let ref b_ref = b                -- Error [E0402]: bytes is an immutable value type
let mut byte_array: []u8 = Bytes::to_array(b)
byte_array[0] = 0u8
assert(Bytes::at(b, 0) == Some(82u8)) -- The original bytes still start with 'R'
```

- **Array Result**: Allocate ordinary `[]T` with independent slots and length. Clone value elements; preserve reference identities, aliases, and permissions. Tuples and other heap products are references. Freshness is provenance, not a type qualifier.
- **Writable Sharing (`E0510`)**: Mark reception of duplicated writable reference paths with `^mut`.
- **`ref` Target (`E0543`)**: A fresh range result cannot bind directly to a persistent `ref`. Publish it immutable through `let` or an ordinary parameter, or receive it with a lawful `let mut` binding; a later `ref` observes that established origin. Forwarding preserves whether publication actually occurred.
- **Bounds**: For length N, a half-open range requires `0 <= lower <= upper <= N`; equal bounds produce an empty array, including at N. Omitted lower bounds mean zero; an omitted upper bound denotes the exclusive end N. A written inclusive upper bound h requires `0 <= lower <= h < N` and selects through h. Negative, reversed, or out-of-range bounds panic; bounds are never clamped. Safe range lookup (`arr?[a..b]`) returns `?[]T` (`None` when out of bounds).
- **Primitive Sub-Sequences**:
  - `str[a..b]` and `str[a..=b]` evaluate to an independent `str` based on Unicode scalar (code point) indices ($0 \le a \le b \le \text{scalar\_len}$). Range indexing and string length share the same Unicode scalar coordinate system; `s[0..len(s)]` safely selects the entire text.
  - `bytes[a..b]` and `bytes[a..=b]` evaluate to an independent `bytes` byte sub-sequence ($0 \le a \le b \le \text{byte\_len}$).
- **Array Stability**: Structural mutation is `E0526` during iteration or `E0537` before the last possible use of any derived `ref`/observer environment. Nonoverlapping element writes remain allowed.

### Pipeline Operators

- **Linear Pipeline (`|>`)**: Passes the left expression as the first argument to the right callable: `x |> f` desugars to `f(x)`.
- **Mutating Pipeline (`!>`)**: Passes the mutable left lvalue to the right mutating callable: `x !> f` desugars to `f(mut x)`. It never supplies `^mut` implicitly.
- Neither pipeline supplies `ref`; an observing first parameter uses an explicit call such as `f(ref source, ...)`.
- **Call Form and Propagation**: `x |> f(a)` means `f(x, a)`; `x !> f(a)` means `f(mut x, a)`. Evaluation follows source order: the left operand, the right callee expression, then written right arguments in written order. Each expression evaluates once; an abrupt exit prevents the remaining expressions and the call. Thus `left() |> computed()(arg())` evaluates `left()`, then `computed()`, then `arg()`, before invoking the selected callable. This also applies to mutating pipelines. Trailing closures supply the final argument. Postfix `?` keeps its ordinary precedence: use `(x !> f(a))?` to propagate the whole pipeline result.

```ril
let doubled = [1, 2, 3]
    |> Array::map(\x -> x * 2)
    |> Array::filter(\x -> x > 2)      -- Evaluates to [4, 6]

let mut items = [1, 2, 3]
items !> Array::push(4)                -- In-place mutation: items is now [1, 2, 3, 4]
```

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
let recovered = res ?? \err -> 0       -- 0: Result fallback MUST consume the error
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
| `Option<T> ?? rhs` | Unwrap T; skip rhs | Evaluate rhs as T; never auto-invoke a supplier |
| `Result<T, E> ?? handler` | Unwrap T; skip handler | Evaluate and invoke `fn(E) @& -> T` once, preserving actual obligations and handle permissions; raw T is `E0711` |

`?` outside a function/closure is `E0205`, including module initializers. It performs no Option/Result or error conversion; payload provenance, permissions, and nested inspection duties survive.

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
let optional_record: ?{ name: str } = Some(record)
let safe_name = optional_record?.name -- OK
```

Inside a callable, a postfix `?` operand other than `Option` or `Result` is `E0712`. A valid operand whose failure cannot be returned by the enclosing callable is `E0713`, including an incompatible Result error type. A `??` left operand outside those two families is `E0714`; a raw-value Result fallback retains `E0711`, and incompatible fallback value/callable types use `E0301`. Safe field access on a non-optional receiver is `E0715`; safe element lookup also admits ordinary collections as specified below, and unsupported lookup receivers use `E0352`.

`??` evaluates its left operand once. Callback effects/permissions remain checked. Direct outward `return`/`last`/`next` is `E0710`; a return inside a nested callable stays local to it.

| Safe access | Rule |
| :--- | :--- |
| `?.` | Field projection from an optional receiver |
| `?[` | Array/map element lookup, also through an optional receiver |
| `None` receiver | Return `None`; skip access and index evaluation |
| Missing key / out-of-bounds element | Return `None` |
| Selected U / selected `Option<U>` | `Some(value)` / unchanged Option; no further flattening |
| Range index | Use ordinary range indexing syntax and bounds rules |

### Record Construction and Functional Update

```ebnf
RecordExpr      ::= [ TypeReference ] ".{" [ RecordValueField { "," RecordValueField } [ "," ] ] "}"
RecordValueField ::= [ MemberMode ] FieldLabel [ ":" Expression ] | ".." Expression
```

Explicit fields override equally named fields from a value spread, independent of written position. Multiple explicit definitions are `E0210`; conflicting spreads without an override are `E0211`. Spreads preserve member schemas, references, and actual permissions. A typed constructor inherits omitted modes; an untyped explicit field defaults to immutable. Neither spreading nor a written mode upgrades a stored source.

```ril
let left = .{ id: 1 }
let right = .{ id: 2 }
-- let duplicate = .{ id: 1, id: 2 }  -- Error [E0210]: two explicit definitions
-- let conflict = .{ ..left, ..right } -- Error [E0211]: both spreads supply id
let chosen = .{ ..left, ..right, id: 3 } -- OK: explicit override resolves the conflict
let mapping = ["id": 1, "id": 2]     -- OK: duplicate map keys retain the last value
```

```ril
type Point = { x: int, y: int, z: int }

let p1 = Point.{ x: 1, y: 2, z: 3 }
let p2 = Point.{ z: 10, ..p1 }         -- Functional record update: { x: 1, y: 2, z: 10 }
```

### Assignments and Compound Assignments

```ebnf
AssignmentExpr  ::= AssignTarget AssignmentOperator Expression
AssignTarget    ::= QualifiedName | Expression "." ( FieldLabel | TupleIndex | "(" Expression ")" )
                  | Expression "[" Expression "]"
AssignmentOperator ::= "=" | "+=" | "-=" | "*=" | "/=" | "%=" | "+%=" | "-%=" | "*%="
                     | "&=" | "|=" | "^=" | "<<=" | ">>="
```

Assignments require an addressable mutable lvalue target. Assignments are expressions evaluating to `()`.

```ril
-- (1 + 2) = 3                       -- Error [E0503]: expression is not an assignable location
let fixed = 1
-- fixed = 2                         -- Error [E0501]: location exists but binding is immutable
var changing = 1
changing = 2                         -- OK
```

A target that is not an addressable lvalue is `E0503`. Existing locations with insufficient reassignment or interior authority use `E0501`, `E0502`, or `E0520`; missing members and invalid indexing retain their specific diagnostics. Chained assignment retains `E0701`.

Qualified names and static computed fields keep ordinary lvalue permissions. Compound assignment evaluates the location once, then reads, evaluates the RHS, and writes.

```ril
var x = 10
x = 20                                 -- Simple assignment
x += 5                                 -- Compound addition (25)
x -= 2                                 -- Compound subtraction (23)
x *= 2                                 -- Compound multiplication (46)
x /= 2                                 -- Compound division (23)
x %= 5                                 -- Compound remainder (3)

-- Compound wrapping arithmetic:
var byte_val: u8 = 250u8
byte_val +%= 10u8                      -- 4u8 (compound wrapping addition)
byte_val -%= 10u8                      -- 250u8 (compound wrapping subtraction)
byte_val *%= 2u8                       -- 244u8 (compound wrapping multiplication)

-- Compound bitwise assignments:
var flags = 0b0011
flags |= 0b1100                        -- 0b1111
flags &= 0b1010                        -- 0b1010
flags ^= 0b0011                        -- 0b1001
flags <<= 1                            -- 0b10010
flags >>= 2                            -- 0b00100

-- Pinned handles (let mut) permit field assignment but reject handle reassignment:
type Buffer = { var capacity: int }
let mut pinned_buf = Buffer.{ capacity: 16 }
pinned_buf.capacity = 32               -- OK: field assignment through pinned handle
pinned_buf.("capacity") += 1           -- OK: same field permissions
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
   - Declarations (`fn`, `type`, `eff`) MUST NOT appear in `StatementSequence` (`E0703`).
   - Variable bindings (`let`, `let mut`, `var`) MUST NOT appear in `where` clauses (`E0702`).
- **Local Effect Discharge (`E0618`)**:
   - Any local `eff` declared in `BlockWhereClause` MUST be completely discharged via an in-scope `with` handler within the enclosing block frame.
   - Local effects MUST NOT appear in outer `@Effect` annotations or escape into unhandled closures.
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

| Built-in source | Element and traversal order |
| :--- | :--- |
| `[]T` | T, increasing element index |
| `[K: V]` | (K, V), first-insertion order |
| `Set<T>` | T, first-insertion order |
| Integer range | Endpoint type, ascending bounds as specified for ranges |
| Other values, including strings, bytes, and iterator Source records | No implicit iteration (`E0355`); use explicit conversion or operations |

Evaluate the source once. Read each entry when visited; later element replacement may be observed, but structural mutation during traversal is `E0526`. Default element bindings require immutable data (`E0535`); use an explicit `ref` pattern for live reference observation. Destructuring cannot grant missing writers (`E0521`); independent scalar `var` copies remain permitted. Source identities and lifetime restrictions survive every pattern.

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

`let Pattern = expr else { Block }` matches a refutable pattern or diverges.

```ril
fn unwrap_or_zero(value: ?int) -> int {
    -- let Some(x) = value             -- Error [E0345]: refutable binding needs else
    let Some(x) = value else { return 0 }
    x
}
```

Without `else`, patterns must be irrefutable under the initializer's static type/refinement (`E0345`), including mutable/destructuring bindings. A single-variant constructor may qualify. Guarded names exist after success, not in the failure block.

- **Divergence Invariant**: The `else` block MUST diverge (evaluate to `never`).
- **Non-Vacuous Binding (`E0309`)**: Every ordinary or guarded `let` must bind a variable, except unguarded `let _ = expr`. Nullary patterns, unit patterns, and guarded wildcard discards are rejected. Binding-free tests use `?`, `is`, or `match`.

```ril
fn process_account(data: [str: str]) -> Result<str, str> {
    -- The 'else' block MUST diverge (evaluate to 'never') and MUST bind >= 1 variable:
    let Some(id) = data?["account_id"] else {
        return Err("missing account_id") -- OK: diverges via 'return', binds variable 'id'
    }
    let Some(user) = fetch_user(id)? else {
        return Err("missing user")     -- OK: propagates error via '?' or diverges via 'return'
    }

    -- Non-diverging 'else' is statically rejected:
    -- let Some(name) = data?["name"] else {
    --     println("name missing")     -- Error [E0321]: 'else' branch of 'let ... else' must diverge
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

-- Divergence via 'next' and 'last' inside loops:
for records as entry {
    let Ok(val) = parse_entry(entry) else {
        next                           -- OK: diverges out of this iteration, binds variable 'val'
    }
    process(val)
}

loop {
    let Some(work) = active(runtime)? else {
        last                           -- OK: propagates error via '?' or diverges via 'last'
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
                     | TuplePattern | ArrayPattern | RecordPattern | ConstructorPattern | RangePattern | TypePattern
BindingModifier    ::= MemberMode
VariablePattern    ::= [ BindingModifier ] Identifier
ConstructorPattern ::= QualifiedName [ "(" [ PatternList ] ")" ]
PatternList        ::= Pattern { "," Pattern } [ "," ]
TuplePattern       ::= "(" [ TuplePatternElement { "," TuplePatternElement } [ "," ] ] ")"
TuplePatternElement ::= Pattern | ".."
ArrayPattern       ::= "[" [ ArrayPatternElement { "," ArrayPatternElement } [ "," ] ] "]"
ArrayPatternElement ::= Pattern | ".." [ Identifier ]
RecordPattern      ::= [ TypeReference ] ".{" [ RecordPatternField { "," RecordPatternField } [ "," ] ] "}"
RecordPatternField ::= [ BindingModifier ] FieldLabel [ ":" Pattern ] | ".." [ Identifier ]
NumericPattern  ::= [ "-" ] ( IntLiteral | FloatLiteral )
LiteralPattern  ::= Literal | NumericPattern
WildcardPattern ::= "_"
RangePattern    ::= NumericPattern ( ".." | "..=" ) NumericPattern
```

Matches are evaluated top-to-bottom and must be exhaustive (`E0303`). A trailing guard belongs to the whole or-pattern, not just its last alternative. Every alternative binds the same identifiers with compatible types and modes (`E0346`); within one alternative each identifier is bound at most once (`E0347`). Each tuple, array or record pattern permits at most one immediate rest (`E0347`); nested patterns count their rests independently. Thus `([a, ..xs], [b, ..ys])` is valid. A guard cannot establish exhaustiveness. Pattern/subject incompatibility uses `E0301`; incompatible result types across otherwise valid reachable arms use `E0351`.

These binding patterns govern `match`, bindings, `if let` / `while let`, iteration and handler parameters. The nonbinding [is value tests](#value-tests-with-is) have their own grammar and admit expected-value expressions.

`TypePattern` is the exception: it is admitted only in static `match` arms against token subjects/constituents (`E0306` for another pattern context). It does not introduce type binders through ordinary `let`, iteration, or handler patterns. Run-time token subjects remain `E0816`.

A tuple or array pattern without a rest requires exactly its written number of elements. With a rest, its subject must contain at least the number of non-rest elements; prefix and suffix patterns select from their corresponding ends, and the rest may be empty. Tuple rests are anonymous. Named array rests use the range-indexing copy rules and ordinary array extent, permission, publication, and sharing checks.

```ril
let mut values = [1, 2, 3]
let ref observed = values
let [_, ..tail] = observed             -- New ordinary array; value elements cloned
values[1] = 9
values !> Array::push(4)
assert(tail == [2, 3])                 -- Independent slots and length
-- let ref [_, ..bad] = values       -- Error [E0543]: the named rest allocates a new array
```

```ril
type Choice { Left(int), Right(int) }
fn invalid_alternative(value: Choice) -> int {
    -- match value { Left(x) | Right(y) -> 0 } -- Error [E0346]: different binding names
    match value { Left(x) | Right(x) -> x }    -- OK: same binding contract
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

`E0345` applies when a binding, `for` element pattern, or handler parameter requires an irrefutable pattern but the pattern may fail. It is distinct from a nonexhaustive `match` (`E0303`). Reversed or non-integer numeric range patterns use `E0348`; a valid empty half-open range still follows ordinary coverage/reachability rules. Repeated identifiers across alternatives are not duplicate binders. Arbitrary computed expressions in a literal-pattern position use `E0349`.

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

Numeric patterns use the scrutinee's numeric type and the same representability rules as numeric expressions. Range patterns require integer endpoints of that type with `lower <= upper`; an equal-bound closed range matches one value and an equal-bound half-open range matches none. Arbitrary computed expressions are not literal patterns (`E0349`); a non-integer or reversed range pattern is `E0348`.

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

### Flow-Sensitive Type Narrowing

Flow-sensitive type narrowing refines the static type of existing bindings in-place across conditional branches, guard clauses, and loops without introducing new variable bindings.

```ebnf
NarrowingTarget    ::= Identifier | NarrowingFieldPath
NarrowingFieldPath ::= Identifier "." Identifier [ "." Identifier [ "." Identifier ] ]
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
- **Zero-Binding Refinement**: Narrowing refines existing bindings in-place across conditional branches without introducing new variable bindings (contrasting with `match`, `if let`, and `let ... else` which introduce new bindings).
- **Non-Binding Predicates**: `x is Variant(expected)` reads an existing expected value; an unresolved name is `E0204`. Use `match` or guarded bindings to introduce payload variables. `is` has no trailing guard.
- **Value-Test Refinement**: A successful constructor test refines the tested stable path to that variant. Failure excludes the variant only when the payload test covers every payload (for example, a bare tag or all wildcards); a failed value comparison alone excludes no variant. Alternatives join their proven facts. Expected-expression writes invalidate affected facts (`E0310`, or `E0533` for unproved independence); completing the test does not restore them.
- **Payload Projection ($S|_V$)**: Testing `x is V` refines sum type $S$ to variant $S|_V$ ([Sum Types and GADTs](#sum-types-and-gadts)):
   - $n = 0$: No payload; value projection raises `E0337`.
   - $n = 1$: Projected via `.0` (`p.0`). `?T != None` directly unboxes to `T`.
   - $n \ge 2$: Projected via positional tuple indices `.0`, `.1`, ..., `.(n-1)`.
   - Record: Projected via declared field names (`x.field`).
- **Stability & Invalidation**:
   - `let`: Permanently narrowed across dominance region.
   - `var` / `var mut`: Slot assignment, including compound assignment, invalidates that slot's narrowing (`E0310`). Interior writes through `var mut`, including `!>` calls, invalidate overlapping facts according to their actual write origins; `!>` does not reassign the slot.
   - `let mut`: Tag identity is pinned (`E0502`); writes through `var` or writable members invalidate overlapping facts.
- **Transitive Latent Havoc**: Invoking a callable whose effective writes reach v, through a global or captured group, a contract reference, a callback, or an active handler, resets the affected refinement to $T_{\text{root}}$. Group spelling does not change the actual write origin.
- **Anti-Aliasing (`E0533`)**: Preserving a live-origin refinement across a call requires proof that the call's possible writes are independent of that origin. Unknown overlap uses `E0533`; a known write invalidating an established refinement uses `E0310`. A `ref` does not supply independence. The examples below contrast both failures with an immutable snapshot.
- **Generic Confinement**:
   - Testing bare type parameters (`x is T`) is rejected (`E0301`).
   - GADT equations on $x$ are local to $x$ and do not rebind $T$ elsewhere in scope.
   - Mutable fields preserve container invariance ([Type Identity and Subtyping](#type-identity-and-subtyping)).
- **Dead Paths & Phase Ordering**:
   - Divergent branches (`never`) are pruned from joins ($\Gamma \sqcup \bot = \Gamma$).
   - A narrowing predicate contradictory to an already active refinement is `E0311`. An ordinary constant-false condition is instead an inactive branch; it does not by itself produce this diagnostic.
   - Dead-path pruning precedes Definite Mutation analysis (`E0527`); writes in dead paths do not count as reachable mutations.
- **Bounded Analysis**:
    - **Path Bound**: Field paths are tracked through at most three projections after the root (`a.b.c.d`); deeper paths default to $T_{\text{root}}$.
    - **Loop Widening**: Unconverged loop variables widen to $T_{\text{root}}$ after $K = 3$ iterations.

```ril
type Cell = { var value: ?int }

-- E0533: the callback's possible writes are not known to be independent.
-- An explicitly open capability row preserves actual obligations; a bare fn() -> () is closed and pure.
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
type User = { id: int, name: str }

fn process_user(u: ?User) -> str {
    if u != None {
        u.name                                 -- OK: 'u' narrowed to User; direct field access
    } else {
        "Anonymous"
    }
}

-- Guard clause with early divergent return:
fn fetch_id(u: ?User) -> int {
    if u == None {
        return -1                              -- Diverges (never); pruned from join
    }
    u.id                                       -- OK: sequential flow inherits User
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
type Account = { id: int, details: ?{ balance: int } }

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
    --     unused = Some(20)                  -- Write in statically unreachable branch does not satisfy Definite Mutation Invariant
    -- }
}

-- Path depth bound (depth <= 3 tracked; depth > 3 requires local 'let' anchor):
fn test_bounded_path_depth(root: { a: ?{ b: ?{ c: ?{ d: int } } } }) -> () {
    if (root.a != None) && (root.a.b != None) && (root.a.b.c != None) {
        let c_node = root.a.b.c                -- OK: path depth 3 (root.a.b.c) tracked
        let d_val = c_node.d                   -- OK: access deeper fields through local anchor
    }
}
```

---

## Functions, Closures, and Callables

### Named Function Declarations and Contrast Matrix

Named functions are declared at module or block scope. They support newspaper ordering (module-wide hoisting) and mutual recursion without forward declarations.

```ebnf
FunctionDecl         ::= [ "pub" ] [ "halt" ] "fn" Identifier [ GenericParams ]
                         "(" [ ParameterList ] ")" [ EffectAnnot ] [ StateAnnot ] [ ReturnType ]
                         [ SignatureWhereClause ] Block
SignatureWhereClause ::= "where" SignatureWhereItem { Separator SignatureWhereItem } [ Separator ]
SignatureWhereItem   ::= LocalTypeDecl
ParameterList        ::= Parameter { "," Parameter } [ "," ]
Parameter            ::= [ ParameterMode ] Identifier [ ":" TypeExpression ] [ "=" Expression ]

Argument             ::= [ Identifier ":" ] ( MutableArgumentMode AssignTarget | "ref" Expression | "new" Expression | Expression )
MutableArgumentMode  ::= "mut" | "^mut"
ArgumentList         ::= Argument { "," Argument } [ "," ]
CallExpr             ::= Expression "(" [ ArgumentList ] ")" [ TrailingClosure ] | Expression TrailingClosure
TrailingClosure      ::= AnonFnExpr
CallableType     ::= "fn" "(" [ ParameterTypeList ] ")" [ CallableContract ] [ ReturnType ]
CallableContract ::= "@&" [ StateAnnot ]
                   | CallableEffectAnnot [ CallableStateAnnot ]
                   | CallableStateAnnot
CallableEffectAnnot ::= EffectAnnot | "@"
CallableStateAnnot  ::= StateAnnot [ "&" ] | "&"
ParameterTypeList::= ParameterTypeItem { "," ParameterTypeItem } [ "," ]
ParameterTypeItem ::= [ ParameterMode ] [ SnakeCase ":" ] TypeExpression
ReturnType       ::= "->" ReturnContract
```

Leading `mut`/`^mut` arguments require assignable targets (`E0410` for `f(^mut clone(x))`); `ref` observes an expression. A parenthesized sharing expression cannot replace a parameter-mode marker (`E0405`). [Fresh storage inputs](#fresh-values-in-storage-calls) receive construction authority before immutable publication; other ordinary parameters require immutable data. Constructors follow their product member and payload contracts.

```ril
type DeferredFactory = fn() -> fn() @Io -> int -- Io belongs to the returned callable
type EffectfulFactory = fn() @Io -> fn() -> int -- Io belongs to the factory
type CapturingFactory = fn() &capture -> new (fn() &up -> int)
```

Arrows associate right. Each effect/state clause belongs to the callable whose parameter list it follows, before that callable's return arrow. Return contracts follow [return construction, permissions, and sources](#return-construction-permissions-and-sources). Executable named definitions must complete missing required result annotations, including `-> ()`, under [mandatory contract completion](#mandatory-contract-inference-and-completion). A callable type or bodyless effect operation may abbreviate a unit result. Anonymous definitions retain the short lambda syntax and require no source type, result, effect, state, or capture annotation completion; the compiler infers their full contracts, and any explicit or contextual constraints are checked against them.

#### Dual-Tier Where Invariants

- **Signature `where` Scope (`SignatureWhereClause`, `E0704`)**:
   - `SignatureWhereClause` is restricted to `LocalTypeDecl` (`type`). Declaring `fn` or `eff` is statically rejected (`E0704`).
   - Types declared in `SignatureWhereClause` are in scope across the function signature and the function body block.
- **Signature Reference Confinement (`E0706`)**:
   - Any type referenced in a function signature MUST be declared in `SignatureWhereClause` or an outer scope. Referencing types declared in `BlockWhereClause` is statically rejected (`E0706`).
- **Downward Isolation (`E0705`)**:
   - Items in `SignatureWhereClause` MUST NOT reference items declared in `BlockWhereClause` (`E0705`). Items in `BlockWhereClause` MAY reference items from `SignatureWhereClause`.
- **Collision Prohibition (`E0203`)**:
   - Declaring an identical identifier in both `SignatureWhereClause` and `BlockWhereClause` of the same function is statically rejected (`E0203`).
- **Exported Type Meaning**:
   - For `pub fn`, structural aliases in `SignatureWhereClause` have the same meaning for importers as their expanded structural types; private helper names are not required at call sites.
- **Generic Constraints and Pipeline Guards in `SignatureWhereClause`**:
   - Pure `type` functions declared in `SignatureWhereClause` are in scope for the generic parameter list and may be referenced as pipeline constraints (`<T |> Guard>`) as well as computed return types, enabling locally encapsulated domain guards without polluting enclosing module namespaces.

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
        out !> Array::push(res)
    }
    Ok(out)
}

-- Prohibited: Declaring 'fn' or 'eff' in SignatureWhereClause (E0704):
-- fn bad_waist_fn(x: int) -> int
-- where
--     fn helper(n: int) -> int { n * 2 }    -- Error [E0704]: 'fn' cannot be declared in signature 'where' clause; place in block 'where' clause
--     eff Yield { emit(int) -> () }         -- Error [E0704]: 'eff' cannot be declared in signature 'where' clause; place in block 'where' clause
-- {
--     helper(x)
-- }

-- Prohibited: Downward reference from waist to block where (E0705):
-- fn bad_downward<T>(item: T) -> Wrapper
-- where
--     type Wrapper = { state: InternalState } -- Error [E0705]: signature 'where' clause cannot reference 'InternalState' declared in inner block 'where' clause
-- {
--     Wrapper.{ state: .{ code: 0 } }
-- where
--     type InternalState = { code: int }
-- }

-- Prohibited: Signature referencing type defined in block where (E0706):
-- fn bad_sig_target(cb: Callback) -> ()      -- Error [E0706]: type 'Callback' used in function signature must be declared in signature 'where' clause, not block 'where' clause
-- {
--     cb()
-- where
--     type Callback = fn() -> ()
-- }

-- Prohibited: Duplicate declaration across waist and block tiers (E0203):
-- fn bad_duplicate(h: Handler) -> ()
-- where
--     type Handler = fn() -> ()
-- {
--     ()
-- where
--     type Handler = fn(int) -> ()           -- Error [E0203]: type 'Handler' is already declared in signature 'where' clause
-- }
```

```ril
-- Hoisted Named Function:
pub fn calculate_tax(amount: int) -> int {
    amount * 20 / 100
}
let r1 = calculate_tax(100)            -- OK: direct call
```

| Aspect | Named Function (`fn`) | Stateless Anonymous Function (`\x -> ...`) | Stateful Anonymous Function (`\x -> ...`) |
| :--- | :--- | :--- | :--- |
| **Hoisting** | Module-wide newspaper ordering | Strictly lexical (definition before use) | Strictly lexical (definition before use) |
| **Environment Capture** | Explicit named origins; block-local values can retain an environment | None (no captured state) | Actual lexical environment, abbreviated in types by `&up` |
| **Type Representation** | Item identity / `fn(P) -> R` | `fn(P) -> R` | `fn(P) &up -> R` |
| **Handle Requirement** | Direct declaration call; stored values follow actual environment permissions | Callable via `let` handle | `let` (immutable), `let ref` (live observer), or writable handle (mutable environment) |

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

- **Definitions**: Infer complete contracts for public, private, module-level, block-local, anonymous, and test functions after lawful handling and local discharge. Named definitions must spell the required concrete state and residual effect obligations, including known obligations inherited from another callable; missing named-function state is `E0510`, and missing named-function effects are `E0612`. Anonymous functions retain the same actual obligations without mandatory source spelling. An omitted annotation never makes an inferred obligation empty.
- **Local Purity**: Mutation of confined local storage, immutable publication of eligible construction results, and call-local environments do not by themselves create outward state obligations. Creating a surviving environment or an additional surviving writer retains the applicable `&capture`, `&^mut`, or named-source obligation. Named definitions spell those obligations; anonymous functions may retain them entirely in their inferred contracts.
- **Callback Dependence**: Obligations that genuinely depend on callable values supplied through formal parameters may be inferred and forwarded symbolically. This includes callable constituents reached through a parameter's fields, elements, projections, or preserved aliases; the dependency remains tied to the actual parameter value. Having such a parameter or returning a callable does not erase unrelated concrete obligations or exempt a named definition from spelling them. A caller supplying a known callable, directly or inside an aggregate, retains the resulting concrete obligations after its own handling and local discharge; a named caller must declare them, and an anonymous caller may leave them to inference.
- **Anonymous Definitions**: Infer the same complete contract, including captures, as for named definitions. Anonymous functions have no mandatory source type, result, effect, state, capture, or returned-source annotation completion. An explicit contextual callable type supplies constraints but is not a prerequisite for a valid inferred anonymous definition. Concrete lexical sources remain identified in the inferred contract even when no source group is written. Explicit annotations must satisfy their declared constraints and cannot erase actual obligations. Latent body operations are obligations of the later invocation; creating a callable does not execute them.

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

type Actions = { run: fn() @& -> () }
fn invoke_field(actions: Actions) -> () { actions.run() }
fn declared_field() &up(sub){mut global_count} -> () { invoke_field(.{ run: tick }) }
-- fn hidden_field() -> () { invoke_field(.{ run: tick }) } -- Error [E0510]: wrapping the known callback does not erase state
```

#### Mandatory Contract Inference and Completion

The compiler MUST infer the full checked contract of every function, including public, private, local, anonymous, and test functions. Named definitions must spell their prescribed annotations in executable source. Anonymous functions retain their short lambda form and have no mandatory source-annotation completion: the complete inferred contract remains available to checking, tooling, callers, and module summaries whether or not the developer chooses to write annotations.

| Inference / completion | Requirement |
| :--- | :--- |
| Inference scope | The same complete analysis for public, private, local, anonymous, and test functions |
| Facts | Types, permissions/history, root and contained origins, aliases, writes, retention, captures, effects, escape/ownership, and callback dependencies |
| Required named source | Parameter types/modes, result contracts, contained dependency groups, and concrete effect/state/capture annotations prescribed for named definitions |
| Anonymous source | Type, result, effect, state, capture, and returned-source contract annotations are optional; absence alone is never `E0544`, `E0510`, or `E0612` |
| Anonymous constraints | Written annotations and contextual callable types constrain the inferred contract; incompatible constraints are rejected by the applicable typing, permission, or callable-matching diagnostic |
| Authority syntax | Parameter/binding modes, argument markers, shared-reception markers, and resource operations retain their existing semantic requirements for every function |
| Shared-reception completion | Prefer `let ^mut` / `var ^mut` for a single identifier's shared initialization; equivalent `mut ... = ^mut expr` remains valid. Assignments, fields, containers, and patterns keep expression markers |
| Root-return normalization | `^mut(x)` covers only root-return retention; actual writes and extra escape paths remain distinct obligations |
| Context and generality | Use body and contextual constraints to infer complete callable contracts, including generic/structural constraints and symbolic callback dependencies; lack of a unique monomorphic signature is not by itself a missing-annotation error |
| Diagnostics | Missing named type/result contract: `E0544`; missing required named state or an independently required reception marker: `E0510`; missing named effect declaration or an actually unhandled effect boundary: `E0612`; argument marker: `E0405`; unresolved required type/static instantiation: `E0344`; invalid written return sources: `E0545` |
| Explanations | Expose complete inferred classifications and origin/propagation chains, including possible sharing, actual anonymous captures, and unproved overlap |
| Interfaces | Preserve fine paths, permission history, store/return relations, and output correlations in semantic summaries; changes invalidate dependent proofs |
| Proof limits | Unknown facts never prove permission, immutability, freshness, separation, or escape. Bodyless foreign declarations remain trusted explicit contracts |

Missing required annotations reject an executable named definition. Anonymous inference and optional source annotation are ordinary compilation behavior, not an abbreviated-fixture mode. Inference and completion cannot silently clone, grant authority, freeze surviving writers, extend lifetimes, consume resources, or reorder evaluation. Independently required authority syntax and safety conditions remain enforced. Immutable sharing and still-symbolic callback/termination facts remain in metadata where no source spelling is prescribed.

`E0344` retains the rules of the construct that requires a determined type or static argument; it is not a fallback error for an anonymous function whose complete inferred contract contains generic or structural constraints. Inference responsibility does not authorize the compiler to select an arbitrary nominal type, invent a run-time representation, or discharge an unresolved safety proof. Required instantiations and explicit constraints must still be validated.

```ril
type Cell = { var count: int }

-- Named-source completion remains mandatory:
-- fn make() { Cell.{ count: 0 } }      -- Error [E0544]: complete as fn make() -> new Cell
-- fn id(x) { x }                      -- Error [E0544]: spell the inferred generic parameter/result contract
fn make() -> new Cell { Cell.{ count: 0 } }
fn inspect(cell: Cell) -> int { cell.count }

-- Anonymous functions need no complete contextual type or source contract:
let identity = \value -> value        -- OK: infer its generic identity contract
let inferred_read = \cell -> cell.count -- OK: retain the inferred structural parameter constraint
let inferred_write = \mut cell: Cell -> { cell.count += 1 } -- OK: inferred &mut; explicit mut grants only its checked authority

-- Explicit contextual types remain available:
let read: fn(cell: Cell) -> int = \cell -> cell.count

eff Log { write(str) -> () }
let logged = \-> Log::write("event") -- OK: infer and preserve Log without a source effect annotation
-- let invalid: fn() -> () = logged  -- Error [E0534]: the explicit closed callable type cannot erase Log
```

#### Closed and Open Callable Rows

Callable types are closed by default at every arrow, independently of whether that arrow receives or returns another callable. A bare `fn() -> ()` therefore admits no residual effects, ambient or captured access, surviving environment creation, or retained writable publication. It is pure in the effect/capability sense; it does not establish termination or finite-budget coverage.

The annotations belong to the callable whose parameter list immediately precedes them, before that callable's result arrow:

```ril
type PureAction = fn() -> ()
type ExplicitPureAction = fn() @{} &{} -> ()
type EffectOpenAction = fn() @ -> ()
type CapabilityOpenAction = fn() & -> ()
type OpenAction = fn() @& -> ()
type LoggedAction = fn() @Log -> ()
type LoggedWithOpenState = fn() @Log & -> ()
type EffectOpenMutator = fn(mut Cell) @ &mut -> ()
type MutatorWithOpenState = fn(mut Cell) &mut & -> ()
```

| Row form on a callable type | Matching requirement |
| :--- | :--- |
| Omitted effects / `@{}` | Closed empty residual effect row |
| Explicit nonempty effects | Closed exact normalized residual effect row |
| Standalone `@` | Open effect dimension; preserve all actual residual effects |
| Omitted capabilities | Closed normalized capabilities supplied by the written clauses and the return contract's implicit baseline |
| Explicit `&{}` | Closed empty total capability row, including the return contract's baseline; incompatible return retention cannot be hidden |
| Explicit nonempty capabilities | Closed exact normalized total capability row, including the return baseline |
| Standalone `&` | Open capability dimension; written capability clauses remain requirements and additional actual obligations are preserved |
| `@&` | The combined spelling of open effects and open capabilities |

Only a whole effect dimension is opened: this version has no partial-effect-row form or source-level effect-row parameter. Capability openness may accompany concrete requirements such as `&mut`, `&up(sub){...}`, `&up{...}`, or `&return{...}`. Opening one dimension leaves the other closed. An open marker is never permission to perform an operation, obtain a writable handle, retain an argument, or erase an actual obligation. An arrow cannot combine open capabilities (`&` or `@&`) with the explicit closed-total assertion `&{}` (`E0547`); use an effect-only `@` when capabilities must remain empty.

Explicit empty rows are admitted on first-order and higher-order callable types and definitions. A named definition may spell an empty row when its completed contract satisfies it; otherwise the applicable contract diagnostic rejects it. Anonymous definitions infer their full contracts without a source-completion obligation, and any explicit annotations are checked against that inference. Named definitions still complete their concrete effect/state/return annotations; symbolic obligations genuinely inherited from callable parameters are inferred and preserved.

Open markers belong only to `CallableType` arrows. A standalone `@`, `&`, or `@&` directly annotating a named or anonymous definition, an effect-operation declaration, or a bodyless foreign declaration is `E0547: InvalidOpenRowPlacementError`; so is placing an open capability marker on the same arrow as `&{}`. An open callable type nested in a definition's parameter, result, or data schema remains valid; it is that nested type's arrow which is open. A bodyless foreign declaration provides a trusted explicit contract and has no implementation from which to infer an open invocation row.

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
-- type ConflictingRows = fn() @& &{} -> ()    -- Error [E0547]: the capability dimension cannot be both open and explicitly closed
```

An explicit `&{}` constrains total capabilities, including root-return retention, capture, inherited access, and contained-dependency obligations. Omission instead retains the return contract's implicit baseline; it is not an instruction to forget that baseline:

```ril
type Cell = { var count: int }
fn retain(^mut cell: Cell) -> ^mut(cell) Cell { cell }
type RootRetainer = fn(^mut value: Cell) -> ^mut(value) Cell
let renamed: RootRetainer = retain              -- OK: source labels are bound by parameter position
-- let erased: fn(^mut x: Cell) &{} -> ^mut(x) Cell = retain
-- Error [E0534]: explicit empty total capabilities conflict with root-return retention
-- let wrong_result: fn(^mut x: Cell) & -> Cell = retain
-- Error [E0534]: an open capability row cannot replace a writable root return with an immutable result
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

Match a callable's complete normalized contract at every assignment, argument, aggregate member, return, and module/type boundary. Closed effect and capability rows use equality, not an upper-bound or subset relation. A callable with fewer obligations also fails a closed row that explicitly requires more. Open rows admit additional actual entries only in their selected dimension; every explicitly written entry must still be satisfied.

Normalization expands effect-set and transparent aliases, compares effect instances using static-argument identity, canonicalizes source and provider identities, combines equivalent access entries, and includes permissions implied by a return contract. Duplicate spellings do not create different contracts. Formal parameter labels and their bound return-source references are alpha-renamed by parameter position before comparison; external and captured sources retain their resolved declaration and activation identities.

Parameter data shapes retain their specified contravariant checks and result data shapes their covariant checks. Parameter modes must match. Independently check root construction/mode/source guarantees and every explicit contained dependency. An open row cannot admit a result whose root is outside the declared source alternatives, turn `ref` into `^mut`, publish live data as immutable, make an existing root `new`, or change a resource or scoped lifetime.

The explicit `&up` callable-type abstraction continues to admit an environment-free callable or the checked abstract environment shape without exposing private capture names. Normalize that declared environment abstraction for matching and preserve the actual captured origins, modes, lifetimes, and correlations in verified metadata. It does not cover additional effects, named global access, independent retained publication, or the current invocation's `&capture` obligation.

| Callable contract component | Rule |
| :--- | :--- |
| Closed effect row | Exact normalized actual effects |
| Closed capability row | Exact normalized actual obligations after the written environment abstraction and implicit return baseline |
| Open effects / capabilities | Preserve the actual complete row; permit additional entries only in the opened dimension |
| Parameter/handle permissions | Unchanged by openness, aliases, or ascription |
| Root returns | Construction, permission, and source guarantees remain independently checked |
| Contained return dependencies | Explicit dependencies must match; open `&` may admit additional actual `&return` facts, all of which continue to propagate |
| Symbolic callback dependencies | Preserve their complete conditions and instantiate them at calls; closure of a destination row checks those conditions rather than erasing them |
| Alternatives | Preserve every possible obligation and only common guarantees under [provenance](#complete-provenance-and-required-annotations). Every retained callable-contract alternative must satisfy a closed equality or an open required entry; a union cannot invent a required entry missing from one alternative |
| Named definitions | Complete concrete source annotations; symbolic parameter-dependent obligations remain in the full verified contract |
| Anonymous definitions | Full inference; no requirement to spell inferred annotations in source |
| Incompatible callable value | `E0534`; parameter-mode mismatches retain `E0407` and other dedicated conditions retain their codes |
| Bodyless foreign declarations | Trusted explicit invocation rows; omitted rows are closed and no termination/coverage guarantee follows |

Fine paths, permission history, relations between input and output regions, and output correlations that have no source spelling remain in verified semantic summaries. Closed matching does not fabricate or discard them. In particular, an open capability row may preserve an unlisted observed/retained constituent of a returned graph, but the receiver still checks that actual constituent before immutable publication, task crossing, further retention, or exclusivity-sensitive access.

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
-- let loses_state: fn() @ -> () = tick          -- Error [E0534]: capabilities remain closed
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

Ascription never drops actual obligations. Passing a callable through an open type and later checking it against a closed type uses its preserved actual contract, not the open spelling alone. Explicit named-function state references on callable types resolve to the provider's verified named projection; they cannot rebind private source identities or substitute for another contract component.

Invoking already shared storage does not itself publish another writer. Actual environment mode determines whether invocation needs a writable or observation handle. Termination and finite-budget-coverage conditions remain independent of both rows and survive every ascription. A default-pure callable may still diverge; an open callable is not a finite or budget-covered callable merely because its operations are handled.

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
    messages !> Array::push(message)
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

### Return Construction, Permissions, and Sources

A value result needs only `-> T`. Reference results distinguish the root from its contained references; all reception checks use the complete graph.

```ebnf
ReturnContract   ::= [ ReturnMode ] TypeExpression
ReturnMode       ::= "new" | ( "ref" | "^mut" ) "(" ReturnSources ")"
ReturnSources    ::= SnakeCase { "|" SnakeCase }
```

Root source names denote formal parameters; field/index paths are retained in metadata. `|` selects possible existing sources, never a newly allocated alternative. Return modifiers are not standalone data types or allocation expressions. The separate `new expression` construction handoff is admitted only at a matching construction argument or a `-> new T` return; it preserves the actual object identity and ends the old construction path.

| Result contract | Checked guarantee |
| :--- | :--- |
| `int`, `str`, `bytes`, other value types | Copy the value; no return-reference source or sharing annotation |
| Plain reference `T` | Deeply immutable; existing immutable storage may be shared |
| `new Cell` | Root constructed during this invocation or handed onward from an eligible `new` parameter, with legal root write authority; true origins and graph permissions remain checked |
| `ref(x) Cell` | Root is an existing object provided by parameter `x`, including a projected child; read-only |
| `^mut(x) Cell` | Same root relation with retained write authority; parameter/argument require `^mut`; root return needs no duplicate `&^mut` |
| `ref(a \| b) Cell`, `^mut(a \| b) Cell` | Root comes from either entry source; does not mean it contains both or that inputs are disjoint |
| `new Holder &return{ref x}` | New root contains an observed dependency on `x` |
| `new Holder &^mut &return{^mut x}` | New root contains a retained writable dependency on `x` |

```ril
type Cell = { var count: int }
type Box = { mut cell: Cell }

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

| Rule | Required check |
| :--- | :--- |
| Value result | Plain `T`; copying a value has no return-reference dependency. Actual writes/effects retain their obligations; named definitions spell required annotations |
| Plain reference result | Deeply immutable graph at return; eligible private construction may be published, but surviving writers cannot be frozen (`E0535`) |
| `new T` | Root created during this invocation, including verified factory calls, or explicitly handed onward from an active `new` parameter, with preserved root write authority (`E0546`). Forwarded construction paths retain their true entry origins and satisfy the fresh-construction handoff rules |
| Constructor syntax | Use the constructor's semantic contract: a zero-cost nominal wrapper does not create a root; a clone preserves its verified isolation |
| `ref(x)` / `^mut(x)` | Root comes from the reference graph supplied by formal `x` at call entry; a child/element still displays only `x` (`E0545`) |
| Source alternatives | Every returned root has a listed entry origin; `a \| b` allows either, excludes fresh roots, and proves no disjointness |
| Existing-root writable return | `^mut(x)` requires a `^mut` parameter and argument; ordinary `mut` cannot escape as writable (`E0528`). A consumed construction input follows its separate `new T` handoff contract, without disguising it as a retained ordinary parameter writer |
| Return dependencies | `&return{ref x, ^mut y}` lists possible contained dependencies; scalar copies and unchanged contents inherited from a root return add no new item |
| State separation | Root-return retention, actual writes, contained retention, other storage, and environment creation are distinct inferred facts |
| Scope | Observation stability, scoped-resource lifetime, task crossing, member permissions, and exclusivity remain checked; annotations extend none of them |

`new` preserves root authority; it does not restore authority lost through `let`, a read-only parameter, or a `ref` path. A locally constructed returned root may already have external aliases. A root forwarded through a `new` parameter instead requires the explicit unpublished-construction handoff, which ends the old formal path. Parameter-origin relations and construction-chain returns retain true entry provenance, not reachability created by writes or a fabricated allocation inside this call.

| Reception | Requirement |
| :--- | :--- |
| `let` / plain `var` | Entire result permits immutable publication; reject possible live dependencies or surviving writers (`E0535`) |
| `let mut` / `var mut` | Receiving paths possess write authority; existing immutable or observed paths never upgrade (`E0528` for returned authority laundering) |
| Shared writable result | Identifier initialization: `let ^mut` / `var ^mut` or equivalent expression marker. Assignment, field/container insertion, or destructuring: explicit `^mut expression` (`E0510` if absent) |
| Persistent `ref` | Established observation origins or a lawful passive observer wrapper; independent allocations remain `E0543` |
| Fresh-storage input | Prove the full unpublished initial-reception contract; the `new` label alone is insufficient |

A reception marker confirms the same returned authority; it is not a second publication. Source annotations never grant absent authority. Compare callable capabilities after combining return retention with explicit invocation bounds. An explicit empty `&{}` closes that combined total; purity checks use the same total.

| Branches | Result contract |
| :--- | :--- |
| All roots constructed here or lawfully handed onward from `new` parameters, and writable | `new T`; require each forwarded branch's explicit handoff and retain every branch's true origins and internal dependencies |
| All roots from non-construction entry parameters | `ref(a \| b) T`, or `^mut(a \| b) T` when every alternative permits writes |
| New root and existing immutable data | Plain `T` after lawful publication |
| New root and entry live reference | No bare mixed-root contract; construct an explicit wrapper or result variant |
| Locally created root published elsewhere, returned writable | `new T` plus the required independent retention/state capability |
| Locally created root published elsewhere, returned only through `ref` | No bare-root contract in this version; use an explicit observer wrapper |
| Existing live root supplied only by a global/capture | No bare-root contract in this version; use a wrapper or an explicit formal parameter. Immutable descriptors/data still use plain `T` |

Verified interfaces retain root permissions/history, contained origins, store/return relations, and correlations between output components. These semantic summaries participate in dependency invalidation. Higher-order/dynamic joins preserve only common guarantees; absent summaries prove no separation. Opaque boundaries may hide names, not safety facts. Return-mode/source erasure is `E0534`; parameter-label renaming also renames bound source names by position.

A generic signature must hold for every admitted instantiation. Unknown `T` is not presumed a reference: use a uniformly valid plain result, sufficient type constraints, or a `new` parameter whose admitted instantiations satisfy the ordinary-reference construction restriction. A forwarding `-> new T` return is valid only for those admitted instantiations and an active explicit handoff. Foreign and resource contracts retain their existing restrictions; return annotations supply no new exchange or resource authority.

```ril
-- Cell and Box have the preceding declarations.
fn wrap(ref box: Box) &return{ref box} -> new { ref item: Cell } {
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
type Holder = { mut item: Cell }
type Slot = { var mut child: Cell }

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
let mut cells: []Cell = []
-- cells !> Array::push(install(mut slot)) -- Error [E0535]: new root is not an unpublished storage input
cells !> Array::push(^mut installed)
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
fn install_observer(mut dst: Slot) &^mut -> new { ref item: Cell } {
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
-- Error [E0534]: the closed capability row cannot erase root-return retention
```

### Termination and halt Contracts

```ril
fn countdown(n: int) -> int {
    if n <= 0 { 0 } else { countdown(n - 1) }
}                                               -- Proven finite without halt
fn spin() -> int { loop {} }                     -- Pure, possibly non-terminating; legal
fn forward_spin() -> int { spin() }              -- Same termination conclusion; no effect declaration needed
halt fn checked(n: int) -> int { countdown(n) }   -- Unmarked finite helpers are admissible
-- halt fn unchecked() -> int { spin() }         -- Error [E0820]: no termination proof
```

Every callable retains a termination judgment independently of its effect and capability rows. `Finite` means its current invocation performs finite computation for all admitted inputs; `MayDiverge` means finite computation has not been established, including a known infinite loop or insufficient evidence. These are specification judgments, not source-level types or annotations. `MayDiverge` does not assert that some input has been proved to diverge.

- **Mandatory Inference**: Apply the same finite-computation rules to ordinary named functions, anonymous functions, and `halt` definitions. Ordinary functions may be `MayDiverge` without any annotation. Neither default purity nor empty-row constraints supply a termination proof. `@Div` denotes only the separate budget-exhaustion effect; writing it neither authorizes nor proves divergence.
- **Finite Outcomes**: Normal return, early return, panic, and a terminating delimited abort count as finite outcomes. `never` describes absence of normal continuation, not infinite execution: a panic may be finite while `loop {}` is not. Finite local computation alone promises no wall-clock bound or external scheduling progress.
- **Invocation Dependencies**: Preserve termination conditions through calls, evaluated parameter defaults, callable arguments and constituents, aliases, branches, handlers, resumption, cleanup, and required child completion. Unknown callable or handler behavior remains a symbolic condition; a concrete invocation is `Finite` only when its required conditions hold. Unknown conditions cannot establish termination. Built-in waits have their stated external-progress premises; arbitrary external functions have no such termination premise.
- **Cycles**: Every possible execution cycle, including indirect callable invocation and handler re-entry, requires finite-descent evidence or a covering finite-evaluation boundary. Mutually dependent conclusions cannot establish one another without that evidence. Proving a loop finite does not prove an unbounded computation inside one iteration finite.
- **Current vs. Latent Computation**: Creating, returning, or storing a callable does not execute its body. Preserve that callable's termination conditions for its later invocation. Creation, capture, and publication still retain their ordinary current-invocation obligations.
- **`halt fn`**: Require `Finite` and empty effective outward effect/capability rows after lawful handling and local discharge, including all admitted parameter-default evaluations. Local mutation, temporary local callable environments, and completely handled local effects are allowed. A called helper need not itself be marked `halt`. A fixed failure of termination is `E0820`; residual effects or capabilities violate `halt` purity (`E0821`). Nonempty outward annotations cannot exempt a `halt` definition from purity. Evaluation of explicit caller-supplied arguments retains its separate caller obligations.
- **Higher-Order Constraints**: A `halt` definition constrains admitted callable arguments wherever their obligations are inferable. An incompatible actual argument is `E0534`. These constraints and actual termination facts cross module and callable-type boundaries; no new callable-type annotation is required. Closing effect/capability rows alone imposes no termination constraint.

```ril
halt fn local_sum(values: []int) -> int {
    var sum = 0
    for values as value { sum += value }
    sum
}                                               -- Local writes discharge; overflow may panic

eff ReadValue { get() -> int }
halt fn local_read() -> int {
    with ReadValue::get() -> resume 7
    ReadValue::get()
}                                               -- Internal handling remains pure and finite
-- halt fn bad_io() @Fiber -> () { Fiber::yield() }     -- Error [E0821]: outward effect

var outside_count = 0
-- halt fn bad_state() &up(sub){mut outside_count} -> () { outside_count += 1 }
-- Error [E0821]: outward capability

fn invoke(action: fn() -> ()) -> () { action() }
halt fn invoke_finite(action: fn() -> ()) -> () { action() }
fn done() -> () {}
fn forever() -> () { loop {} }
invoke(done)                                    -- Finite
-- invoke(forever)                              -- Legal, MayDiverge; not executed in this fixture
invoke_finite(done)                             -- OK
-- invoke_finite(forever)                       -- Error [E0534]: admitted callback must be finite

halt fn make_later() -> (fn() -> int) { spin }   -- Returning an existing callable is finite
-- halt fn run_later() -> int { make_later()() } -- Error [E0820]: its later invocation still diverges
-- halt fn bad_default(value: int = spin()) -> int { value } -- Error [E0820]: default may diverge
```

| Finite-iteration case | Required proof |
| :--- | :--- |
| `for` | Finite collection/range and finite per-element computation |
| `while`/`loop` | Each continuing path makes the next condition false, or advances a counter toward a stable finite bound |
| Counter progression | Nonzero step in a fixed direction; continuation stays on the corresponding side of the bound |
| Equality exit | Initial value and step are known to reach the exit |
| `next` | The same progress obligation as every other continuing path |
| Aliases, callbacks, handlers, other writes | Must not invalidate the counter, bound, or descent facts |
| Arithmetic | Checked overflow is a finite panic; wrapping arithmetic alone proves no descent |

| Recursive case | Required proof |
| :--- | :--- |
| Ordinary or `halt` recursion | Each cycle strictly decreases a nonnegative integer under a lower-bound guard, or takes a proper subpart of a known finite acyclic structure |
| Mutual/indirect recursion | Preserve the same descent relation around every cycle; not every edge must strictly decrease, but no cycle may lack strict decrease |
| Recursive type unfolding or potentially cyclic data | Not structural descent by itself |
| Other calls and handler computation | Retain and discharge their own termination conditions |
| `halt type` helpers | All reached meta/type computation must also be finite, whether or not the helpers are marked `halt` |

```ril
fn even(n: int) -> bool { if n <= 0 { true } else { odd(n - 1) } }
fn odd(n: int) -> bool { if n <= 0 { false } else { even(n - 1) } }
halt fn parity(n: int) -> bool { even(n) }        -- Certified mutual descent

fn stuck(n: int) -> () { if n > 0 { stuck(n) } }       -- MayDiverge: no descent
fn skipped_progress(n: int) -> () {
    var i = 0
    while i < n { if i == 0 { next }; i += 1 }
}                                               -- MayDiverge: next bypasses progress
-- halt fn bad_loop() -> () { skipped_progress(1) }    -- Error [E0820]

type Link = { var mut following: ?Link }
fn follow(node: Link) -> () {
    match node.following { Some(child) -> follow(child), None -> () }
}                                               -- MayDiverge: Link need not be acyclic
-- halt fn bad_follow(node: Link) -> () { follow(node) } -- Error [E0820]

fn closed_but_infinite(action: fn() -> ()) @{} &{} -> () { action(); loop {} }
-- Closed higher-order rows still permit divergence.
fn inferred_alias() -> () {
    let action: fn() -> () = forever
    action()
}                                               -- Ascription preserves MayDiverge
-- halt fn invalid_alias() -> () { inferred_alias() }  -- Error [E0820]
```

Uncertified loops or recursion give `MayDiverge`, not an effect. The special [finite-evaluation contract](#finite-evaluation-with-div) can certify a bounded invocation without certifying its unbounded action. Merely handling `Div::exhausted`, counting selected user operations, or imposing a static-evaluation budget supplies no such proof for an arbitrary run-time call.

### Parameter Modes, Caller Obligations, and Defaults

```ril
type Cell = { var count: int }
fn inspect(cell: Cell) -> int { cell.count }
fn observe(ref cell: Cell) -> int { cell.count }
fn bump(mut cell: Cell) &mut -> () { cell.count += 1 }
fn retain(^mut cell: Cell) -> ^mut(cell) Cell { cell }

let immutable = Cell.{ count: 0 }
assert(inspect(immutable) == 0)
let mut cell = Cell.{ count: 0 }
bump(mut cell)
cell !> bump()                         -- Supplies mut, not ^mut
assert(observe(ref cell) == 2)
let ^mut alias = retain(^mut cell)
alias.count += 1
assert(cell.count == 3)                -- Retained alias survives the call

-- inspect(cell)                      -- Error [E0535]: surviving writer
-- observe(cell)                      -- Error [E0405]: missing ref marker
-- inspect(mut cell)                  -- Error [E0406]: wrong mode
let ref observed = cell
-- bump(mut observed)                 -- Error [E0520]: no write authority
-- let bad: fn(Cell) &mut -> () = bump -- Error [E0407]: parameter modes differ
```

| Parameter | Caller form | Accepted input | Authority |
| :--- | :--- | :--- | :--- |
| `p: T` | `expression` | Immutable value / publishable fresh data | Read-only immutable data |
| `ref p: T` | `ref expression` | Reference data / callable environment | Observe; preserve immutable/live origins |
| `mut p: T` | `mut target` or `!>` | Writable reference / callable environment | Pinned interior access; ends at return |
| `^mut p: T` | `^mut target` | Writable reference / callable environment | Pinned interior access; may retain a writer |
| `new p: T` | `new expression` | Verified unpublished ordinary reference construction | Pinned construction access until explicitly handed onward; old construction paths then end |

The ordinary `ref`/`mut`/`^mut` modes cover named/anonymous functions, callable types, effect operations/handlers, and generic/built-in instantiations. Fresh construction parameters add the verified `new` path for ordinary Ril callables and recognized storage inputs; effect and foreign restrictions remain explicit. [Fresh storage inputs](#fresh-values-in-storage-calls) receive construction authority before ordinary immutable publication. A wrapper must declare `new` to preserve that path; an ordinary read-only wrapper still publishes immutable data.

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
| Write through immutable data or a `ref` | `E0520` |
| Callable parameter modes differ | `E0407` |
| Omit a required retained-writer capability on a named definition, or omit an independently required sharing marker | `E0510`; anonymous contract inference never supplies absent authority |

Modes are explicit, including through forwarding and subtyping. They neither grant absent permissions nor extend lifetimes or bypass exclusivity.

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
ParameterMode    ::= "ref" | "mut" | "^mut" | "new"
```

Mutable modes do not apply to static key arguments.

#### Fresh Construction Parameters

A `new value: T` parameter receives the unpublished construction authority of ordinary reference data without first publishing it immutable. Its explicit argument is `new expression`. This mode is available to verified named and anonymous Ril functions, their callable types, and the recognized storage inputs below; it is not an allocation expression, a deep copy, a reference-to-resource conversion, or a general move of an established variable.

```ril
type Cell = { var count: int }
fn append_cell(mut target: []Cell, new cell: Cell) &mut -> () {
    target !> Array::push(new cell)
    -- target !> Array::push(new cell) -- Error [E0549]: the old construction path has ended
    -- let count = cell.count         -- Error [E0549]: reads through that path have ended too
}
fn forward_cell(new cell: Cell) -> new Cell {
    new cell                          -- Explicit root handoff; no allocation occurs here
}
fn normalize_cell(new cell: Cell) &mut -> new Cell {
    cell.count += 1                   -- Writes before handoff retain parameter-write obligations
    new cell
}
let mut cells: []Cell = []
append_cell(mut cells, new forward_cell(new Cell.{ count: 0 }))
cells[0].count += 1
```

| Construction parameter concern | Normative rule |
| :--- | :--- |
| Eligible type (`E0411`) | Ordinary reference data only. Value types, resource/task/scope authority, callable roots, and any graph containing retained callable environments or non-ordinary authority are excluded; wrapping, opacity, or an outer fresh root cannot hide them |
| Eligible expression (`E0548`) | Prove the complete initial-reception contract: eligible constructed writable regions are isolated from pre-existing writable regions and have no surviving outside writer, observer, or active environment. Preserve immutable constituent sharing, aliases, cycles, and member schemas |
| Existing bindings (`E0548`) | `new immutable`, `new observed`, and `new ordinary_mutable_binding` do not thaw, copy, or consume those established bindings. Last use is not evidence of construction eligibility |
| Forwarding source | A still-active root `new` formal, or a verified eligible construction expression, may be handed onward. Projection does not split a formal's construction authority into independently transferable roots |
| Use before handoff | The formal is pinned: no rebinding (`E0502`). Reads, temporary `ref` observations, and schema-authorized writes are allowed while active; actual parameter writes require `&mut`. Observation aliases remain tied to the same construction authority |
| Handoff | Evaluate each explicit `new` argument operand once in ordinary argument order. When that operand passes reception checks, transfer authority to its prepared argument and end all accesses through the old formal and its derived reference paths before evaluating later arguments or defaults. The callee receives that one active construction path; copied scalar values remain usable. A later argument failure discards the prepared transfer without reviving the old path. A direct construction return transfers to the prepared return value before subsequent cleanup |
| Ended use (`E0549`) | Reject any possible read, write, forwarding, alias use, or capture access through an ended construction path. Branches and loops must establish that the path is active at each use; a path consumed on a possible branch is not proved active after the join |
| Outside aliases | An outstanding derived reference or environment cannot remain independently usable across a handoff. Alias, lifetime, exclusivity, and task-boundary checks remain required; invalidating a source path does not invalidate or grant authority to unrelated established bindings |
| Return | A compatible `-> new T` result may hand an active `new` formal onward using `new value` in a direct tail or `return new value`. The old path ends before the caller receives the result. Locally constructed roots retain their ordinary construction-return rules |
| Publication and sharing | Read-only publication or creating an independent retained writer ends initial-forwarding eligibility. Deliberate `^mut` sharing still requires its source/retention contracts and markers; it cannot be disguised as another `new` reception. A root `new` handoff alone adds no `&^mut` |
| Omitted transfer | A construction parameter is affine: it may be discarded on completion only subject to outstanding Result-inspection and other ordinary completion obligations. Failure or abort does not return construction authority to an ended caller path. Any ordinary immutable result still must satisfy the usual whole-graph publication checks |
| Higher-order use | Callable parameter modes must match (`E0407`); aliases, imports, ascriptions, and callback forwarding preserve construction-path consumption and result-source metadata. An ordinary parameter or an open effect/capability row cannot substitute for `new` mode |
| Defaults | A `new` parameter cannot have a default (`E0404`); an actual handoff requires its explicit argument marker |
| Effect/foreign boundary | This version supplies no construction-input contract for effect-operation parameters or handler binders (`E0411`), or for bodyless foreign calls (`E0908`). Ordinary temporary effect/foreign modes keep their existing rules |
| Phase | This is a run-time construction contract. Static/meta/type computation has no construction-input mode; a `new` parameter in a static declaration is `E0411`, and run-time construction handoffs are not static computations |

The only additional positions admitting a `new expression` handoff are a matching construction argument and a `-> new T` return. It is not a new binding, member, or standalone data-type modifier. Missing and wrong argument modes remain `E0405` and `E0406`; a `new` expression in another expression position is `E0548`. A construction parameter cannot be passed implicitly through an ordinary immutable parameter. Distinct expression evaluations keep their true allocation identities; handoff never creates a new allocation identity.

In a caller with an active construction formal `cell`, `f(new cell, cell.count)` and `f(new cell, new cell)` both use an ended path in their second argument (`E0549`). Preparing all arguments before invoking `f` does not duplicate construction authority or defer its consumption.

For a generic `new value: T`, this parameter mode restricts admitted instantiations to eligible ordinary reference data; it does not assume every bare `T` is a reference. A concrete declaration with an ineligible parameter type and an ineligible generic instantiation are `E0411`. Existing structural bounds may establish ordinary reference shape; no new type sort or run-time witness is introduced. Definition checking must hold for every admitted instantiation, and full graph eligibility is checked at each handoff.

```ril
-- Cell, append_cell, and forward_cell have the preceding contracts.
let immutable = Cell.{ count: 0 }
let mut established = Cell.{ count: 0 }
established.count += 1
let mut cells: []Cell = []
-- append_cell(mut cells, Cell.{ count: 0 }) -- Error [E0405]: missing construction argument marker
-- append_cell(mut cells, new immutable)    -- Error [E0548]: immutable publication cannot be undone
-- append_cell(mut cells, new established)  -- Error [E0548]: ordinary writers are not moved
-- fn scalar(new value: int) -> int { value } -- Error [E0411]: new parameters require ordinary reference data
fn forwarding<T>(new value: T) -> new T { new value }
let mut cell = forwarding(new Cell.{ count: 0 })
cell.count += 1
-- let value = forwarding<int>(new 1)   -- Error [E0411]: ineligible generic instantiation
```

`-> new T` is deliberately weaker than this input contract: a locally constructed root may already have been shared under its required retention contracts. A forwarding `new` formal must still possess unpublished authority at its explicit handoff. Verified summaries retain whether a returned root was allocated inside the invocation or arrived through a construction parameter, its true entry origins, all contained dependencies, and its permission history. Initial eligibility and disjointness must be proved from those facts, never from the word `new` alone.

#### Fresh Values in Storage Calls

```ril
type Cell = { var count: int }
fn copy_cell(cell: Cell) -> new Cell { clone(cell) }
fn build_cell() -> new Cell {
    let mut cell = Cell.{ count: 0 }
    cell.count += 1
    cell                               -- OK: root write authority survives; full initial eligibility is verified
}
let original = Cell.{ count: 1 }
let mut cells: []Cell = []
cells !> Array::push(clone(original))   -- OK: initial writable reception
cells !> Array::insert(0, Cell.{ count: 2 }) -- OK: constructor
cells !> Array::push(copy_cell(original))   -- OK: verified fresh return
cells !> Array::push(build_cell())
cells[0].count += 1
cells[1].count += 1
cells[2].count += 1
cells[3].count += 1
assert(original.count == 1 && cells[0].count == 3 && cells[3].count == 2)
```

The `value` input in `Array::push`, `Array::insert`, and `Map::set` retains its initial-storage contract and additionally accepts an explicit `new expression` construction handoff. Its existing ordinary immutable/value, `ref` observation-storage, and `^mut` retained-writer forms remain distinct valid receptions; this is not a single strict `new`-only parameter. An unmarked eligible construction expression continues to receive unpublished authority directly at these built-ins before ordinary immutable reception. An incoming `new` formal must instead be forwarded with its explicit `new` handoff. Ordinary wrappers can preserve this construction path by declaring a [fresh construction parameter](#fresh-construction-parameters); an ordinary read-only parameter still ends eligibility. A `-> new T` return label alone proves neither initial eligibility nor absence of outside aliases. Existing live data still requires explicit `ref` or `^mut` reception. The `ref` form checks persistent observation origins and escape; call-time observation alone does not permit retention.

```ril
-- Cell, original, and copy_cell have the preceding declarations/contracts.
fn identity(cell: Cell) -> Cell { cell }
fn frozen_cell() -> Cell { let cell = Cell.{ count: 1 }; cell }
fn append(mut target: []Cell, cell: Cell) &mut -> () { target !> Array::push(cell) }

let frozen_copy = clone(original)
let mut cells: []Cell = []
cells !> Array::push(frozen_copy)       -- OK: stores a read-only element
-- cells[0].count += 1                -- Error [E0522]: let already published immutable data
cells !> Array::push(identity(clone(original)))
-- cells[1].count += 1                -- Error [E0522]: read-only parameter path
cells !> Array::push(frozen_cell())
-- cells[2].count += 1                -- Error [E0522]: fresh allocation, but already immutable
append(mut cells, clone(original))
-- cells[3].count += 1                -- Error [E0522]: wrapper's parameter is read-only

fn append_copy(mut target: []Cell, source: Cell) &mut -> () {
    target !> Array::push(copy_cell(source)) -- OK: constructs a new result; &mut suffices
}
let push: fn(mut []Cell, Cell) &mut -> () = Array::push
push(mut cells, clone(original))       -- OK: alias preserves the operation's contract
cells[4].count += 1
```

```ril
type Cell = { var count: int }
type Holder = { child: Cell }          -- Default member is deeply immutable
let mut shared = Cell.{ count: 1 }
let mut cells: []Cell = []
cells !> Array::push(ref shared)      -- OK: explicit read-only live element
-- cells !> Array::push(shared)       -- Error [E0535]: no implicit live reception
-- cells[0].count += 1                -- Error [E0522]: existing writer needs an argument marker
cells !> Array::push(^mut shared)      -- OK: explicit retained writer
cells[1].count += 1
assert(shared.count == 2)

let mut holders: []Holder = []
let snapshot = clone(ref shared)
holders !> Array::push(Holder.{ child: snapshot })
-- let mut child = ^mut holders[0].child -- Error [E0520]: default member remains immutable
```

```ril
type Cell = { var count: int }
let original = Cell.{ count: 1 }
let repeated = (mut original, mut original)
let mut pairs: [](mut Cell, mut Cell) = []
pairs !> Array::push((^mut clone(repeated))) -- OK: marks internal sharing, not an argument mode
pairs[0].0.count += 1
assert(pairs[0].1.count == 2 && original.count == 1)
-- pairs !> Array::push(clone(repeated)) -- Error [E0510]: internal writable sharing is unmarked
-- pairs !> Array::push(^mut clone(repeated)) -- Error [E0410]: argument mode requires a target
```

| Check | Requirement |
| :--- | :--- |
| Eligible regions | Newly constructed ordinary writable storage, isolated from pre-existing writable regions, with no surviving outside observer, writer, or active environment |
| Established paths | Bindings select permissions; `let`, plain `var`, `ref` handles, and read-only parameters end eligibility. A valid `new` formal can hand its construction path onward explicitly; ordinary established writers, including retained returns, still need `^mut` arguments |
| Expressions / returns | Preserve actual provenance. A `new` root with outside aliases or contained live dependencies is not automatically eligible; every retained alternative must satisfy the full initialization contract |
| Constituents | Preserve member schemas and nonfresh permissions. Default members stay immutable; fresh outer data cannot retain concealed existing writers |
| Operation identity | Imports, aliases and type ascriptions preserve built-in reception contracts. A verified `new` parameter supplies the user-callable construction path; a matching name or ordinary read-only signature supplies none |
| Reception | Evaluate once in ordinary order. Success installs initial authority and invalidates a forwarded `new` formal's old construction paths; failure installs no path and never revives an ended path. Initial transfer alone adds no standalone `&^mut`; actual sharing and other effects/state retain their checks |
| Other obligations | Internal aliases obey exclusivity; traversal, live array `ref` stability, and Result inspection remain checked. Foreign exchange, resources and retained callable environments gain no exemption |

#### Default Parameters and Named Arguments

```ril
fn pair(a: int = 1, b: int = 2) -> (int, int) { (a, b) }
assert(pair(b: 20, 10) == (10, 20))
assert(pair(a: 10, 20) == (10, 20))
-- pair(10, a: 20)                     -- Error [E0325]: a is already bound
```

- Named and anonymous parameters share the same default rules. Defaults have no residual effects or state obligations; `mut`/`^mut`/`new` defaults are forbidden (`E0404`). A `ref` default is received in its declared mode without a caller token; explicit supplied arguments still require `ref`. Earlier `ref` parameters do not exempt a later ordinary default from immutable reception.
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

Defaults run anew in the caller before callee entry, using declaration scope and earlier read-only arguments. New environments/retained handlers belong to that preparation; forwarding them adds no callee `&capture`, but publication beyond the caller does. Origin, permission, lifetime, and [termination/`halt` checks](#termination-and-halt-contracts) remain unchanged. Preparation adds no frame or entry charge; its calls, loops, handler entries, and resumptions use all active budgets.

An unknown parameter label is `E0339`; a non-callable callee is `E0338`. Missing or excess ordinary arguments retain `E0314`, after accounting for supplied names and defaults. Nullary variant parentheses retain the specific `E0353`. These diagnostics introduce no new restriction on the relative order of positional and named arguments.

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

References from a parameter default to itself or a later parameter are `E0408`. Other unresolved names retain `E0204`; generic-default forward references retain `E0320`. A parameter default with any residual effect or state obligation is `E0409`, even if the enclosing callable declares that obligation. Pure defaults referring to earlier parameters remain valid.

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
| Subtyping / type identity | Labels are call-site metadata, not additional type-identity constraints; parameter modes, types, and obligation contracts remain checked |

Callable types admit no default-expression syntax. An ascription may rename labels by position, but never changes the called body, parameter order, permissions, effects, or provenance. A call that uses a preserved default retains that default's evaluation, termination, and dependency checks. Duplicate labels in one signature are `E0203`.

### Anonymous Functions, Trailing Closures, and Projection Accessors

```ebnf
AnonFnExpr    ::= "\" [ AnonParams ] [ EffectAnnot ] [ StateAnnot ] "->" ( Expression | Block )
AnonParams    ::= AnonParam { "," AnonParam } [ "," ]
AnonParam     ::= [ ParameterMode ] Identifier [ ":" TypeExpression ] [ "=" Expression ]
AccessorExpr  ::= "\" AccessorNav AccessorField { AccessorNav AccessorField }
AccessorNav   ::= "." | "?."
AccessorField ::= Identifier | TupleIndex
```

- **Unary Desugaring Equivalence**: An `AccessorExpr` evaluates to a unary pure function projecting properties from its argument:
   - `\.field` desugars to `\x -> x.field`
   - `\.0` desugars to `\x -> x.0`
   - `\.field?.subfield` desugars to `\x -> x.field?.subfield`
   - `\?.field` desugars to `\x -> x?.field`
- **Product Type Duality**:
   - `Identifier` statically projects named fields from records (`{...}`), nominal wrappers, or refined named variants. Unknown fields trigger `E0336`.
   - `TupleIndex` statically projects 0-indexed positional components from tuples (`(T0, T1, ...)`) or refined positional variant payloads ($S|_V$). Positional indices are statically checked at compile time against tuple arity $n$ ($0 \le i < n$). Out-of-bounds indices trigger `E0312`.
- **Safe Navigation Propagation**:
   - If any navigation segment uses safe navigation `?.`, evaluation short-circuits to `None` when the intermediate receiver is `None`. The resulting accessor closure return type is automatically lifted into `?T`.
- **Collection Segregation**:
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
type Employee = { id: int, name: str, salary: int }
type Department = { name: str, leader: ?Employee }
type Company = { name: str, dept: ?Department }

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
type Team = { id: int, leader: (str, int) }
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
type Cell = { var count: int }
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

- **Abstraction**: `&up` follows [callable contract matching](#callable-contract-matching); direct named capture access still requires source groups.
- **Definitions (`E0534`)**: A standalone `&up` annotation on a definition cannot replace its concrete source obligations. Parameter/return callable types may use it as an abstraction under callable matching. Named definitions spell the required concrete capture-source annotations; anonymous definitions preserve the same concrete sources in their fully inferred contracts without mandatory source completion.
- **Creation**: New environments surviving the enclosing callable's return contribute `&capture`, including those nested in returned aggregates. Named definitions must spell that obligation; anonymous definitions may retain it entirely in the inferred contract. Forwarding existing environments or using call-local ones adds no environment-creation obligation.
- Anonymous functions capture free value bindings, including module bindings. Module-level named functions use declared external access; escaping block-local functions retain their required lexical environments.
- **Binding Choice**: An immutable environment can be bound with `let`; an existing immutable environment may also be observed with `ref`. Observer environments use `let ref` under the [observation-wrapper rules](#normative-rules-for-read-only-references), preserving immutable and pinned live dependencies. A persistent mutable environment requires a writable handle. These are environment facts, not consequences of the visible `&up` spelling.
- **Sharing**: A private cell exposed only through one new closure requires `&capture`. Exposing another authority to that cell also requires `&^mut`.



## State and Capability Tracking

### Local Mutation Purity and Local Capability Discharge

A function that mutates locally allocated variables that do not escape retains a purely functional external interface. Capability obligations for frame-confined variables are **discharged locally**:

```ril
type Buffer = { mut items: []int }
fn append_val(mut b: Buffer, v: int) &mut -> () { b.items !> Array::push(v) }

-- Pure function with internal primitive mutation:
fn compute_sum(n: int) -> int {
    var total = 0
    var i = 1
    while i <= n {
        total += i
        i += 1
    }
    total                              -- Pure to callers: signature is fn(int) -> int
}

-- Local Capability Discharge with reference types and &mut callees:
fn generate_sequence(count: int) -> []int {
    let mut local_buf = Buffer.{ items: [] }
    var i = 0
    while i < count {
        append_val(mut local_buf, i)   -- &mut discharged locally: local_buf does not escape
        i += 1
    }
    local_buf.items                    -- Pure: signature carries NO &mut!
}

-- Local discharge of scalar insertion (no retained mutable reference):
type NodeHub = { mut nodes: []int }
fn link(mut hub: NodeHub, node: int) &mut -> () { hub.nodes !> Array::push(node) }

fn test_internal_hub() -> int {
    let mut local_hub = NodeHub.{ nodes: [] }
    let local_node = 42
    link(mut local_hub, local_node)    -- &mut discharged locally: the scalar is copied
    len(ref local_hub.nodes)          -- Pure: local observation adds no external mutation obligation
}
```

### Parameter Mutation

A function mutating any parameter retains at least the `&mut` obligation; independent `&^mut` includes this obligation. Named definitions MUST spell the required capability, while anonymous functions may leave it to full inference. A root return `^mut(x) T` covers only that return's retention, so actual writes remain a distinct `&mut` obligation. Named external mutation keeps its named capability and concrete origin.

```ril
fn clear_items(mut list: []int) &mut -> () {
    list !> Array::truncate(0)         -- OK: declared &mut
}

-- Missing capability annotation is statically rejected:
-- fn bad_clear(mut list: []int) -> () {     -- Error [E0510]: mutating operation requires caller signature to declare '&mut'
--     list !> Array::truncate(0)
-- }
```

### Retained Mutable Sharing

`^mut` has unary prefix precedence; it evaluates its operand once and preserves identity and permissions under the contracts below.

```ebnf
SharingExpr     ::= "^mut" Expression
```

```ril
type Entry = { var id: int }
type Hub = { mut entries: []Entry }
let mut global_hub = Hub.{ entries: [] }

fn register_entry(mut hub: Hub, ^mut entry: Entry) &^mut -> () {
    hub.entries !> Array::push(^mut entry)
}
fn publish_entry(^mut entry: Entry) &^mut &up(sub){mut global_hub} -> () {
    global_hub.entries !> Array::push(^mut entry)
}
-- The retained origin is entry. Merely inserting it does not create a new authority to global_hub.
```

- **Retention**: `&^mut` publishes another independent writable authority, including sharing newly created local state among multiple surviving authorities. A `^mut source` item names a retained global or captured source in its corresponding group and includes that source's write access; a destination merely receiving data uses a `mut destination` item. Standalone `&capture` and `&^mut` remain separate annotations, never group entries.
- **Arguments**: Retaining a mutable argument writer requires `^mut` on both parameter and argument. Ordinary call-scoped `mut` authority ends at return. Indirection preserves retained permissions and source identities.

```ril
type Cell = { var count: int }
type Holder = { mut child: Cell }
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
-- let mut bad = ^mut immutable        -- Error [E0520]: marker cannot grant write permission
-- let mut bad_ref = ^mut observed    -- Error [E0520]: marker cannot upgrade a live ref

let repeated = (mut immutable, mut immutable)
let ^mut copied = clone(repeated)
copied.0.count += 1
assert(copied.1.count == 1)             -- Internal aliases survive the isolated copy
-- let mut hidden_copy = clone(repeated) -- Error [E0510]: writable internal sharing must be marked
```

- **Local Sharing Marker (`E0510`)**: A new local writable path to existing ordinary storage or an existing callable environment requires an explicit reception marker: a [shared declaration](#shared-writable-reception) for single-identifier initialization, or `^mut expression` at any receiving site. The marker may cover one constituent or a whole construction/destructuring source; every constituent retains its own permissions. Deep copies with possible internal writable aliases also require acknowledgment. Proven immutable sharing needs none.
- **Checked Meaning**: The marker evaluates its operand once and preserves identity. It neither clones nor freezes, transfers ownership, grants missing permissions, revives invalid resources, or extends temporary mutable authority. Missing markers and invalid authority are distinct errors; adding a marker cannot repair `E0520`–`E0528` violations. Possible internal aliases need not be resolved to one exact graph, but remain subject to all overlap checks.
- **Return and Reception**: `^mut(x) T` covers root-return retention without a duplicate independent `&^mut`; actual writes and extra escaping paths retain their own obligations. Every shared writable reception still needs a marker, supplied by declaration sugar only for its initializer and by `^mut expression` elsewhere. It confirms the same return publication and does not add a second capability obligation. A checked callable tail may forward authority under its declared return contract; a plain block cannot hide local alias creation. `clone` isolation alone does not mark internal writable aliases, including at [fresh storage inputs](#fresh-values-in-storage-calls).
- **Confinement**: Local `^mut` does not by itself add external `&^mut` to the enclosing function. Conversely, local discharge does not remove required markers at local data-sharing sites. Captured and returned sharing still contributes its actual authority roots whether or not its facts are written explicitly.

```ril
fn retain(^mut cell: Cell) -> ^mut(cell) Cell { cell }
let mut original = Cell.{ count: 0 }
let ^mut returned = retain(^mut original) -- Explicit reception of the returned writer
returned.count += 1
original.count += 1
type Packet = { mut item: Cell }
let mut packet = Packet.{ item: ^mut retain(^mut original) }
packet.item.count += 1
-- let mut hidden_packet = Packet.{ item: retain(^mut original) } -- Error [E0510]: wrapping does not hide shared reception
-- let mut hidden = retain(^mut original) -- Error [E0510]: returned sharing still needs a reception marker
-- let mut hidden = ^mut retain(original) -- Error [E0405]: ordinary argument lacks the retention marker
-- let mut hidden = ^mut retain((^mut original)) -- Error [E0405]: sharing expression is not an argument-mode marker
-- let mut hidden = ^mut retain(^mut clone(original)) -- Error [E0410]: mutable argument must be an assignable target
```

| Surviving references | Sharing obligation |
| :--- | :--- |
| Repeated fields/cycles inside one fresh passive result graph | No additional external authority; still check internal aliasing |
| Entry parameter root retained only through `^mut(x) T` | Root return covers retention; writes still require `&mut` |
| Extra storage/contained/captured writable path, including to the same source | Independent `&^mut` or its named form |
| One cell exposed through a closure and a direct graph reference | `&^mut`, even inside one returned tuple |
| One cell exposed through multiple mutable closures | `&^mut` |

Each newly surviving external path, mutable environment, and separately exposed graph participates in retention. Merely returning an unchanged graph does not recreate its existing aliases, cycles, or environments, and adds no duplicate `&^mut` or `&capture`.
- **Local Discharge**: Retention whose origins and authority roots all remain confined to the current frame is discharged locally. Mutation of already shared storage does not itself create another retention obligation. Existing sharing remains a provenance fact; it is not a repeated publication on every invocation.
- **Contract Matching**: Concrete definitions cannot overstate capabilities (`E0529`). Callable types use exact normalized closed contracts or explicit openness under [callable contract matching](#callable-contract-matching); neither changes parameter modes. Actual retention satisfies `E0527` for `^mut`.

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

A writable container never upgrades an immutable/`ref` element (`E0522`). Retaining an inserted existing writer requires `^mut` and the corresponding retention capability. Receiving an unpublished fresh value under its storage contract supplies initial construction authority, subject to the same internal-alias checks.

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
-- fn bad_read() -> str { APP_CONFIG_NAME }          -- Error [E0510]: accessing external state requires caller signature to declare capability '&up(sub){APP_CONFIG_NAME}'
-- fn bad_write() -> () { transaction_count += 1 }        -- Error [E0510]: mutating external state requires caller signature to declare capability '&up(sub){mut transaction_count}'

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

These forms use the same [callable contracts](#callable-contracts); spelling the call differently does not change its concrete origins.

Accessing module-level or captured bindings records the corresponding concrete named-source obligation. Named definitions must spell those source groups and must also declare concrete named obligations inherited from calls, either with a matching source group or an admissible function state contract reference. Anonymous definitions retain the same concrete source identities without mandatory source spelling. Only genuine callable-parameter dependencies retain symbolic forwarding; anonymous inference never reclassifies a known concrete source as an unknown parameter dependency.

This includes reading a module-level `meta let NAME` in a run-time value expression: the inferred contract records that named source, and a named definition declares `&up(sub){NAME}`. Compile-time evaluation and immutability do not erase the source. Reads performed in the static/type domain are exempt from this run-time state obligation, including type expressions and static arguments.

Within either kind of source group, a bare item permits read-only access, whether its actual data is immutable or live. It does not promise deep immutability or create a `let ref` binding. `mut name` adds writes; `^mut name` additionally permits retained writable sharing. Each mode applies only to its own item.

Direct access includes storage access in a named definition's lexical anonymous functions and handler arms when those operations contribute to the named definition's current invocation, and mutable argument permissions it supplies. The named definition must spell those direct source obligations after local discharge; a contract reference cannot replace them. The anonymous callable itself retains its complete inferred source contract without mandatory annotation. Referencing a named function declaration is not itself a read of storage; accessing a stored external callback is. Future operations of a returned callable remain latent, while its creation, capture, and retention obligations are checked separately.

### State Groups and Captured Layers

```ebnf
StateAnnot          ::= StateCapability { StateCapability }
StateCapability     ::= "&mut" | "&^mut" | "&up" | "&capture" | "&" "{" "}"
                      | GlobalStateGroup | CapturedStateGroup
                      | ReturnDependencyGroup | StateContractRef
GlobalStateGroup    ::= "&up" "(" "sub" ")" "{" StateItemList "}"
CapturedStateGroup  ::= "&up" [ "(" CaptureOwner ")" ] "{" StateItemList "}"
ReturnDependencyGroup ::= "&return" "{" ReturnDependencyList "}"
ReturnDependencyList ::= ReturnDependency { "," ReturnDependency } [ "," ]
ReturnDependency    ::= ( "ref" | "^mut" ) QualifiedName
CaptureOwner        ::= SnakeCase
StateItemList       ::= StateItem { "," StateItem } [ "," ]
StateItem           ::= [ StateMode ] QualifiedName
StateMode           ::= "mut" | "^mut"
StateContractRef    ::= "&" QualifiedName
```

| Form | Meaning | Source resolution |
| :--- | :--- | :--- |
| `&up` | Callable-type environment abstraction | Actual captured origins remain in verified metadata |
| `&up(sub){mut cache, CONFIG}` | Current invocation's module-storage access | Module bindings |
| `&up{mut count}` | Current invocation's captured access | Directly enclosing callable layer |
| `&up(outer_layer){mut count}` | Current invocation's farther named capture | The resolved binding must belong to `outer_layer` |
| `&return{ref x, ^mut y}` | Possible contained dependencies of the returned graph | Formal parameters or visible external/captured origins |

Return dependencies are facts, not invocation permissions. They neither replace `&mut`, `&^mut`, `&capture`, or named state, nor introduce a general parameter-access group. Scalar copies add no return dependency; capturing a mutable scalar cell retains its origin. Body-local regions and output correlations remain in verified metadata without inventing public identifiers.

```ril
var global_count = 0
let GLOBAL_SCALE = 2
fn tick() &up(sub){mut global_count, GLOBAL_SCALE} -> int {
    global_count += GLOBAL_SCALE
    global_count
}

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

- **Module Groups (`E0538`)**: `&up(sub){...}` contains only resolved module-storage bindings. The literal `sub` is a contextual source selector, not a resolved name; it is excluded from `CaptureOwner` in this position. Qualified names and declaration imports preserve storage identity; a named function declaration is not a storage item.
- **Environment Groups (`E0538`)**: `&up{...}` contains captured bindings from one enclosing callable layer. A directly enclosing layer needs no owner. A farther named layer requires its function name in `&up(owner){...}`. A farther anonymous layer uses a separate ownerless `&up{...}` group. An explicit owner verifies the source layer; it cannot select a same-spelled binding hidden by shadowing.
- **Resolution Before Classification**: Resolve each item by ordinary lexical rules, then verify its group and owner. Headers do not bypass shadowing, rebind a local source to a module source, or identify a dynamic activation by name.
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

Standalone `&capture`, `&mut`, `&^mut`, and the callable-type environment abstraction `&up` remain separate forms. The open capability marker `&` belongs only to callable-type patterns; it supplies no group, authority, or source-completion exemption for a named definition. No group establishes uniqueness, consumes ordinary writable authority, or changes a retained handler's definition.

In a contract position, unqualified `&up` takes precedence over state-contract references. A following `{` selects a captured-source group. A following `(` selects a source group with a required selector: the literal `sub` selects module storage, and any other capture-owner name selects an enclosing callable layer. Every source group requires a nonempty `{...}` list; empty parentheses, missing braces after a selector, repeated parenthesized selectors, and empty groups use `E0538`. Without a following `{` or `(`, `&up` is the standalone callable-type environment abstraction. This choice is fixed before name resolution and never falls back to another source kind. `&return{...}` also retains its group-head priority and requires braces. Use a qualified provider reference, such as `&Helpers::up`, for a same-spelled function. The words `up` and `sub` remain ordinary identifiers outside these contextual positions.

```ril
var env = 0
fn bump_env() &up(sub){mut env} -> () { env += 1 }
var sub = 0
fn bump_sub() &up(sub){mut sub} -> () { sub += 1 } -- Selector and storage item have distinct roles
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
pub type Cell = { var count: int }
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
-- Error [E0201]: a contract reference does not export the private binding
```

- **Provider (`E0539`)**: `&callee` / `&Module::callee` selects a visible ordinary named Ril definition's verified named-state contract. Resolve names first: lexical absence `E0204`, absent module member `E0209`, private member `E0201`; then reject a wrong provider kind with `E0539`. Value aliases and callable parameters are not providers.
- **Position (`E0539`)**: Allowed on ordinary named function definitions and callable types. Reject it as a direct annotation on anonymous definitions, effect operations, and bodyless foreign declarations. A nested callable type may use a verified provider reference independently of its enclosing construct.
- **Concrete Named Projection**: A reference denotes the provider's concrete global/captured source items and their verified access modes for its current invocation, including concrete named dependencies obtained through other calls. The bindings and lexical owners remain anchored to the provider's scope. It does not include effects, anonymous parameter permissions, standalone `&capture`/`&^mut`, symbolic callback dependencies, or a returned callable's future invocation obligations.
- **Coverage**: On a named definition, after local discharge, match inherited concrete named obligations by origin and permission; the caller need not invoke the provider by name. On a callable type, the verified named projection participates in exact closed matching or in the explicitly open capability contract. A reference imports no return relation: declare that separately. Actual parameter writes and extra retention still need `&mut`/`&^mut`; root-return retention follows its own annotation. Unrelated references on a definition leave `E0510`; unnecessary references there remain `E0529`.
- **No Erasure**: Calling through an alias or higher-order helper preserves the concrete dependencies. A provider reference cannot turn them into unknown callback dependencies, discharge conflicting mutable authority, or prove a recursive dependency empty. An explicit `&{}` constrains the total state, including referenced state.
- **Declaration Identity**: A declaration import alias or re-export preserves its provider identity. `let action = callee` and a public callable-valued binding do not create provider declarations; references to such bindings are `E0539`. The built-in capability spellings keep their established meanings; a same-spelled function requires a qualified reference. Public callable values without a suitable visible provider do not acquire an implicit private-state permission.

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
type Cell = { var count: int }
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

### Closure Capabilities and Handle Permissions

```ril
let mut counter = create_counter(0)
assert(counter() == 1)
-- let immutable = counter                -- Error [E0535]: live mutable environment cannot become immutable
let ref observer = counter
-- observer()                          -- Error [E0520]: observing a mutable callable does not permit invocation
```

A callable that writes its persistent captured environment requires `let mut`, `var mut`, or a `mut`/`^mut` parameter at invocation. An observer callable that reads live origins uses a `ref` handle/parameter. Plain `let`, plain `var`, and unmodified callable parameters require immutable environments; latent named-state/effect obligations remain checked independently.

An immutable callable may still have effects or named external-state obligations. Invocation checks those obligations and all transitive access sets, including handlers; `let` does not erase them. Declared external access alone does not create a named function's mutable environment.

### Law of Exclusivity and Cross-Argument Disjointness

A mutable invocation's writes must not overlap another participant's reads/writes. Read/read overlap is allowed. Check actual possible storage origins, not field names or indices; unknown overlap is `E0523` or `E0524`.

Use through the `mut` formal belongs to that call. Independent arguments, captures, and ambient origins are other participants. Nested forwarding suspends the caller's access until return; inactive aliases do not prohibit sequential sharing.

A call-local closure that captures a `mut` formal retains that formal's call-scoped authority and cannot extend its invocation lifetime. Access through this derived path belongs to the active call. An independently obtained ambient or captured path does not become part of that call authority merely because its object identity matches the formal's.

```ril
type Cell = { var count: int }
fn swap(mut a: Cell, mut b: Cell) &mut -> () {
    let saved = a.count
    a.count = b.count
    b.count = saved
}
let mut cells = [Cell.{ count: 1 }, Cell.{ count: 2 }]
swap(mut cells[0], mut cells[1])        -- OK: distinct allocations, not merely distinct indices
-- swap(mut cells[0], mut cells[0])    -- Error [E0523]: same writable origin

let immutable_cell = Cell.{ count: 0 }
let repeated = (mut immutable_cell, mut immutable_cell)
let ^mut copied = clone(repeated)
copied.0.count += 1
assert(copied.1.count == 1)             -- clone preserves internal aliases
-- swap(mut copied.0, mut copied.1)    -- Error [E0523]: distinct projections reach the same copied object
```

An explicit `^mut` publication permits sequential sharing, not overlapping exclusive writes or races. Mutations through any alias invalidate affected live refinements. Immutable references are exempt from such invalidation because no writable origin remains.

### Monotonic Permission Degradation and Anti-Laundering Matrix

Apply [provenance propagation](#complete-provenance-and-required-annotations) at every access path. The following cases distinguish permission failures from immutable-publication failures; clone and derive retain their explicit fresh-data contracts.

```ril
type Cell = { var count: int }
let mut box = .{ mut child: Cell.{ count: 0 } }
-- var hidden = box                  -- Error [E0535]: plain var requires immutable data
var ref cursor = box
-- let mut stolen = ^mut cursor.child -- Error [E0520]: projection cannot escape the read-only path
box.child.count += 1
assert(cursor.child.count == 1)        -- The independent writer remains valid
let mut replacement = .{ mut child: Cell.{ count: 9 } }
replacement.child.count += 1
cursor = replacement

fn project(ref box: { mut child: Cell }) -> ref(box) Cell { box.child }
-- let mut stolen = project(ref box) -- Error [E0528]: the observation return has no write authority
```

Plain `let`, plain `var`, ordinary parameters, and default members require immutable graphs. `ref` bindings/parameters observe existing data without freezing it or revoking independent writers. A callable's named external-state obligations remain independent of its data handle.

[Fresh storage reception](#fresh-values-in-storage-calls) precedes read-only binding or parameter passage; it cannot recover authority after either boundary.

```ril
type Cell = { var count: int }
let immutable = Cell.{ count: 0 }
-- let mut upgraded = immutable           -- Error [E0520]: existing immutable reference
let mut cells: []Cell = []
cells !> Array::push(immutable)           -- OK: container is writable, inserted element remains immutable
-- cells[0].count += 1                 -- Error [E0522]: container cannot grant its element write authority
let mut copied = clone(immutable)
cells !> Array::push(^mut copied)      -- Explicit retained writable element, locally discharged
copied.count += 1

fn identity(cell: Cell) -> Cell { cell }
-- let mut stolen = identity(immutable)  -- Error [E0528]: returned origin remains immutable
let same = identity(immutable)

let mut active = create_counter(0)
assert(active() == 1)
-- clone(ref active)                -- Error [E0530]: mutable captured environment cannot be cloned
-- let observed_as_immutable = active   -- Error [E0535]: ordinary let cannot contain this environment
```

Spread/destructuring copy scalars but preserve reference permissions (`E0525`/`E0521`); scalar `var` patterns are independent values. Structural collection mutation through any alias during iteration is `E0526`.

```ril
let mut items = [1, 2]
for items as item {
    -- items !> Array::push(item)      -- Error [E0526]: invalidates active iteration
}
items !> Array::push(3)
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

eff AppEffects { Console, State<int> } -- Combined effect set
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
| Effect-set aliases | Expand to their member instances; aliases do not create new operation identities |
| Operation selected through a set alias | Exactly one member instance must supply it; unresolved selection is `E0344` |
| Omitted effect arguments | Infer from ordinary argument/result, arm, and protected-computation constraints only when one instance is determined (`E0344` otherwise) |
| Generic arguments in source | Appear on the effect name; operations declare no independent generic parameter list |
| Handler arm | Handles one determined instance; never implicitly handles every instantiation |

Repeated arms for the same instantiated operation are `E0622`, including through aliases. A handler discharges only the instances it covers; uncovered instances remain residual. Effect instances containing still-symbolic enclosing static parameters retain those parameter identities until instantiation.

```ebnf
EffectDecl       ::= [ "pub" ] "eff" PascalCase [ GenericParams ] "{" EffectMemberList "}"
EffectMemberList ::= EffectOpDecl { "," EffectOpDecl } [ "," ] | EffectIdentifier { "," EffectIdentifier } [ "," ]
EffectOpDecl     ::= SnakeCase "(" [ ParameterTypeList ] ")" [ StateAnnot ] [ ReturnType ]
EffectAnnot      ::= "@" ( EffectRow | "{" "}" )
EffectRow        ::= EffectIdentifier { "+" EffectIdentifier }
EffectIdentifier ::= QualifiedName [ GenericArgs ]
EffectOperationRef ::= EffectIdentifier "::" SnakeCase
```

Effect identifiers resolve to PascalCase effect declarations. Operation signatures use the ordinary parameter-mode and capability rules; a declared operation may request read-only, temporary writable, or retained writable access. A `new` operation parameter is rejected with `E0411`: this version defines no effect-operation construction-input contract.

```ril
-- Console and BufferIo have the declarations above.
-- Effectful computation: invokes print twice and read_line once
fn hello() @Console -> () {
    Console::print("Enter name:")      -- First intercepted operation
    let name = Console::read_line()     -- Second intercepted operation
    Console::print("Hello, {name}")  -- Third intercepted operation (deep handler re-entered)
}

-- Effectful computation invoking capability-bearing BufferIo:
fn fill_header(mut target: []u8) @BufferIo &mut -> int {
    BufferIo::read_into(mut target)    -- OK: &mut capability flows through caller to operation
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
        Console::print(msg) -> { messages !> Array::push(msg); resume () },
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

A leading `ref`/`mut`/`^mut` on a handler parameter is its operation-parameter mode, before pattern interpretation. A `new` binder is rejected with `E0411`. The remaining pattern is irrefutable and contains no binding modifiers: `var` is `E0403`, and nested modes are `E0406`. Modes must match the operation declaration (`E0406`); omission does not infer observation or write authority. Ordinary names in handler-target position remain admitted so non-operation targets receive `E0621`.

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

type Cell = { var count: int }
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
| Discharge a declared effect instance | Cover every operation of that instance; built-in resource/system obligations follow their separate contracts |

```ril
type Cell = { var count: int }
eff Store { keep(^mut cell: Cell) &^mut -> () }
let mut cell = Cell.{ count: 0 }
let mut held: []Cell = []
with Store::keep(^mut value) -> {
    held !> Array::push(^mut value)
    resume ()
}
Store::keep(^mut cell)
held[0].count += 1
assert(cell.count == 1)
-- with Store::keep(mut value) -> resume () -- Error [E0406]: temporary mode cannot replace retained mode
```

| Operation parameter | Handler binder | Granted authority |
| :--- | :--- | :--- |
| Default | Plain pattern | Deeply immutable data; scalars copy |
| `ref` | `ref pattern` | Read-only observation of reference data or callable environments; preserve live origins and source lifetimes |
| `mut` | `mut pattern` | Temporary operation authority, ending when resumption starts |
| `^mut` | `^mut pattern` | Retained writable authority; actual retention remains tracked |

Destructured reference bindings receive no more than the mode and every source path permit; scalar constituents remain independent read-only copies. A `^mut` handler parameter still must exercise its authority under `E0527`. Resumption does not revoke lawful retained authority, but neither the handler mode nor the operation declaration extends a scoped lifetime or suspends exclusivity checks on independent origins.
`ref` parameters retain their observation restrictions across resumption; the following revocation rule concerns temporary `mut` authority only.

| Operation's ordinary `mut` authority | Arm's permission |
| :--- | :--- |
| Before `resume`, including evaluation of its value | Access through the matching parameter |
| Continuation starts | Revoke the authority; end all arm access through the parameter and derived aliases (`E0540`) |
| `resume` returns | No restoration; copied scalars, independent data, and lawful retained `^mut` authority remain usable |

Outer function/callback activations stay active. Independent captures and ambient aliases remain separate exclusivity participants. Neither resumption nor `^mut` extends a call-scoped or resource-scoped lifetime.

| Retained handler context | Rule |
| :--- | :--- |
| New callable | Select creation-scope lexical handlers for transitive residual operations, including callees |
| Handler inside callable body | Establish on invocation |
| Hoisted block-local function | Context at defining-block entry, before its sequential `with`; nested blocks inherit their enclosing context |
| Existing callable / first reference | Never rebind or select a new handler context |
| Expected callable type | Check after selection; reject an incompatible selection rather than substitute a future caller's handler |
| Uncovered operations | Remain residual; each later invocation must handle/forward them; closed contracts require discharge |
| Persistent definition (`E0614`) | Lawful environment and fresh boundary/resumptions per invocation; no old continuations, scoped resources, or return/loop targets |
| Answer (`E0614`) | Every retained arm tail fits the new answer type; outer dependencies have stable handlers or residual rows |
| Creation | Does not execute latent body operations; counts actual environment creation, sharing, and escape |
| Child task (`E0615`) | No ancestor active handler or live/mutable environment; immutable data may establish a child-local handler |

Escape alone is valid. Retention preserves dispatch, required outer definitions, and access/sharing/escape facts for provenance diagnostics, without extra capture syntax. Effect discharge never removes state, capture, live `ref`, or mutable-environment obligations.

```ril
type Button = { label: str, on_click: fn() &up -> () }
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
    -- read_without_state(captured)    -- Error [E0534]: the retained handler environment cannot cross a closed state contract
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

`with f(args)` without `->` makes the rest of the containing block a zero-argument anonymous callable, supplied as the final argument to `f`. The result of that call is the result of the containing block's remaining computation. This is a general callable application form, not a special syntax for `Div`; `f` may define a parameterized handler or another scoped computation.

| Application rule | Contract |
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

A helper's internal handler can discharge operations that the final callable forwards, but cannot replace handlers already selected by that callable. The usual declaration partition and `where` scopes remain in force; this form creates no new declaration region beyond the anonymous callable's ordinary execution scope. Each application includes the following applications in its final callable, so applications nest in source order. A supplied argument list must leave the final callable parameter unbound; ordinary call diagnostics reject an incompatible target or duplicate argument.

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

-- Delimited Early Abort with Proven LIFO Cleanup & Commit-on-Write Memory:
eff Auth {
    authenticate() -> bool,
}

type AuditLog = { mut entries: []str }

fn guarded_workflow(mut audit: AuditLog) @Auth &mut -> str {
    audit.entries !> Array::push("STEP_1")                               -- Physical mutation committed
    let scoped mut file = Resource.{ name: "vault.dat", on_close: \-> audit.entries !> Array::push("CLEANUP_FILE") }
    let scoped mut session = Resource.{ name: "admin_token", on_close: \-> audit.entries !> Array::push("CLEANUP_SESSION") }

    if !Auth::authenticate() {
        "Unauthorized"
    } else {
        audit.entries !> Array::push("SUCCESS")
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

Ril provides the system operation families Fiber, Concurrent, and Div, and the alias Async:

- **`@Fiber` (Cooperative Fiber Control)**: Cooperative yielding and leaf I/O suspension without concurrent task branching authority. A leaf operation's contract determines what event completes its wait; there is no bare public park/unpark operation.
- **`@Concurrent` (Structured Concurrency)**: Structured scope, child-task forking, and joining, with the contracts below.
- **`@Async` (Suspendable I/O)**: An effect alias `{Fiber, Concurrent}` tracking uncolored asynchronous computations.
- **`@Div` (Budget Exhaustion)**: Declares the abortive `Div::exhausted()` operation used by finite evaluation. It is an ordinary residual effect that can be handled. Possible non-termination is tracked separately and never automatically adds `@Div`.

The sub-effect lattice satisfies:

$$\emptyset \subset \lbrace\text{Fiber}\rbrace \subset \lbrace\text{Fiber}, \text{Concurrent}\rbrace \equiv \text{Async}, \quad \text{disjoint from } \lbrace\text{Div}\rbrace$$

#### Normative Rules for Built-in System Effects
- **Least-Privilege Leaf I/O Principle (`@Fiber`)**: Leaf I/O operations requiring cooperative suspension without forking child tasks MUST declare only `@Fiber`. Holding `@Fiber` does not grant authority to fork concurrent tasks (`@Concurrent`), preserving frame containment and single-fiber DRF-SC invariants.
- **Compound Asynchronous Workflows (`@Async`)**: Functions that both suspend on I/O and manage concurrent child tasks declare `@Async`.
- **Scheduling and Value Generators**: `Fiber::yield() -> ()` yields cooperatively without emitting a user value. Value-emitting streams use user-defined effects such as `eff Yield<T> { emit(T) -> () }`, with affine resumption. A resumption cannot escape its handler arm to become a pull iterator (`E0611`).

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

| System request | Source-handler discharge |
| :--- | :--- |
| `Fiber::yield` | A matching operation arm discharges this yield request |
| Leaf I/O / environmental or endpoint operation | Retains its `Fiber` obligation unless its public contract explicitly provides a handler for its result and external behavior |
| Scope / fork / join | Retains its `Concurrent` obligation; these callables are not operation-arm targets |
| `Div::exhausted` | Handled by an ordinary abortive operation arm; resumption remains forbidden |

The current resource I/O and structured-concurrency contracts provide no source-level handler that replaces their external behavior. Handling yield alone never covers these obligations. A user-defined effect may expose a mockable interface before any resource operation is invoked. Handling a request does not make an excluded operation eligible for `Div::budget` or remove its access, cleanup, or task-boundary restrictions.

```ril
-- Signature of the built-in yielding operation, not a redeclaration in user code:
eff Fiber {
    yield() -> (),                     -- Relinquishes quantum to runtime scheduler
}

-- Leaf I/O Suspension Principle (@Fiber):
fn read_socket_chunk(fd: int) @Fiber -> []u8 {
    Socket::read_chunk(fd)             -- Fixture contract: waits for this socket and returns immutable data, @Fiber
}

-- Functions declared @Fiber cannot invoke structured concurrency primitives:
fn bad_leaf_fork(fd: int) @Fiber -> []u8 {
    -- scope(\mut s -> {               -- Error [E0612]: function declares '@Fiber' but invokes unhandled '@Concurrent' primitive 'scope'
    --     s.fork(\-> Socket::read_chunk(fd))
    -- })
    read_socket_chunk(fd)
}

-- Compound Asynchronous Workflow (@Async = {Fiber, Concurrent}):
fn fetch_pipeline(url: str) @Async -> Result<str, TaskFault> {
    let raw = read_socket_chunk(80)    -- Inherits @Fiber
    scope(\mut s -> {                  -- Requires @Concurrent (present in @Async)
        let worker = s.fork(\-> parse(raw))
        let parsed = worker.join()?
        Ok(parsed)
    })
}

-- Cooperative Fiber Yielding (@Fiber):
fn cooperative_worker(count: int) @Fiber -> () {
    var c = count
    while c > 0 {
        c -= 1
        Fiber::yield()                  -- Yields execution quantum to runtime scheduler
    }
}

-- Value-Streaming Generator Composition:
eff Yield<T> {
    emit(value: T) -> ()
}

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
            collected !> Array::push(v)
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

-- Termination inference is independent of effect annotations:
fn collatz(n: int) -> int {
    if n <= 1 { 1 }
    else if n % 2 == 0 { collatz(n / 2) }
    else { collatz(3 * n + 1) }
}

-- Pure finite function; ordinary unmarked factorial would receive the same proof:
halt fn factorial(n: int) -> int {
    if n <= 1 { 1 } else { n * factorial(n - 1) }
}
-- halt fn bad_total(n: int) -> int {  -- Error [E0820]: 'halt fn' contains uncertified recursion or unbounded loop
--     collatz(n)
-- }
```

### Finite Evaluation with Div

```ril
-- Built-in operation contract, not a user redeclaration:
eff Div { exhausted() -> never }

-- Built-in callable shape; its additional finite-evaluation contract is defined below:
-- Div::budget<T>(limit: int, action: fn() @& -> T) @Div -> T

fn spin() -> int { loop {} }               -- MayDiverge, with no algebraic effects
halt fn bounded() -> ?int {
    with Div::exhausted() -> None
    with Div::budget(10_000)
    Some(spin())
}
assert(bounded() == None)

halt fn bounded_value() -> ?int {
    with Div::exhausted() -> None
    with Div::budget(10_000)
    Some(42)
}
assert(bounded_value() == Some(42))

-- The parameterized with is the ordinary final-callable application form:
halt fn explicit_budget() -> ?int {
    with Div::exhausted() -> None
    Div::budget(10_000, \-> Some(spin()))
}
assert(explicit_budget() == None)
```

The built-in `Div` namespace contains the operation `exhausted` and the finite-evaluation callable `budget`. `Div::budget` is not an effect operation and cannot be the target of a `->` handler arm (`E0621`). Its limit is an ordinary call argument, not a handler parameter pattern or a resumption value.

`Div::budget(limit, action)` creates a fresh finite-evaluation boundary and invokes `action` once when its initial allowance permits entry. Normal completion returns the action's value. At exhaustion the protected computation is irrevocably abandoned, its required finite cleanup runs, and the call requests `Div::exhausted()`. The operation has no returning continuation; any `resume` targeting it is `E0822`, before resumption-value type checking. Its answer and delimited scope use ordinary handler rules (`E0625`). The exhausted computation cannot be resumed or refilled.

```ril
fn finite_attempt() @Div -> int { Div::budget(10_000, spin) }
-- fn missing_handler() -> int { finite_attempt() } -- Error [E0612]: real residual Div effect

-- Merely installing an exhaustion handler does not limit a computation:
fn handler_only() -> int {
    with Div::exhausted() -> 0
    spin()
}                                           -- MayDiverge; spin never requests exhausted
-- halt fn still_unbounded() -> int { handler_only() } -- Error [E0820]

-- An exhaustion handler can itself diverge after the protected action ends:
fn bad_recovery() -> int {
    with Div::exhausted() -> spin()
    with Div::budget(0)
    42
}                                           -- MayDiverge, although its effect row is empty
-- halt fn invalid_recovery() -> int { bad_recovery() } -- Error [E0820]
-- with Div::exhausted() -> resume ()         -- Error [E0822]: exhaustion is non-resumable
```

#### Coverage and Finite Outcomes

- **Covered Computation (`E0822`)**: The protected invocation must be ordinary run-time Ril computation with no residual effects or outward capabilities after its internal handling and lawful local discharge. Confined mutation and temporary local environments are allowed. Termination of the action itself is not required. Actual calls, callback constituents, selected handlers, and cleanup all participate in this check; purity alone does not establish coverage.
- **Local State**: Apply the existing origin, callback-handle, and local-discharge rules. Local mutation inside the action is permitted; capturing storage does not supply missing invocation authority. An annotation cannot discharge actual outside state. The boundary neither rolls back prior writes nor authorizes additional sharing or escape.
- **Excluded Computation**: Reachable bodyless foreign calls, Fiber/I/O operations, structured concurrency, resource endpoint operations, and parallel combinators are inadmissible even if an enclosing handler removes their residual effect label. Ordinary finite language primitives and sequential collection computations follow their normative finite contracts. A primitive without a finite contract must expose its repeated computation to the charging rules or is inadmissible.
- **Callable Dependencies**: Budget eligibility follows actual callable values through aliases, fields, returns, and modules. Symbolic callable parameters retain coverage constraints; incompatible or unresolved actual coverage at a required use is `E0822`. Closing a higher-order function's effect/capability rows alone cannot certify an arbitrary external callback as covered.
- **Handler Boundary**: The budget callable's own `Div` obligation is outside its protected action. It uses the exhaustion handler selected for that invocation by ordinary handler-selection rules. Installing another exhaustion handler inside the action cannot intercept the enclosing boundary's exhaustion. Other effects, capabilities, and termination conditions introduced by recovery remain caller obligations.
- **Termination Conclusion**: After finite evaluation of the explicit arguments, a valid budget boundary performs finite protected computation. The whole handled expression is `Finite` only if its required cleanup and recovery computation are finite too. An unhandled `Div` operation retains both its ordinary effect obligation and the chosen handler's termination condition. A `halt` caller must discharge all of them.
- **Latent Computation**: A budget's allowance belongs to its dynamic invocation and never escapes inside a callable. Returning an action does not certify its later execution. Explicitly invoking `Div::budget` inside a later action creates a new boundary then; it does not recover an old allowance.
- **Static Domain**: `Div::budget` is a run-time built-in, not a meta/type helper. Existing call-family restrictions (`E0810`) apply. Static evaluation retains its own budget and `E0811`.

#### Allowance and Charging

The limit has type `int`. Evaluate it and the action expression once, before establishing the new boundary, in ordinary argument order. A negative limit panics before invoking the action; zero abandons the call without invoking the action and requests exhaustion. Argument evaluation is not protected by the new boundary, so its purity and termination still require their own checks. These evaluations remain covered by any already active outer boundary.

| Charged event while a boundary is active | Cost |
| :--- | :--- |
| Ordinary function or anonymous-callable entry, including the protected action | One unit before entering its body |
| Each loop iteration | One unit before evaluating its condition/next-element test and possible body; `next` cannot skip this event |
| Each effect-handler entry and each `resume` | One unit before executing the arm or continuing the computation |
| Entry to an inner `Div::budget` | One unit to existing outer boundaries, before creating the inner allowance |
| Finite primitive operation | No additional charge beyond its specified callable entry, if any |
| Other finite expression steps | No additional charge |

These are abstract language events, including source-level calls eliminated by an equivalent evaluation strategy. Every possible infinite execution path within eligible computation must encounter unboundedly many charged events; no uncharged primitive can conceal such a path. Sequential built-in combinators charge each callback entry and iteration under their specified sequential behavior. Installing a handler alone executes no operation; handler code runs only when its operation is requested.

Before a charged event, if any active boundary has no remaining units, do not execute the event; exhaust the outermost such boundary. Otherwise subtract one unit from every active boundary and execute the event. Consuming the last unit does not itself interrupt the event; a later charged event triggers exhaustion. Inner boundaries never replenish, hide, or suspend outer allowances during ordinary computation. An inner handler cannot intercept exhaustion owned by an outer boundary.

| Cleanup and allowance | Rule |
| :--- | :--- |
| Eligibility | Cleanup independently finite (`E0617`) |
| Entry | Suspend allowances already active; exhaustion cannot skip or repeatedly interrupt cleanup |
| Budget created inside cleanup | Its own allowance remains active |
| Exit | Restore surviving outer allowances, including for recovery handlers |
| Unwinding | LIFO, EffectAborted, and double-fault rules remain in force; no rollback |
| Limit | Counts protected events; excludes total cleanup/recovery work and wall-clock time |

```ril
fn one() -> int { 1 }
halt fn zero_allowance() -> ?int {
    with Div::exhausted() -> None
    with Div::budget(0)
    Some(1)
}
halt fn one_entry() -> ?int {
    with Div::exhausted() -> None
    Some(Div::budget(1, one))          -- The action entry consumes the one unit
}
assert(zero_allowance() == None)
assert(one_entry() == Some(1))
halt fn negative_allowance() -> ?int {
    with Div::exhausted() -> None
    Some(Div::budget(-1, one))
}
-- negative_allowance()             -- Panics before invoking one; exhaustion handler is not requested

halt fn nested_limits() -> ?int {
    with Div::exhausted() -> None
    with Div::budget(2)
    with Div::exhausted() -> Some(99)
    with Div::budget(100)
    Some(spin())
}
assert(nested_limits() == None)       -- Outer exhaustion bypasses the inner arm

halt fn make_later() -> (fn() -> int) {
    with Div::exhausted() -> one
    with Div::budget(100)
    spin
}
-- halt fn run_later() -> int { make_later()() } -- Error [E0820]: no escaped budget

-- A separate .d.ril fixture declares: pub fn foreign_work() -> int
-- with Div::exhausted() -> 0
-- with Div::budget(100)
-- foreign_work()                    -- Error [E0822]: external computation is not covered
```

```ril
-- The limit expression runs before its own budget becomes active:
-- halt fn bad_limit_expression() -> int {
--     with Div::exhausted() -> 0
--     Div::budget(spin(), one)
-- }                                 -- Error [E0820]: computing the limit may diverge

fn budgeted_action(action: fn() -> int) -> ?int {
    with Div::exhausted() -> None
    with Div::budget(100)
    Some(action())
}
assert(budgeted_action(spin) == None)  -- Eligible divergence is bounded
-- budgeted_action(foreign_work)     -- Error [E0822]: forwarding cannot conceal uncovered code

halt fn handler_work() -> ?int {
    with Div::exhausted() -> None
    with Div::budget(100)
    with ReadConfig::get() -> resume spin()
    Some(ReadConfig::get())
}
assert(handler_work() == None)        -- Executed user-handler computation also consumes the budget

halt fn limited_sum(values: []int) -> ?int {
    with Div::exhausted() -> None
    with Div::budget(100)
    var total = 0
    for values as value { total += value }
    Some(total)
}
assert(limited_sum([1, 2, 3]) == Some(6)) -- Confined mutation remains admissible

type Guard = { on_close: fn() -> () }
halt fn cleanup_before_recovery() -> ?int {
    with Div::exhausted() -> None
    with Div::budget(100)
    let scoped guard = Guard.{ on_close: \-> panic("cleanup fault") }
    loop {}
}
-- cleanup_before_recovery()         -- Finite DoubleFaultFatal: cleanup panics during budget abort; no None recovery
-- A budget cannot legalize divergent cleanup:
-- let scoped bad = Guard.{ on_close: \-> { loop {} } } -- Error [E0617]

-- with Div::exhausted() -> ()
-- with Fiber::yield() -> resume ()
-- with Div::budget(100)
-- Fiber::yield()                     -- Error [E0822]: excluded operation, even with an outer handler
```

### Structured Concurrency and Panic Containment

```ril
use ril/concurrent::{scope, TaskFault}
fn isolated_value() @Concurrent -> Result<int, TaskFault> {
    scope \mut s -> {
        let task = s.fork(\-> 42)
        task.join()
    }
}
```

Task boundaries enforce the language's ordinary permission, provenance, effect, and termination judgments. In particular, outside mutable/live ordinary data and indirect outside access cannot cross a task boundary (`E0601`); an immutable function descriptor does not erase its callable obligations. Residual user effects and Div exhaustion require child-local handlers (`E0615`). Scope/task authority cannot escape its owner or be concealed in aggregates (`E0606`). Result inspection duties survive task packaging and joining (`E0720`).

A child panic may become a Result at its owning structured boundary. Synchronous frames cannot catch panics. Child barriers constrain lifetimes without proving that arbitrary child computation terminates.

### Deterministic Data Parallelism and Divide-and-Conquer Primitives

```ril
use ril/parallel
halt fn square_all(numbers: []f64) -> []f64 {
    numbers |> Parallel::map(\x -> x * x)
}
-- @Parallel is not an effect annotation (E0620).
```

Parallel invocation requires no residual effects and independently established finite computation; empty effect rows alone are insufficient (`E0820`). Outside mutable/live/resource dependencies, including those hidden in handlers or cleanup, are rejected (`E0605`), except the explicitly lent disjoint regions admitted by a concrete library operation. Overlapping or unproved-disjoint write/read or write/write regions are `E0619`. Checks are transitive; a distinct name, index, or copied graph path is not evidence of independence. Handling Div exhaustion alone does not establish finiteness. No live authority may escape the invocation.

The ordinary `numbers: []f64` parameter already requires deeply immutable data. Existing live data must be copied before this call; `ref` observation alone does not satisfy a pure parallel input.

Parallel reference evaluation determines result order and observable faults. Double faults in branch-local cleanup use the same visibility rule. Permitted writes remain confined to their explicitly lent regions.

### Structured Concurrency Channels

```ril
use ril/concurrent/channel
-- Invocation fixture in the owning scope with exclusive receiver authority:
let ticket = Channel::detach(mut rx)
-- rx !> Channel::recv()               -- Error [E0603]: authority was transferred
-- clone(ticket)                      -- Error [E0530]: detached authority cannot be duplicated
```

Channel payloads admit immutable ordinary data or explicitly detached resource descriptors (`E0602`), not implicit transfer of a `mut`/`^mut` authority. Endpoint/ticket use respects its one-task and transfer permissions (`E0603`); scope escape is `E0606`. Clone and derive eligibility inspect nested constituents (`E0530`, `E0536`). Result inspection obligations follow actual payloads and aliases; inspecting transport success does not inspect a nested Result (`E0720`).

A resource contract must state endpoint creation, cloning, transfer, closure, and cancellation permissions. Endpoint-specific permissions do not authorize copying or transferring ordinary writable graphs or unrelated opaque resources.



## Compile-Time Computation and Totality

### Static Type Values and Type Quotation

```ebnf
TypeQuoteExpr    ::= "<" TypeExpression ">"
TokenType        ::= "Type" [ "<" TypeExpression ">" ]
TypeFunctionExpr ::= "\" TypeFnParam { "," TypeFnParam } "->" Expression
TypeFnParam      ::= StaticKeyParamDecl
                  | PascalCase [ ":" TypeSort ] [ "=" TypeExpression ]
                  | SnakeCase ":" TypeExpression [ "=" Expression ]
```

`TokenType` is the protected intrinsic family resolved through `NominalRef`. A quote is a value expression, never a type annotation. Its root must denote one type, not a type-function program; stripping grouping parentheses cannot bypass that requirement (`E0306`). Existing const, `typeof`, and mapped-type expression slots keep their rules.

| Position | Spelling / meaning |
| :--- | :--- |
| Type declaration / data annotation | `type User = { id: int }`, `x: User`; direct type syntax |
| Static type value | `<User>`, `<int>`, `<{ id: int }>` |
| Tuple / unit token | `<(T, U)>`, `<()>`; reuse ordinary tuple grammar |
| Generic application | `F<T, U>`; two arguments, not a tuple quote |
| Type pattern | `<Option<let U>>`; pattern-only binders/rests |
| Token type | `Type` hides the target; `Type<T>` guarantees exactly T |
| Type-parameter sort | `T: Type`; distinct from a value parameter `token: Type` |
| Existing values | `Marker` remains a singleton and `UserId` a constructor; their types use `<Marker>` / `<UserId>` |

The following local bindings are fragments of static type-function evaluation:

```ril
type User = { id: int, name: str }
let exact = <User>                     -- Type<User>, not Type
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
```

| Token typing | Rule |
| :--- | :--- |
| Default binding | `let` and `var` preserve `Type<T>`; completion must not silently widen to `Type` |
| Exact target | `Type<A>` matches `Type<B>` only when A and B are definitionally equal; target subtyping is insufficient |
| Widening | `Type<T>` may enter an explicitly general `Type` context without changing the represented target |
| Immutability | Tokens are atomic immutable static values; `var` changes the selected token, not its target type |
| Described schema | Preserve nominal/opaque identity, member modes, and callable contracts; immutable token reception suppresses none of them and grants no object authority |
| Equality | Any two tokens support `==` / `!=` by target definitional identity, including different exact metatypes; no ordering (`E0327`) |
| Kind | Static generics may admit meta-value types; materializing them at run time remains prohibited |

```ril
-- Static fixture; User has the preceding schema.
let exact: Type<User> = <User>
let wide: Type = exact
assert(wide == exact)
-- let wrong: Type<int> = <never>       -- Error [E0301]: never being a subtype of int does not make targets equal
var fixed = <int>                      -- Type<int>
fixed = <int>
-- fixed = <str>                      -- Error [E0301]: no retroactive widening

meta fn target_size<T>(token: Type<T>) -> int { byte_size(token) }
meta fn object_size<T>(value: T) -> int { byte_size(<T>) }
meta fn value_type_name<T>(value: T) -> str { type_name(<T>) }
meta fn field_size<T: { ..R }, K: keyof T>(token: Type<T>, key: K) -> int {
    byte_size(<T.(K)>)
}
var selected: Type = <User>
let first_size = field_size(selected, "id") -- Proved current target: T = User, K = "id"
selected = <int>
-- let bad = field_size(selected, "id") -- Error [E0301]: current target fails the record constraint
assert(first_size >= 0 && byte_size(selected) >= 0)
-- let bad = object_size(<User>)        -- Error [E0306]: Type<User> has no ordinary run-time layout
```

| Inference at a use | Required evidence |
| :--- | :--- |
| `value: T` | Infer the argument's own checked value type: a token yields `Type<User>` or `Type`, never User |
| `token: Type<T>` | Bind T from exact token typing or a proved current static target; then validate structural/kind constraints |
| `key: K`, `K: keyof T` | Bind the static key value, then check membership against the determined target T |
| General `Type` | It alone proves no target; do not invent T from desired fields or a key. A current static value, pattern, or explicit type-function evaluation can supply evidence |
| Assignment / join | Invalidate stale slot/path proofs; preserve only guarantees common to retained alternatives until static evaluation selects one |
| Unresolved proof | Defer dependent checks until the required static evaluation; unproved target information is `E0344`, a non-static argument is `E0814`, and a proved incompatible target keeps `E0301` |

Target evidence checks a token against `Type<T>`; it never converts the token into an ordinary T value. `typeof e` checks names, types, and permissions without evaluating e or producing effects, writes, or environments.

```ril
type Resolve = \token: Type -> token
type Wrap = \token: Type -> <{ field: Resolve<token> }>
type Nullable = \T -> <?T>
type PairOf = \T, U -> <(T, U)>

type IntNullable = Nullable<int>
type StringIntPair = PairOf<str, int>
type WrappedInt = Wrap< <int> >        -- Token value argument, not an implicit type argument

-- Static fixture:
var chosen: Type = <int>
let before = Wrap<chosen>              -- Type<{ field: int }>
chosen = <str>
let after = Wrap<chosen>               -- Type<{ field: str }>; before is unchanged
```

Type functions retain their anonymous form and contextual type-producing result; no ordinary function return annotation is added. `Resolve` receives a static token by value; instance keys use target identity at argument evaluation, not a slot or later contents. Token variables and results of permitted type-function calls already are values and need no extra quote; this grants no new call-family permission. A token's value name is not type syntax: compose through a type function instead of silently unquoting.

| Angle context | Deterministic parsing |
| :--- | :--- |
| Prefix `<T>` | Primary type quote; no top-level comma list. `<(T, U,)>` uses existing tuple rules; `<(T,)>` remains invalid |
| Expression `QName<...>` | Commit to generic application only when the resolved declaration or preserved item/constructor alias supplies an application signature; otherwise `<` is infix comparison |
| `F<T, U>` / `fn f<T, U>` | Generic argument / parameter lists; the declared parameter category controls checking |
| `F< <T> >` | Explicit token value argument; keep `<<` as shift, so adjacent opening angles need separation |
| Expected angle closure | Consume one original `>` character, then rescan the remainder: `<Box<T>>`, `<Type<T>>`, `<T>==<U>`, `type A<T>=T` |
| Ordinary operators | `>=`, `>>`, and `>>=` retain their normal meanings outside an expected closure |
| Const / `typeof` angle operations | Parenthesize: `Flag<(n > 0)>`, `Buffer<u8, (1 << n)>`, `<typeof (a > b)>` |
| Pattern quote | Use the type-pattern extension, including `let U` and rests; those binders are not expression syntax |

Resolve declaration-header/application metadata before committing an expression's postfix generic list; never choose the parse by testing operand types, constraints, or current variable contents. A named non-generic callable has an empty generic signature, so explicit arguments retain `E0340`. Type syntax, type patterns, and generic parameter declarations keep their own list productions; embedded expression slots use the expression rule. No post-commit backtracking is performed.

An empty quote or top-level comma is `E0120`; missing/mismatched committed delimiters retain `E0122` / `E0123`. `Type<T, U>` is arity error `E0340`. `Type` is not `any` and grants no phase-polymorphic call privilege.

```ril
fn comparisons(a: int, b: int, c: int, d: int) -> bool { a < b && c > (d) }
fn choose<flag: bool>(value: int) -> int { if flag { value } else { 0 } }
assert(comparisons(1, 2, 4, 3))        -- a is an ordinary value parameter, not a generic declaration
assert(choose<true && false>(4) == 0) -- Known declaration; const argument need not add parentheses for &&
-- let bad = comparisons<int>(1, 2, 4, 3) -- Error [E0340]: known callable has no generic parameters
```

### Pure Type Functions and Type Return Privilege

```ril
halt type SafeRecord = \T ->
    if <T> == <int> { <{ val: int, valid: bool }> }
    else { <{ val: T, valid: bool }> }
type IntRecord = SafeRecord<int>
```

```ril
halt type Identity = \T -> <T>              -- OK: type-producing function
meta fn size_of<T>(t: Type<T>) -> int { byte_size(t) } -- OK: reflection produces an ordinary value
halt fn checked_increment(n: int) -> int { n + 1 } -- May panic at int's maximum
-- halt fn yield_once() @Fiber -> () { Fiber::yield() } -- Error [E0821]: halt requires outward purity
-- halt fn forever() -> () { loop {} }                  -- Error [E0820]: uncertified local loop
-- meta let BAD_SUM = 127i8 + 1i8                 -- Error [E0831]: panic during static evaluation
```

| Static definition | Result / restriction |
| :--- | :--- |
| Type declaration/function | Type functions produce one type token under the declaration's anonymous-function context; no ordinary result annotation. Effects/capabilities forbidden (`E0335`) |
| `meta fn` result | Ordinary value free of tokens and type-producing capabilities; reject after generic instantiation (`E0812`). Effect/state annotations remain forbidden (`E0813`) |
| `meta fn` reflection | May inspect immutable tokens and quote given type syntax, including anonymous shapes; cannot mutate described types or expose a type-producing result API |
| `meta let` | May hold static tokens; only recursively token-free ordinary results can become run-time constants |
| Run-time materialization | Reject tokens and static-only metatypes in materialized value parameters/results, storage, and captures (`E0816`), including through aliases, generics, and opaque wrappers; static generic metadata is excluded |

Both run with empty effect/capability domains. Local bindings, control flow, pure static helpers, and recursion remain supported. Types used as generic metadata stay static; no run-time type token, witness, or phantom value is passed.

```ril
meta fn record_bytes() -> int { byte_size(<{ id: int }>) }
meta fn meta_identity<T>(value: T) -> T { value }
meta let NUMBER = meta_identity(1)
-- meta let BAD_TOKEN = meta_identity(<int>) -- Error [E0812]: instantiated result is Type<int>
-- meta fn leak<T>(token: Type<T>) -> { token: Type<T> } { .{ token: token } }
-- Error [E0812]: wrapping does not remove the returned token

meta let TOKEN = <int>
meta let SIZE = byte_size(TOKEN)
fn runtime_size() &up(sub){SIZE} -> int { SIZE }
fn runtime_client(value: int) -> int {
    -- let token = <int>              -- Error [E0816]: ordinary execution cannot materialize a token
    value
}
-- fn leak_constant() &up(sub){TOKEN} -> Type<int> { TOKEN } -- Error [E0816]: no run-time token values
-- fn leak_shape(value: { token: Type }) -> () {} -- Error [E0816]: nested token type in a run-time parameter
```

Phase checks inspect the entire instantiated result/value graph, opaque summaries, captured environments, and latent type-producing callable contracts. Inlining, wrappers, or generic names cannot erase the boundary. A computation that has reduced to ordinary constants without tokens or type-producing authority may cross as ordinary data. A bare `<T>` value expression at run time is `E0816`; forbidden calls retain `E0810`.

Apply [Termination and halt Contracts](#termination-and-halt-contracts) to symbolic computation as well. All meta/type functions retain finite or possibly non-terminating judgments even though their effect and capability domains are empty. `halt type` requires finite symbolic computation, including every reached helper; invalid input or static defects may still fail. Uncertified `halt` computation is `E0820`; type/meta annotation prohibitions retain `E0335`/`E0813`.

Unmarked static loops and recursion remain admissible subject to the static-evaluation budget. Exhaustion rejects that evaluation (`E0811`); it does not certify the underlying definition as terminating. Certified static computations consume the same budget. The run-time `Div` effect is not involved, and `with Div::exhausted()` cannot intercept a static-evaluation diagnostic.

| Static evaluation | Budget / failure |
| :--- | :--- |
| Each root evaluation | Configured positive budget, including certified computations |
| Meta/type function entry, static callback entry, loop iteration | Consume one unit each |
| Next charged step with no budget | `E0811` |
| Alias cycle | Separate `E0313` check |
| Failed `assert` / other panic | Static `E0830` / `E0831` |

- **Custom Diagnostics and Static Panic (`panic`, `E0831`)**: Type functions, pipeline guards, and meta evaluation blocks may emit developer-specified diagnostics with `panic(message)`. Its `never` result fits any expected branch result, including a type-producing branch. Static panic stops evaluation with `E0831: StaticEvaluationPanicError`, attributed to the triggering instantiation; no run-time unwinding occurs.

```ril
-- Custom diagnostic in pure type function via static panic:
type SizedRecord = \T -> match <T> {
    <{ id: int, ..let _ }> -> <T>,
    _ -> panic("SizedRecord requires a record containing an 'id: int' field"),
}
-- type BadRecord = SizedRecord<str> -- Error [E0831]: panic during static evaluation: SizedRecord requires a record containing an 'id: int' field
-- Meta helper: ordinary value computation only (returns int, not a type token)
meta fn pad_align(size: int, align: int) -> int {
    assert(size >= 0 && align > 0 && (align & (align - 1)) == 0)
    (size + align - 1) & ~(align - 1)
}

-- Meta predicate consuming read-only type token (parametric generic, strictly no 'any'):
meta fn is_compact<T>(t: Type<T>) -> bool {
    byte_size(t) <= 16                         -- OK: inspects shape, returns value bool
}

-- Type functions provide type-producing interfaces; meta helpers return ordinary values.
halt type PaddedBuffer = \raw_size: int, T -> {
    let actual_size = pad_align(raw_size, 8)   -- OK: consumes meta fn value output
    if is_compact(<T>) {                   -- OK: consumes meta predicate
        <{ inline_data: []T, len: int }>   -- OK: constructs shape
    } else {
        <{ heap_ptr: int, cap: int }>      -- OK: constructs shape
    }
}

type FastBuf = PaddedBuffer<64, u8>            -- Resolves to { inline_data: []u8, len: int }

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

### Disjoint Call Families, Evaluation Budgets, and Branch Pruning

```ril
fn runtime_identity(value: int) -> int { value }
-- meta let INVALID_CALL = runtime_identity(1) -- Error [E0810]: run-time fn in static evaluation
```

`E0810` diagnoses a forbidden call across the specified evaluation families. `E0814` diagnoses a run-time value where a static value is required, including const arguments and static-key arguments. Wrong sorts retain `E0323`; a known negative static value is `E0815`. Direct record access with a dynamic computed key retains `E0324`, rather than the argument-oriented static-key diagnostic.

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
| Type function | Other type functions and `meta fn`; no run-time `fn` (`E0810`) |
| Meta value evaluation | `meta fn`, static reflection, and listed dual-phase operations; no ordinary run-time `fn` or direct type-function value call (`E0810`) |
| Run-time value evaluation | No type-function or meta-function value invocation (`E0810`) |
| Both phases | Pure arithmetic/comparison, `len`, `assert`, and library operations explicitly declared dual-phase |

Type elaboration in declarations, annotations, quoted type syntax, and static type metadata remains static even inside an ordinary `fn`. Type-function evaluation there is not a run-time value call. Local type quotations and read-only reflection in meta code grant no token-result interface to `meta fn`.

Static callbacks capture symbolic constants. Mutable resources, handlers, and ordinary run-time calls have no phase-polymorphic exception. Static budget exhaustion is `E0811`.

| Condition | Invocation effects, state, escape, authority use |
| :--- | :--- |
| Static condition (boolean or pattern arm) | Selected branch only |
| Run-time condition | Both branches' possible obligations |

Both branches still obey syntax, name resolution, and ordinary type compatibility. Type tokens expose no callable-value effects/provenance; no built-in `is_pure` exists.
### Unified Tripartite Introspection

Ril unifies compile-time introspection across all three composite data forms (Records, Sum Types, Tuples) under a single operator pair: `keyof T` and constituent projection `T.(K)`.

```ebnf
MappedRecordType ::= "{" [ MemberMode ] "[" PascalCase "in" Expression "]" ":" TypeExpression "}"
MappedTupleType  ::= "(" [ MemberMode ] "[" PascalCase "in" Expression "]" ":" TypeExpression ")"
```

#### Universal Coordinate Indexing
In expression and meta contexts, `keyof T` queries the coordinate index set of composite type $T$:
- **Records**: Evaluates to an immutable array `[]str` of field names sorted strictly in UTF-8 byte order.
- **Sum Types (ADTs)**: Evaluates to an immutable array `[]str` of variant constructor names sorted strictly in UTF-8 byte order.
- **Tuples**: Evaluates to an immutable array `[]int` of positional indices `[0, 1, ..., n-1]` in monotonic ascending order.
- **Leibniz Invariance**: Canonical sorting guarantees that structurally equivalent types produce identical coordinate index arrays ($T_1 \equiv T_2 \implies \text{keyof } T_1 \equiv \text{keyof } T_2$).


#### Static Key Parameters and Computed Value Projection

```ril
fn get_field<T: { ..R }, K: keyof T>(record: T, key: K) -> T.(K) {
    record.(key)
}
type User = { id: int, name: str }
let user = User.{ id: 1, name: "Ada" }
let name: str = get_field(user, "name")
-- get_field(user, "missing")          -- Error [E0323]: key is not in keyof User
fn dynamic_key(user: User, key: str) -> () {
    -- get_field(user, key)             -- Error [E0814]: actual key is not statically known
}
```

- `K: keyof T` is a static string key for records/sums, or an integer tuple position; it is not a run-time literal type.
- `key: K` requires an argument statically equal to K and permits inferring K from it. Both names denote that key in the body.
- K is not an ordinary data type: `[]K` is `E0301`. Check membership after inference (`E0323`); unknown run-time keys are `E0814`.

| Value projection | Requirement |
| :--- | :--- |
| `record.(key)` / `record.("name")` | Static key; preserve reference permissions/origins; bracket indexing is `E0324` |
| Tuple | Static positional index; excluded by the example's record constraint |
| Sum payload | `match` or variant narrowing; membership in `keyof S` alone supplies no value-level product projection (`E0337`) |

An immutable run-time string is not a static key. Sum type keys describe possible payload shapes, not fields present in every value.

#### Universal Constituent Projection
For a composite type $T$ and coordinate key $K \in \text{keyof } T$, `T.(K)` statically projects the corresponding constituent shape, subject to the GADT equation check below:
- **Records**: `User.id` or `User.("id")` resolves to the declared field type.
- **Sum Types**: `UiEvent.Click` or `UiEvent.("Click")` resolves to the variant payload type under Constructor-Tuple Equivalence:
  - Multi-field variants ($n \ge 2$): Resolves to anonymous product tuple `(T1, ..., Tn)`.
  - Single-field variants ($n = 1$): Resolves to scalar type $T_1$ (Ril strictly has no 1-tuples).
  - Unit constructors ($n = 0$, declared `Variant()`): Resolves to unit `()`.
   - Nullary tags (declared `Variant`): Resolves to unit `()` as its injection domain.
- **Tuples**: `Pair.0` or `Pair.(0)` resolves to the component type at positional index $K$.

```ril
type Box<T> { Item<U>(U) -> Box<U> }
type ItemType = Box<int>.Item          -- int: U is recovered from Box<int>
type Expr<T> { Int(int) -> Expr<int>, Bool(bool) -> Expr<bool> }
type IntPayload = Expr<int>.Int       -- int
-- type WrongPayload = Expr<int>.Bool -- Error [E0301]: incompatible constructor result equation
```

Sum `keyof` lists declared variant names even when a supplied index excludes a variant. A GADT payload projection must satisfy the selected constructor's result equation under the existing constraints and recover each variant-local parameter. An incompatible or unresolved equation is `E0301`. Projection introduces no new ambient type equality; membership in `keyof` alone does not prove that a variant is possible.

#### Symmetrical Mapped Comprehensions
- **Mapped Records**: `{ [K in Expr]: TypeExpr }` requires static `[]str`; integer keys are `E0341`. Duplicate/invalid labels are `E0210`/`E0102`; ADT tables may use PascalCase constructor labels.
- Mapped members default to immutable; an explicit `MemberMode` applies to every generated member. `T.(K)` projects the member's data type, not its binding mode. Records and sums use the same mapping form:
  ```ril
  -- Generic visitor / handler table valid for BOTH records and sum types:
  type SchemaTable = \T -> <{
      [K in keyof T]: T.(K)
  }>
  ```
- **Mapped Tuples (`( [I in Expr]: TypeExpr )`)**: `Expr` MUST evaluate to compile-time `[]int`. Supplying `[]str` triggers `E0342: InvalidTupleKeySortError`.
- **Single-Element Tuple Prohibition (`E0343`)**: A mapped tuple comprehension evaluated over an index array of length 1 is statically rejected at compile time, preserving the invariant that Ril has no 1-tuples.

```ril
type Readonly = \T -> <{ [K in keyof T]: T.(K) }>
type Bag = { mut items: []int }
type FixedFields = Readonly<Bag>        -- { items: []int }; default member is deeply immutable
type Box = { var tag: int, mut bag: FixedFields }
let mut box = Box.{ tag: 0, bag: FixedFields.{ items: [1] } }
box.tag = 1
-- box.bag.items !> Array::push(2)    -- Error [E0520]: a default member blocks nested writes
type Slots = \T -> <{ var [K in keyof T]: T.(K) }>
type PairSlots = (var [I in [0, 1]]: int) -- (var int, var int)
```

`Readonly` constructs default-member schemas. Ordinary `let` already removes effective member permissions recursively; neither operation changes callable invocation contracts.

```ril
-- Records:
type User = { id: int, name: str, active: bool }
meta let USER_KEYS: []str = keyof User         -- ["active", "id", "name"] (UTF-8 sorted)
type UserId = User.id                          -- int
type UserName = User.("name")                  -- str

type Pick = \T, included: []str -> {
    let valid_keys = keyof T |> Array::filter(\k -> included |> Array::contains(k))
    <{ [K in valid_keys]: T.(K) }>
}
type PublicUser = Pick<User, ["id", "name"]>   -- { id: int, name: str }

-- Sum Types (ADTs):
type UiEvent {
    Click({ x: int, y: int }),
    Hover(int, int),
    Focus,
}
meta let EVENT_KEYS: []str = keyof UiEvent     -- ["Click", "Focus", "Hover"] (UTF-8 sorted)
type ClickPayload = UiEvent.Click              -- { x: int, y: int }
type HoverPayload = UiEvent.("Hover")          -- (int, int)
type FocusPayload = UiEvent.Focus              -- () (nullary injection domain)

type EventHandlerTable = \T, R -> <{
    [K in keyof T]: fn(T.(K)) -> R
}>
type UiHandlerTable = EventHandlerTable<UiEvent, ()>
-- { Click: fn({ x: int, y: int }) -> (), Focus: fn(()) -> (), Hover: fn((int, int)) -> () }

-- Tuples:
type Pair = (int, str)
meta let PAIR_KEYS: []int = keyof Pair         -- [0, 1]
type First = Pair.0                            -- int
type Second = Pair.(1)                         -- str

-- Canonical Tuple Reversal via array pipeline:
halt type ReverseTuple = \T -> {
    let rev_indices = keyof T |> Array::reverse
    <(
        [I in rev_indices]: T.(I)
    )>
}
type ReversedPair = ReverseTuple<Pair>         -- (str, int)

-- Rejection of Invalid Mapped Comprehensions:
-- type BadRecordKeys = { [K in [0, 1]]: int } -- Error [E0341]: mapped record comprehension requires '[]str' keys, found '[]int'
-- type BadTupleKeys = ( [I in ["a", "b"]]: int ) -- Error [E0342]: mapped tuple comprehension requires '[]int' keys, found '[]str'
-- type Bad1Tuple = ( [I in [0]]: int )       -- Error [E0343]: mapped tuple comprehension produced single-element tuple (Ril strictly has no 1-tuples)
```

### Structural Type Pattern Matching

Static tokens use the ordinary `MatchExpr`, with any token-valued expression as subject. Type patterns match its represented type; they are not run-time type tests. Bare literals inside a type pattern remain limited to const-argument positions.

```ebnf
TypePattern      ::= "<" TypePatternInner ">"
TypePatternInner ::= RigidNominalPattern | TypeTuplePattern | TypeRecordPattern
                   | TypeArrayPattern | TypeMapPattern | PrimitivePattern | LiteralPattern | "_" | "let" ( PascalCase | "_" )
RigidNominalPattern ::= QualifiedName [ "<" TypePatternInner { "," TypePatternInner } [ "," ] ">" ]
PrimitivePattern ::= PrimitiveType
TypeArrayPattern ::= "[" [ Expression ] "]" TypePatternInner
TypeMapPattern  ::= "[" TypePatternInner ":" TypePatternInner "]"
TypeRecordPattern ::= "{" [ TypePatternField { "," TypePatternField } [ "," TypeRestPattern ] [ "," ] ] "}"
TypePatternField ::= [ MemberMode ] FieldLabel ":" TypePatternInner
TypePatternMember ::= [ MemberMode ] TypePatternInner
TypeTuplePattern ::= "(" ")" | "(" TypePatternMember "," ( TypeRestPattern | TypePatternMember { "," TypePatternMember } [ "," TypeRestPattern ] [ "," ] ) ")"
TypeRestPattern ::= ".." "let" PascalCase
```

- **Scoped Pattern Variables (`let U`)**: A `let U` binder inside `<P>` introduces an immutable target-type variable scoped strictly to the arm's guard and RHS. `U` MUST be `PascalCase` (`E0101`); it alone proves no record structure or fields.
- **Member Modes**: Structural type patterns match declared member modes exactly; omission means the default mode. Row/tuple rests preserve remaining member modes. The `let U` type-variable binder is not a member modifier and remains explicit.
- **Linearity Invariant**: Pattern variables MUST be linear; repeating the same identifier within a pattern branch is statically rejected (`E0347: DuplicatePatternBindingError`). Multi-position equality is asserted via explicit guards (`if <A> == <B>`).
- **Tuple Rest**: A type-pattern rest is a tuple type of the remaining components; an empty rest is unit. A one-component rest cannot form a tuple and fails that pattern, allowing the next arm to match. It is not silently coerced to its component type.
- **Rigid Application Head (`E0306`)**: Require a known rigid type constructor; no head binding or inverse type-function matching. Transparent aliases may expand. Primitive/structural patterns and whole-type `_`/`let U` remain legal.

| Match evidence | Scope / invalidation |
| :--- | :--- |
| Subject evaluation | Evaluate once and match that token snapshot, including a variable or type-function result |
| `<User>` arm | Matched value is `Type<User>`; named source paths retain the fact only while unchanged |
| `<let U>` arm | Snapshot is `Type<U>`; U remains the original target even if a source slot is reassigned |
| Structural arm | Restore only the member/mode/identity facts actually proved by that pattern |
| Assignment / alias write | Invalidate affected source-path evidence; a fresh current static target may prove different facts |

```ril
-- User and field_size have the preceding contracts.
meta fn inspect_wide(token: Type) -> int {
    match token {
        <User> -> field_size(token, "id"),
        _ -> 0,
    }
}
meta let _ = {
    var selected: Type = <User>
    match selected {
        <let U> -> {
            let snapshot = <U>
            selected = <int>
            assert(snapshot == <User>)
            -- let stale = field_size(selected, "id") -- Error [E0301]: U does not retarget with selected
        },
    }
}
```

```ril
-- Deep Recursive Unwrapping of Container / Fallible Types:
type UnwrapAll = \T -> match <T> {
    <Result<let OkVal, let _>> -> UnwrapAll<OkVal>,
    <Option<let SomeVal>>      -> UnwrapAll<SomeVal>,
    _                              -> <T>,
}

-- Element Extraction from Collections:
halt type ElementOf = \T -> match <T> {
    <[]let E>        -> <E>,
    <Set<let E>>     -> <E>,
    <[let _: let V]> -> <V>,
    _                    -> <never>,
}

-- Tuple Destructuring:
halt type DeconstructTuple = \T -> match <T> {
    <(let Head, ..let Tail)> -> <{ head: Head, tail: Tail }>,
    _                            -> <never>,
}

type Nested = Option<Result<int, str>>
type Unwrapped = UnwrapAll<Nested>             -- int
-- UnwrapAll uses the evaluation budget: recursive type graphs need not have a finite wrapper depth.
type Elem = ElementOf<[]str>                   -- str
type HeadTail = DeconstructTuple<(u8, i32, f64)>-- { head: u8, tail: (i32, f64) }

-- Rejection of Non-Rigid Type Patterns (E0306):
-- type BadPattern = \T -> match <T> {
--     <(let M)<let U>> -> <U>,         -- Error [E0306]: rigid type pattern cannot bind constructor '(let M)' as a higher-kinded pattern variable
--     _                    -> <never>,
-- }
```

### Static Parameter Sorts and Adaptation Rules

Type functions accept the following parameter sorts and constraints:

- **Bare Types (`\T` or `\T: Type`)**: Accepts static type expressions. Unannotated parameters default to sort `Type`.
- **Const Values (`\param: ValueType`)**: Accepts compile-time known values (literals, `meta let`, statically foldable expressions), including `token: Type` / `token: Type<T>`. Passing runtime variables raises `E0814`. Token arguments are copied at argument evaluation and compared by target identity.
- **Bounded Structural Types (`\T: { id: int, ..R }`) and Static Keys (`\K: keyof T`)**: Structural bounds constrain types; keyof bounds constrain static key values. These are distinct sorts even though both use PascalCase binders.
- **Higher-Kinded Constructors (`\M: Type -> Type`)**: Enforces constructor kind arity (`E0306`).
- **Default Sort Arguments**: Type function parameters support default expressions conforming to their sort: `\T = u8`, `\cap: int = 1024`. Default arguments follow the Telescopic scoping and trailing rules ([Generic Parameters, Defaults, and Value Sorts](#generic-parameters-defaults-and-value-sorts)).

| Parameter | Kind / value category |
| :--- | :--- |
| `\T: Type` | Type argument |
| `\M: Type -> Type` | Constructor receiving a type argument and producing a type |
| `\token: Type` | Static token value argument, not a constructor of kind `Type -> Type` |
| `\K: keyof T` | Static key value argument, not a type |

```ril
type SchemaV1 = { id: int, name: str }
type SchemaV2 = { id: int, name: str, email: str }

type VersionedSchema = \version: int -> match version {
    1 -> <SchemaV1>,
    2 -> <SchemaV2>,
    _ -> <never>,
}

type ActivePayload = VersionedSchema<2>        -- SchemaV2

type PickField = \T: { ..R }, K: keyof T -> <T.(K)>
type UserName = PickField<SchemaV1, "name">    -- str

type Wrapper = \M: Type -> Type, T -> <M<T>>
type OptInt = Wrapper<Option, int>             -- Option<int>
-- type BadKind = Wrapper<Resolve, int>         -- Error [E0306]: Resolve receives a token value, not a type argument
```

### Compile-Time Execution and Layout Cooperation

```ebnf
MetaLetDecl      ::= "meta" "let" ( ScreamingSnakeCase | "_" ) [ ":" TypeExpression ] "=" Expression
MetaFnDecl       ::= [ "pub" ] "meta" "fn" SnakeCase [ GenericParams ] "(" [ ParameterList ] ")" ReturnType Block
```

`meta let` and `meta fn` evaluate in the pure static domain. Only ordinary results recursively free of tokens, static-only metatypes, and type-producing authority may become immutable run-time constants. Token-valued `meta let` bindings remain static. Type functions may consume static values to select shapes; arithmetic on sizes follows ordinary integer rules.

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
        <{ inline_data: []u8, len: int }>
    } else {
        <{ heap_ptr: int, capacity: int, len: int }>
    }
meta let CAPACITY = align_to(60, 16)
type Buffer = BufferShape<CAPACITY>
meta let _ = assert(CAPACITY == 64)
-- meta let _ = assert(CAPACITY == 32) -- Error [E0830]: failed static assertion
```

Shape declarations promise no packed order, offsets, pointer size, or external binary layout.

```ril
-- Language-defined static declaration exposed by the prelude:
-- meta fn byte_size(value: Type) -> int
meta let BYTE_SIZE = byte_size(<u8>)
meta let _ = assert(BYTE_SIZE == 1)
-- let runtime_size = byte_size(<u8>) -- Error [E0810]: query requires static evaluation
```

| `byte_size` contract | Rule |
| :--- | :--- |
| Input | A `Type` token; query its represented target, not the token implementation |
| Result | Nonnegative `int` size of the represented target's value/handle on the selected abstract target; not its reachable graph |
| Layout domain | Static-only metatypes such as `Type` / `Type<User>`, and shapes requiring their materialization, have no ordinary run-time layout (`E0306`) |
| Phase | Static only; finite; usable by meta/type computations and other required static evaluations |
| Ordinary execution | `E0810`; a `meta let` result may be used as an ordinary constant |
| Visibility | Prelude declaration with ordinary lexical shadowing; not reserved syntax |
| Layout | May depend on the abstract target; grants no packed layout or field-offset guarantee |

## Modules, Program Execution, and Prelude

### Modules and Compilation Units

Every source file is an independent compilation unit. Compilation units are partitioned into two mutually exclusive kinds:

- **Implementation Units (`.ril`)**: Standard modules containing executable definitions. Functions in `.ril` modules MUST provide implementation bodies (`{ ... }`).
- **External Interface Declaration Units (`.d.ril`)**: Contract-only modules declaring external types, ambient constants, and foreign signatures without implementation bodies ([External Interface Declarations](#external-interface-declarations)). When a module path resolves to `<path>.d.ril`, the module is designated as an `ExternalContractModule` providing foreign interface signatures without local definitions.

Top-level items in both unit types are private to the file by default unless marked with `pub`.

```ril
-- In file: math/geometry.ril (Implementation Unit)
let PI = 3.141592653589793              -- Private to module 'geometry'
pub let TAU = 6.283185307179586         -- Public: exported from module

pub fn circle_area(radius: f64) &up(sub){PI} -> f64 {
    PI * radius * radius                -- OK: internal access to private 'PI'
}

-- In file: platform/fs.d.ril (External Interface Declaration Unit)
pub type FileHandle                     -- OK: opaque nominal external type
pub fn read_file(path: str) @Fiber -> Result<[]u8, str> -- OK: bodyless leaf-I/O signature

-- In file: app/main.ril
use math/geometry::{TAU, circle_area}   -- OK: importing from implementation unit
use platform/fs::{FileHandle, read_file} -- OK: importing from declaration unit
-- use math/geometry::{PI}              -- Error [E0201]: symbol 'PI' is private to module 'math/geometry'
```

### Module Imports and Visibility

```ebnf
UseDecl    ::= [ "pub" ] "use" ModulePath [ "as" PascalCase ]
             | [ "pub" ] "use" ModulePath "::" ( "{" ImportList "}" | "*" | ImportItem )
ModulePath ::= SnakeCase { "/" SnakeCase }
ImportList ::= ImportItem { "," ImportItem } [ "," ]
ImportItem ::= Identifier [ "as" Identifier ]
```

#### Normative Module Import Rules

```ril
-- Fixture module math/numbers.ril exports ONE; math/absent does not exist.
-- use math/absent                   -- Error [E0208]: no module at this path
-- use math/numbers::{TWO}           -- Error [E0209]: no member TWO in the resolved module
use math/numbers::{ONE}              -- OK
```

An unresolved module path is `E0208`. A selective import or qualified module access naming no member of an existing module is `E0209`. An existing but inaccessible member retains `E0201`; an unavailable ordinary lexical name retains `E0204`. Import name collisions retain `E0203`. These conditions do not establish new module search, dependency-cycle, or path-precedence rules.

- **Automatic PascalCase Namespace Derivation**:
   When a module path is imported directly without `::` and without an explicit `as` clause (`use ModulePath`), the module namespace bound in the current lexical scope defaults to the canonical PascalCase transformation of the terminal path segment (`to_pascal_case(last_segment)`):
   - `use math/geometry` automatically binds the namespace identifier `Geometry`.
   - `use ril/concurrent/channel` automatically binds `Channel`.
   - `use data/string_builder` automatically binds `StringBuilder`.
   Developers can invoke exported declarations via qualified member projection (e.g., `Geometry::circle_area(...)`, `Channel::bounded(...)`) without manual `as PascalCase` renaming ceremony.
- **Explicit Namespace Aliasing (`as PascalCase`)**:
   Providing an explicit `as PascalCase` clause overrides the canonical derived namespace identifier (e.g., `use math/geometry as Geo`). Supplying a non-PascalCase alias is statically rejected under `E0101`.
- **Selective Member Import (`use ModulePath::{ ... }`)**:
   Imports specific exported declarations into the lexical scope without qualification. Each imported item may optionally specify a local alias via `as Identifier`, conforming to identifier casing invariants (`E0101`).
- **Glob Import & Re-Export (`pub use ModulePath::*`)**:
   Re-exports or imports all public symbols from the target module into the local scope.
- **Lexical Scoping**:
   `use` declarations evaluate within their enclosing scope (file-level or block-level). Block-scoped imports remain strictly private to the enclosing block.

```ril
-- Automatic PascalCase Namespace Binding (omits redundant 'as'):
use math/geometry                       -- Automatically binds namespace 'Geometry'
let area = Geometry::circle_area(5.0)   -- OK: qualified static call

-- Explicit Namespace Aliasing:
use ril/crypto as Hash                  -- OK: explicit alias override via 'as PascalCase'
let digest = Hash::sha256("data")
-- use ril/crypto as hash               -- Error [E0101]: module namespace alias must be PascalCase, found 'hash'

-- Selective Member Import with Optional Renaming:
use ril/array::{push, pop as remove_last}
let mut arr = [1, 2]
arr !> push(3)
let last_item = arr !> remove_last()

-- Glob Re-Export:
pub use ril/math::*                     -- Re-export all public math items

-- Lexical Block-Scoped Import:
fn calculate() -> () {
    use ril/crypto::{sha256}            -- Block-scoped import: visible strictly inside calculate()
    let d = sha256("data")
}
-- let bad = sha256("data")              -- Error [E0204]: unresolved identifier 'sha256'
```

### Top-Level Initialization and Purity

- Top-level initialization has no observable effects; mutable variables require constant initializers.
- Ordinary `let` requires immutable data. Foreign resource constants expose stable descriptors with separate operation contracts.
- Postfix `?` outside a callable is `E0205`, including module initializers.

```ril
let MAX_CONNECTIONS: int = 100
let DEFAULT_TITLE: str = "Ril Application"
var active_workers: int = 0            -- OK: initialized with constant expression
fn start_worker() &up(sub){mut active_workers} -> () { active_workers += 1 }

-- Prohibited top-level runtime side effects and error propagation:
-- let current_time = Clock::now()      -- Error [E0202]: top-level declaration must be a pure constant expression
-- let db = Database::connect("db.loc") -- Error [E0202]: top-level declaration cannot invoke runtime I/O or effects
-- let top_parse = parse_id("10")?      -- Error [E0205]: postfix '?' operator used outside function or closure body; no enclosing activation frame to receive early return
```

### Test Conventions and Execution Protocol

Tests are ordinary functions. Their handlers, scoped bindings, Result inspection duties, and panic boundaries obey the same rules as other functions.

### Program Entry Point

```ril
-- Complete executable root; no root main is declared.
pub fn helper() -> () {}              -- Error [E0903]: executable program lacks its root main
```

An executable program without its required root `main` declaration is `E0903`. A present declaration that does not satisfy the entry contract is `E0904`. An ordinary library module is not required to declare `main`. Duplicate declarations of root `main` retain `E0203`.

Executable programs define one root `main` function. The examples below are alternatives, not two definitions in one program. Prelude print/println have `@Fiber`, and file-I/O examples use the corresponding leaf-I/O contract:

```ril
pub fn main() @Fiber -> () {
    println("Hello, Ril!")
}

-- Alternative complete fallible executable root:
use ril/file
pub fn main() @Fiber -> Result<(), str> {
    let config = File::read("config.json")?
    if config == "" {
        Err("empty configuration")     -- Runtime halts with non-zero exit code (1)
    } else {
        Ok()                            -- Exits cleanly with status code (0)
    }
}
```

```ril
-- Separate executable-root fixtures:
-- fn main() -> () {}                        -- Error [E0904]: entry must be public
-- pub fn main(value: int) -> () {}          -- Error [E0904]: entry has a parameter
-- pub fn main<T>() -> () {}                 -- Error [E0904]: entry has a generic parameter
-- pub fn main() -> int { 0 }          -- Error [E0904]: unsupported entry result
```

| Entry property | Requirement |
| :--- | :--- |
| Declaration | Public ordinary named Ril function in the executable root; `halt` is allowed subject to its usual checks |
| Value / generic parameters | None, including defaulted parameters |
| Result | `()` or the language's `Result<(), str>`, after transparent alias expansion |
| Effects / state | Ordinary declaration and provenance rules; undeclared residual effects remain `E0612` |
| Residual user-defined effect | No program-environment handler; `E0612` even if listed on main |

| Completed program outcome | Environment behavior |
| :--- | :--- |
| `()` or `Ok()` after required cleanup/barriers | Exit status 0 |
| `Err(message)` | Inspect the result; write the message and one LF to standard error, then exit status 1 |
| Reporting the error fails | Exit status 1; no successful outcome or further output guarantee |
| Uncontained panic / double fault / cancellation | Exit status 1; explanatory diagnostics are not fixed text |
| Declared `Fiber` / `Concurrent`, including `Async` | Supply their specified system operations |
| Declared `Div` exhaustion without a source handler | Begin panic unwinding; never resume the exhausted action |

Environment reporting occurs outside main's invocation and does not add a `Fiber` annotation requirement to a fallible pure main. An outward abortive source handler may produce a normal main result; it still follows the result table after cleanup. The program environment does not waive child-local effect confinement or guarantee termination.

### Prelude Scope

```ril
type UserId(int)
assert(inner(UserId(1001)) == 1001)
let original = [1, 2, 3]
let mut detached = clone(original)
detached !> Array::push(4)
assert(original == [1, 2, 3] && len(ref detached) == 4)
let snapshot = clone(ref detached)
let revised = .{ theme: "dark" } |> derive \mut draft -> {
    draft.theme = "light"
}
assert(revised.theme == "light" && len(snapshot) == 4)
let count = len([1, 2, 3])
println("Count: {count}")
```

The prelude is an ambient lexical scope enclosing every Ril compilation unit. Its declarations are accessible without explicit import statements. Local declarations may shadow ordinary prelude names; the intrinsic type family `Type` cannot be shadowed (`E0203`). Shadowing does not alter built-in syntax, compiler intrinsics, or declaration identities required by language-defined operators.

Primitive type spellings (`int`, `str`, `bool`, etc.), static metatypes (`Type`, `Type<T>`), `?T`, collection type syntax (`[]T`, `[K: V]`), and built-in system effect identities (`Fiber`, `Concurrent`, `Async`, `Div`) are language constructs, not imported prelude declarations.

#### Built-in Foundational Operations

Ril defines the following built-in foundational operations directly in the language prelude:

```ril
assert(len("Ril") == 3 && len(b"RIFF") == 4)
let copied = clone(42)
assert(copied == 42)
-- len(ref "Ril")                    -- Error [E0401]: text is a value type
-- clone(ref 42)                     -- Error [E0401]: use ordinary value passage
```

For inputs supported by the selected operation:

| Input | Ordinary form | Explicit `ref` form |
| :--- | :--- | :--- |
| Value type, including `str` / `bytes` | Receive value | `E0401` |
| Immutable reference data | Receive immutable data | Observe same data |
| Live reference data | `E0535` | Observe without freezing |

Forms preserve data schemas and operation identity. Resource contracts remain separate; neither form grants resource permissions. Operators, projections, indexing, and traversal are primitive observations, not immutable-parameter receptions.

| Operation | Signature | Effects | Phase | Complexity | Contract |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `len` | `len(value)` / `len(ref value) -> int` | Pure | Dual-phase | $O(1)$ / $O(n)$ text | Count of elements, entries, bytes, or Unicode scalars |
| `inner` | `inner(wrapper) -> T` / `inner(ref wrapper) -> ref(wrapper) T` | Pure | Runtime | $O(1)$ | Preserve immutable/observed payload authority; value payloads use a plain result; unit nominal yields `()` |
| `clone` | `clone(value)` / `clone(ref value)` | Pure | Runtime | $O(\text{graph})$ | Ordinary reference result `new T`, value result `T`; preserves graph aliases, cycles, and schemas. Resource cloning follows its separate contract |
| `derive` | `derive(base, recipe) -> T` | Forwards recipe | Runtime | $O(\text{affected})$ | Functional update on immutable value via confined mutable draft |
| `byte_size` | `meta fn byte_size(value: Type) -> int` | Pure | Static only | $O(1)$ | Size of the represented target's value/handle; static-only targets have no run-time layout |
| `type_name` | `meta fn type_name(value: Type) -> str` | Pure | Static only | $O(\text{len})$ | Canonical representation of the token's target, including static metatypes, for diagnostics |
| `panic` | `panic(message: str) -> never` | Defect | Dual-phase | Finite | Initiates panic unwinding at runtime; halts compile-time evaluation with E0831 |
| `assert` | `assert(condition: bool, message: str = "assertion failed") -> ()` | Defect | Dual-phase | $O(1)$ | Panics on false condition; compile-time failure is `E0830` |
| `print` | `print(text: str) @Fiber -> ()` | `@Fiber` | Runtime | $O(\text{len})$ | Writes UTF-8 text to standard output without trailing newline |
| `println` | `println(text: str) @Fiber -> ()` | `@Fiber` | Runtime | $O(\text{len})$ | Writes UTF-8 text followed by one LF byte (`\n`) to standard output |

#### Normative Rules for Built-in Operations

- **Length Invariant (`len`)**:
  - `len` is a pure, dual-phase built-in operation admitted in both runtime and static contexts.
  - `len(ref value)` observes reference data; `len(value)` receives immutable data.
  - For `str`, returns the total number of Unicode scalar values (code points), matching `s[a..b]` scalar indexing.
  - For `bytes`, returns the byte count in $O(1)$ time.
  - For arrays (`[]T`), returns the element count in $O(1)$ time.
  - For maps (`[K: V]`), returns the number of key-value pairs in $O(1)$ time.
  - For sets (`Set<T>`), returns the number of unique elements in $O(1)$ time.
- **Unwrapping Invariant (`inner`)**:
  - Unwraps nominal type wrappers to their underlying declared representation ([Nominal Type Wrappers](#nominal-type-wrappers)).
  - `inner(ref wrapper)` preserves observed payload provenance; ordinary `inner(wrapper)` receives immutable data.
  - Single-payload nominal wrapper `type UserId(int)` unwraps to its payload (`int`). Unit nominal wrapper `type Marker` unwraps to `()`.
  - Nominal abstraction boundaries remain sealed across modules; `inner` cannot bypass opaque module access restrictions.
- **Graph Isolation Invariants (`clone`)**:
  - `clone` creates an independent, isolated copy of an ordinary reachable graph, severing writable storage from the source while preserving internal aliases, shared references, and cyclic structures ([Deep Immutability](#deep-immutability)).
  - `clone(ref value)` copies observed reference data without freezing it. The receiver and member schema determine the copy's permissions.
  - Receiving an eligible fresh copy with ordinary `let` publishes immutable data by recursively suppressing member permissions; no separate qualifier is required.
  - Non-clonable entities (retained closure environments, live tasks, unique receivers, and scoped resources) cannot be cloned through `ref` handles or wrappers (`E0530`).
  - Cloning a channel `Sender` obeys the channel endpoint resource contract and requires `@Fiber`.
  - Copying costs $O(\text{graph})$ for the reachable ordinary graph inspected and copied; no storage-sharing guarantee is made for mutable copies.
- **Functional Update Invariant (`derive`)**:
  - Confines mutation to a temporary draft within the recipe closure (`\mut draft -> ...`), returning a new immutable value of the same type and qualifier ([Functional Updates via Derive](#functional-updates-via-derive)).
  - Rejects non-immutable input targets (`E0536`).
  - Traps escaping draft references (`E0607`).
  - Forwards recipe algebraic effects and external state obligations; discharges draft-local writes.
- **Static Layout Query (`byte_size`)**:
  - `meta fn byte_size(value: Type) -> int` queries the represented target's nonnegative value/handle size ([Compile-Time Execution and Layout Cooperation](#compile-time-execution-and-layout-cooperation)). Static-only metatypes have no ordinary layout (`E0306`); widening does not change the target being queried.
  - Static-only: permitted during compile-time static evaluation (`meta let`, type functions); calling `byte_size` in runtime code is `E0810`.
  - Grants no packed layout, field offset, or external ABI alignment guarantees.
- **Defect Initiation and Assertions (`panic`, `assert`)**:
  - `panic(message: str) -> never` is a dual-phase defect primitive:
    - At runtime, initiates stack unwinding, executing synchronous frame LIFO cleanups. A secondary fault during cleanup results in `DoubleFaultFatal` ([Run-Time Failure Conditions](#run-time-failure-conditions)). Panic is a defect mechanism, not an algebraic effect.
    - In static evaluation (`meta let`, `meta fn`, pure `type` functions), `panic(message)` immediately aborts static evaluation, producing diagnostic `E0831: StaticEvaluationPanicError` with `message` as the primary error text attributed to the triggering instantiation site.
  - `assert(condition: bool, message: str = "assertion failed") -> ()` evaluates its arguments eagerly before the call; if `condition` is false, it panics with `message`.
  - In static evaluation (`meta let`), a false assertion condition produces diagnostic `E0830` at compile time. Static assertions cannot catch panics.
- **Standard Output Invariants (`print`, `println`)**:
  - `print` and `println` write UTF-8 encoded text to host standard output under the `@Fiber` system effect.
  - `println` appends exactly one LF byte (`0x0A`, `\n`) without host-specific newline conversions (e.g. no CRLF translation).
  - Both convenience operations panic on unrecoverable host I/O failure; fallible streaming I/O is provided separately by `ril/io`.
  - Concurrent writes across tasks may interleave at arbitrary byte boundaries without synchronization.
- **Prelude Shadowing and Integrity**:
  - Lexical declarations in inner scopes may shadow ordinary prelude names such as `clone`, `len`, and `assert`; protected `Type` is excluded.
  - A locally defined function named `clone` does not acquire the prelude's freshness and copying guarantees (`E0522`).

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

Every Result must be inspected, propagated, unpacked, or returned with its obligation (`E0720`).

| Operation / exit | Inspection duty |
| :--- | :--- |
| Actual success/error tag test | Inspected; any alias discharges the same produced Result |
| `is` wildcard / expected-value equality | No Result inspection by itself; only reached constructor/tag tests discharge their Results |
| Binding, alias, wrapping, aggregate, Task | Preserve one obligation, not one per name |
| Deep copy | Preserve copied Results' obligations; copying is not inspection |
| `_`, overwrite, removal, lost last path | Do not discharge |
| Outer tag test | Does not inspect an inner Result |
| `?` | Propagates failure to the enclosing callable |
| Normal completion, including `Err` return | Cannot abandon other outstanding Results |
| Abnormal unwinding | May discard; structured cancellation keeps its specified rules |

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
| **`E0113`** | [`ReservedKeywordIdentifierError`](#keywords) |
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
| **`E0210`** | [`DuplicateFieldError`](#record-construction-and-functional-update); [Record Types and Row Polymorphism](#record-types-and-row-polymorphism) |
| **`E0211`** | [`ConflictingSpreadFieldsError`](#record-construction-and-functional-update) |
| **`E0212`** | [`OverlappingRowFieldError`](#record-types-and-row-polymorphism) |

### Types, Expressions, Generics, and Patterns

| Code | Diagnostic and defining rule |
| :---: | :--- |
| **`E0301`** | [`TypeMismatchError`](#diagnostic-classification) |
| **`E0302`** | [`UnexpectedFieldError`](#record-types-and-row-polymorphism) |
| **`E0303`** | [`NonExhaustiveMatchError`](#pattern-matching) |
| **`E0304`** | [`UnreachableMatchArmError`](#pattern-matching); [Sum Types and GADTs](#sum-types-and-gadts) |
| **`E0305`** | [`NominalTypeMismatchError`](#nominal-type-wrappers) |
| **`E0306`** | [`KindMismatchError`](#structural-type-pattern-matching); [Static Layout](#compile-time-execution-and-layout-cooperation) |
| **`E0307`** | [`MissingFieldError`](#record-types-and-row-polymorphism) |
| **`E0308`** | [`OpaqueBoundaryViolationError`](#type-declarations-and-opaque-types) |
| **`E0309`** | [`VacuousBindingError`](#guarded-bindings-and-non-vacuous-invariant) |
| **`E0310`** | [`InvalidatedNarrowingAccessError`](#flow-sensitive-type-narrowing) |
| **`E0311`** | [`ContradictoryNarrowingError`](#flow-sensitive-type-narrowing) |
| **`E0312`** | [`TupleIndexOutOfBoundsError`](#array-map-and-tuple-types) |
| **`E0313`** | [`CyclicTypeAliasError`](#type-declarations-and-opaque-types) |
| **`E0314`** | [`ArityMismatchError`](#pattern-matching); [Default Parameters and Named Arguments](#default-parameters-and-named-arguments) |
| **`E0315`** | [`EscapingLocalNominalTypeError`](#block-expressions-tail-values-and-hoisted-declarations) |
| **`E0316`** | [`NonTrailingDefaultGenericParamError`](#generic-parameters-defaults-and-value-sorts) |
| **`E0317`** | [`FunctionDefaultGenericProhibitedError`](#generic-parameters-defaults-and-value-sorts) |
| **`E0318`** | [`LiteralTypeProhibitedError`](#generic-parameters-defaults-and-value-sorts) |
| **`E0319`** | [`BareTypeInExpressionContextError`](#static-type-values-and-type-quotation) |
| **`E0320`** | [`ForwardTypeDefaultReferenceError`](#generic-parameters-defaults-and-value-sorts) |
| **`E0321`** | [`NonDivergentElseError`](#guarded-bindings-and-non-vacuous-invariant) |
| **`E0322`** | [`WildcardExpressionError`](#identifiers-and-casing-invariants) |
| **`E0323`** | [`ConstGenericSortMismatchError`](#generic-parameters-defaults-and-value-sorts) |
| **`E0324`** | [`DynamicRecordIndexProhibitedError`](#record-types-and-row-polymorphism) |
| **`E0325`** | [`DuplicateArgumentError`](#default-parameters-and-named-arguments) |
| **`E0326`** | [`LiteralOutOfRangeError`](#numeric-literals) |
| **`E0327`** | [`UnsupportedOperandTypeError`](#bitwise-and-shift-operators) |
| **`E0328`** | [`InvalidCollectionKeyTypeError`](#relational-equality-and-containment-operators) |
| **`E0329`** | [`IncompatibleFormatSpecifierError`](#text-and-byte-literals) |
| **`E0330`** | [`BareEffectTypeAliasError`](#type-definition-boundaries) |
| **`E0331`** | [`BareCapabilityTypeAliasError`](#type-definition-boundaries) |
| **`E0332`** | [`VariantComputationAnnotationError`](#type-definition-boundaries) |
| **`E0333`** | [`FieldComputationAnnotationError`](#type-definition-boundaries) |
| **`E0334`** | [`GenericComputationConstraintError`](#type-definition-boundaries) |
| **`E0335`** | [`TypeFunctionComputationAnnotationError`](#type-definition-boundaries) |
| **`E0336`** | [`UnknownFieldError`](#record-types-and-row-polymorphism) |
| **`E0337`** | [`NonProductProjectionError`](#record-types-and-row-polymorphism); [Anonymous Functions, Trailing Closures, and Projection Accessors](#anonymous-functions-trailing-closures-and-projection-accessors) |
| **`E0338`** | [`NonCallableInvocationError`](#default-parameters-and-named-arguments) |
| **`E0339`** | [`UnknownNamedArgumentError`](#default-parameters-and-named-arguments) |
| **`E0340`** | [`GenericArityMismatchError`](#generic-parameters-defaults-and-value-sorts) |
| **`E0341`** | [`InvalidRecordKeySortError`](#symmetrical-mapped-comprehensions) |
| **`E0342`** | [`InvalidTupleKeySortError`](#symmetrical-mapped-comprehensions) |
| **`E0343`** | [`SingleElementTupleProhibitedError`](#symmetrical-mapped-comprehensions) |
| **`E0344`** | [`InsufficientTypeInformationError`](#generic-parameters-defaults-and-value-sorts); [Array, Map, and Tuple Types](#array-map-and-tuple-types) |
| **`E0345`** | [`RefutablePatternError`](#pattern-matching) |
| **`E0346`** | [`OrPatternBindingMismatchError`](#pattern-matching) |
| **`E0347`** | [`DuplicatePatternBindingError`](#pattern-matching) |
| **`E0348`** | [`InvalidRangePatternError`](#pattern-matching) |
| **`E0349`** | [`InvalidPatternExpressionError`](#pattern-matching) |
| **`E0350`** | [`NonBooleanConditionError`](#conditional-expressions); [Logical Operators](#logical-operators) |
| **`E0351`** | [`IncompatibleBranchTypesError`](#conditional-expressions); [Pattern Matching](#pattern-matching) |
| **`E0352`** | [`InvalidIndexTargetError`](#array-map-and-tuple-types) |
| **`E0353`** | [`NullaryVariantCallError`](#constructor-tuple-equivalence-invariant) |
| **`E0354`** | [`InvalidVariantContractError`](#sum-types-and-gadts) |
| **`E0355`** | [`NonIterableValueError`](#loop-expressions) |

### Parameters, Argument Modes, and Defaults

| Code | Diagnostic and defining rule |
| :---: | :--- |
| **`E0401`** | [`ValueTypeReferenceParameterError`](#parameter-modes-caller-obligations-and-defaults) |
| **`E0402`** | [`ValueTypeReferenceModeError`](#value-types) |
| **`E0403`** | [`VarParameterProhibitedError`](#parameter-modes-caller-obligations-and-defaults); [Effect Handlers](#effect-handlers) |
| **`E0404`** | [`MutableParameterDefaultProhibitedError`](#default-parameters-and-named-arguments) |
| **`E0405`** | [`MissingArgumentModeMarkerError`](#parameter-modes-caller-obligations-and-defaults) |
| **`E0406`** | [`InvalidArgumentModeError`](#parameter-modes-caller-obligations-and-defaults); [Effect Handlers](#effect-handlers) |
| **`E0407`** | [`CallableParameterModeMismatchError`](#parameter-modes-caller-obligations-and-defaults) |
| **`E0408`** | [`InvalidDefaultParameterReferenceError`](#default-parameters-and-named-arguments) |
| **`E0409`** | [`ImpureParameterDefaultError`](#default-parameters-and-named-arguments) |
| **`E0410`** | [`InvalidMutableArgumentTargetError`](#parameter-modes-caller-obligations-and-defaults) |
| **`E0411`** | [`InvalidConstructionParameterError`](#fresh-construction-parameters) |

### Bindings, State, Permissions, and Resource Contracts

| Code | Diagnostic and defining rule |
| :---: | :--- |
| **`E0501`** | [`ImmutableReassignmentError`](#immutable-bindings) |
| **`E0502`** | [`PinnedHandleReassignmentError`](#pinned-mutable-handles) |
| **`E0503`** | [`InvalidAssignmentTargetError`](#assignments-and-compound-assignments) |
| **`E0510`** | [`MissingCapabilityAnnotationError`](#callable-contracts); [Retained Mutable Sharing](#retained-mutable-sharing) |
| **`E0520`** | [`MutabilityLaunderingError`](#monotonic-permission-degradation-and-anti-laundering-matrix) |
| **`E0521`** | [`DestructureMutabilityLaunderingError`](#monotonic-permission-degradation-and-anti-laundering-matrix) |
| **`E0522`** | [`ContainerMutabilityLaunderingError`](#monotonic-permission-degradation-and-anti-laundering-matrix) |
| **`E0523`** | [`MutMutAliasingConflictError`](#law-of-exclusivity-and-cross-argument-disjointness) |
| **`E0524`** | [`ReadMutAliasingHazardError`](#law-of-exclusivity-and-cross-argument-disjointness) |
| **`E0525`** | [`SpreadLaunderingError`](#monotonic-permission-degradation-and-anti-laundering-matrix) |
| **`E0526`** | [`CollectionMutationDuringIterationError`](#monotonic-permission-degradation-and-anti-laundering-matrix) |
| **`E0527`** | [`UnusedMutableBindingError`](#binding-permissions-and-storage-matrix) |
| **`E0528`** | [`ReturnMutabilityLaunderingError`](#monotonic-permission-degradation-and-anti-laundering-matrix) |
| **`E0529`** | [`ExcessiveCapabilityAnnotationError`](#retained-mutable-sharing); [Named Function State Contract References](#named-function-state-contract-references) |
| **`E0530`** | [`IllegalCapabilityCloneError`](#deep-immutability) |
| **`E0531`** | [`InvalidRefOriginError`](#read-only-reference-bindings) |
| **`E0532`** | [`ReassignableScopedResourceError`](#scoped-resource-bindings) |
| **`E0533`** | [`AliasedNarrowingHazardError`](#flow-sensitive-type-narrowing) |
| **`E0534`** | [`HazardErasureProhibitedError`](#callable-contracts); [Closures, Factory Signatures, and Lexical Environments](#closures-factory-signatures-and-lexical-environments) |
| **`E0535`** | [`NonImmutableBindingError`](#immutable-bindings) |
| **`E0536`** | [`NonImmutableDeriveInputError`](#functional-updates-via-derive) |
| **`E0537`** | [`LiveArrayInvalidationError`](#range-and-sequence-indexing-expressions) |
| **`E0538`** | [`InvalidStateSourceGroupError`](#state-groups-and-captured-layers) |
| **`E0539`** | [`InvalidStateContractReferenceError`](#named-function-state-contract-references) |
| **`E0540`** | [`EndedOperationAuthorityAccessError`](#effect-handlers) |
| **`E0541`** | [`InvalidScopedCleanupContractError`](#scoped-resource-bindings) |
| **`E0543`** | [`NewTargetRefError`](#read-only-reference-bindings) |
| **`E0544`** | [`MissingInferredFunctionAnnotationError`](#mandatory-contract-inference-and-completion); missing required source annotations on a named definition only |
| **`E0545`** | [`InvalidReturnSourceContractError`](#return-construction-permissions-and-sources) |
| **`E0546`** | [`InvalidNewReturnContractError`](#return-construction-permissions-and-sources) |
| **`E0547`** | [`InvalidOpenRowPlacementError`](#closed-and-open-callable-rows) |
| **`E0548`** | [`InvalidConstructionInputError`](#fresh-construction-parameters) |
| **`E0549`** | [`EndedConstructionAuthorityAccessError`](#fresh-construction-parameters) |

### Effects, Resumption, Concurrency, and Escape

| Code | Diagnostic and defining rule |
| :---: | :--- |
| **`E0601`** | [`CrossThreadDataRaceHazardError`](#structured-concurrency-and-panic-containment) |
| **`E0602`** | [`IllegalChannelPayloadCapabilityError`](#structured-concurrency-channels) |
| **`E0603`** | [`ChannelEndpointAliasingConflictError`](#structured-concurrency-channels) |
| **`E0604`** | [`ScopedResourceEscapeError`](#scoped-resource-bindings) |
| **`E0605`** | [`InvalidParallelCapabilityError`](#deterministic-data-parallelism-and-divide-and-conquer-primitives) |
| **`E0606`** | [`ScopedTaskEscapeError`](#structured-concurrency-and-panic-containment) |
| **`E0607`** | [`DerivedProxyEscapeError`](#functional-updates-via-derive) |
| **`E0610`** | [`DuplicateResumeInvocationError`](#affine-resumption-and-delimited-early-abort) |
| **`E0611`** | [`EscapingResumeError`](#affine-resumption-and-delimited-early-abort) |
| **`E0612`** | [`UnhandledEffectError`](#callable-contracts); [Built-in System Effects](#built-in-system-effects) |
| **`E0613`** | [`ValueEffectAnnotationError`](#type-definition-boundaries) |
| **`E0614`** | [`UnstableHandlerCaptureError`](#effect-handlers) |
| **`E0615`** | [`CrossTaskUnhandledEffectError`](#structured-concurrency-and-panic-containment); [Effect Handlers](#effect-handlers) |
| **`E0616`** | [`ScopedCleanupEffectError`](#scoped-resource-bindings) |
| **`E0617`** | [`ScopedCleanupDivergenceError`](#scoped-resource-bindings) |
| **`E0618`** | [`UndischargedLocalEffectError`](#block-expressions-tail-values-and-hoisted-declarations) |
| **`E0619`** | [`ParallelDisjointAccessConflictError`](#deterministic-data-parallelism-and-divide-and-conquer-primitives) |
| **`E0620`** | [`PseudoEffectAnnotationError`](#deterministic-data-parallelism-and-divide-and-conquer-primitives) |
| **`E0621`** | [`InvalidHandlerTargetError`](#effect-handlers) |
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
| **`E0706`** | [`SignatureTypeNotInWaistWhereError`](#dual-tier-where-invariants) |
| **`E0707`** | [`InvalidControlTransferContextError`](#control-transfers) |
| **`E0710`** | [`IllegalControlTransferInFallbackError`](#error-and-fallback-operators) |
| **`E0711`** | [`InvalidResultFallbackError`](#error-and-fallback-operators) |
| **`E0712`** | [`InvalidPropagationOperandError`](#error-and-fallback-operators) |
| **`E0713`** | [`IncompatiblePropagationTargetError`](#error-and-fallback-operators) |
| **`E0714`** | [`InvalidFallbackOperandError`](#error-and-fallback-operators) |
| **`E0715`** | [`InvalidSafeAccessReceiverError`](#error-and-fallback-operators) |
| **`E0720`** | [`UnusedFallibleResultError`](#mandatory-inspection-of-fallible-results) |

### Static Computation and Totality

| Code | Diagnostic and defining rule |
| :---: | :--- |
| **`E0810`** | [`CallFamilyViolationError`](#disjoint-call-families-evaluation-budgets-and-branch-pruning) |
| **`E0811`** | [`CompileTimeBudgetExceededError`](#pure-type-functions-and-type-return-privilege) |
| **`E0812`** | [`MetaTypeReturnProhibitedError`](#pure-type-functions-and-type-return-privilege) |
| **`E0813`** | [`MetaComputationAnnotationError`](#pure-type-functions-and-type-return-privilege) |
| **`E0814`** | [`StaticValueRequiredError`](#disjoint-call-families-evaluation-budgets-and-branch-pruning) |
| **`E0815`** | [`InvalidStaticValueError`](#disjoint-call-families-evaluation-budgets-and-branch-pruning) |
| **`E0816`** | [`RuntimeTypeTokenProhibitedError`](#pure-type-functions-and-type-return-privilege) |
| **`E0820`** | [`TotalityViolationError`](#termination-and-halt-contracts); [Deterministic Data Parallelism and Divide-and-Conquer Primitives](#deterministic-data-parallelism-and-divide-and-conquer-primitives) |
| **`E0821`** | [`HaltPurityViolationError`](#termination-and-halt-contracts) |
| **`E0822`** | [`InvalidBudgetBoundaryError`](#finite-evaluation-with-div) |
| **`E0830`** | [`MetaAssertionFailedError`](#pure-type-functions-and-type-return-privilege) |
| **`E0831`** | [`StaticEvaluationPanicError`](#pure-type-functions-and-type-return-privilege) |

### Module Forms, Entry Points, and External Contracts

| Code | Diagnostic and defining rule |
| :---: | :--- |
| **`E0901`** | [`BodyInDeclModuleError`](#external-interface-declarations) |
| **`E0902`** | [`MissingBodyInStandardModuleError`](#external-interface-declarations) |
| **`E0903`** | [`MissingEntryPointError`](#program-entry-point) |
| **`E0904`** | [`InvalidEntryPointError`](#program-entry-point) |
| **`E0907`** | [`ForeignStructuralFieldPenetrationError`](#external-interface-declarations) |
| **`E0908`** | [`UnsupportedExternalAuthorityContractError`](#external-interface-declarations) |
