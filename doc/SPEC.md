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
  - `-- Warning [WXXXX]`: Valid programs meeting a specified advisory warning condition; reporting the warning is optional.
  - `-- Panics`: Programs that raise deterministic runtime panics under defect conditions.
- **Diagnostic Text**: Codes and their triggering conditions are normative. Example message text, source highlighting, notes, and suggested repairs are illustrative. `-- OK` asserts validity, not the absence of advisory warnings.
- **Examples**: Blocks are independent fixtures unless marked as complete source files.
- Local statements run in an enclosing callable; displayed declarations belong to its enclosing declaration scope. Free names are typed fixture inputs or supplied contracts.
- Fixtures handle their local expressions' effects. Named functions and complete files obey their own annotations, casing, and initialization rules.
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
    - [Complete Provenance and Optional Annotations](#complete-provenance-and-optional-annotations)
    - [Functional Updates via Derive](#functional-updates-via-derive)
      - [Normative Rules for Functional Updates](#normative-rules-for-functional-updates)
    - [Generic Parameters, Defaults, and Value Sorts](#generic-parameters-defaults-and-value-sorts)
    - [Type Definition Boundaries](#type-definition-boundaries)
  - [Declarations and Bindings](#declarations-and-bindings)
    - [Binding Permissions and Storage Matrix](#binding-permissions-and-storage-matrix)
    - [Immutable Bindings](#immutable-bindings)
    - [Pinned Mutable Handles](#pinned-mutable-handles)
      - [Normative Rules for Pinned Handles](#normative-rules-for-pinned-handles)
    - [Reassignable Mutable Variables](#reassignable-mutable-variables)
      - [Normative Rules for Reassignable Variables](#normative-rules-for-reassignable-variables)
    - [Scoped Resource Bindings](#scoped-resource-bindings)
      - [Normative Rules for Scoped Bindings](#normative-rules-for-scoped-bindings)
    - [Live View Bindings](#live-view-bindings)
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
    - [Range and Slicing Expressions](#range-and-slicing-expressions)
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
      - [Empty Rows on Higher-Order Signatures](#empty-rows-on-higher-order-signatures)
      - [Callable Type Bounds](#callable-type-bounds)
      - [Higher-Order Calls](#higher-order-calls)
    - [Termination and halt Contracts](#termination-and-halt-contracts)
    - [Parameter Modes, Caller Obligations, and Defaults](#parameter-modes-caller-obligations-and-defaults)
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
  - [Advisory Warnings](#advisory-warnings)

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
- Enforce the complete provenance obligations below regardless of which optional annotations or diagnostic explanations are displayed. Static validity is determined by the specified conservative judgments, not by an assumption that arbitrary run-time behavior can be decided exactly.

### Diagnostic Classification

```ril
let value: str = 1                    -- Error [E0301]: incompatible expression type
let unused_value = 1                  -- Warning [W0001]: valid unused read-only binding
let quotient = 1 / 0                  -- Panics: integer division by zero
meta let QUOTIENT = 1 / 0             -- Error [E0831]: panic during static evaluation
```

An `E` diagnostic rejects a program under a specified syntactic or semantic rule. A `W` diagnostic is advisory and cannot change language validity. A panic is an execution outcome, not a static diagnostic or an algebraic effect. Recoverable `Result` and `Option` values are ordinary data, not diagnostic categories.

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
fn parent_fault() -> Result<int, TaskFault> @Concurrent {
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
| Negative, reversed, or out-of-bounds sub-range | Sub-range bounds panic under the [slicing rules](#range-and-slicing-expressions) |
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
| Parentheses, brackets, generic lists, record/declaration fields | Whitespace; nested executable blocks keep their own boundaries |
| Trailing operator, comma, `=`, `:`, `->` | Continue the required operand or body |
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
| Open syntactic delimiter at end of source | `E0122` |
| Closing delimiter disagrees with its corresponding opener | `E0123` |
| A required separator or other grammar token is absent between otherwise identifiable constituents | `E0124` |

Unterminated literals and comments use their lexical diagnostics rather than `E0121`/`E0122`. `E0124` does not make a token mandatory where the grammar or newline rules permit omission. Malformed interpolation uses `E0112` for its own braces, empty expression, or format syntax; an independently invalid embedded expression retains its ordinary diagnostic.

### Identifiers and Casing Invariants

```ebnf
Identifier         ::= PascalCase | SnakeCase | ScreamingSnakeCase | SuppressedVar
PascalCase         ::= [A-Z] { [a-zA-Z0-9] }
SnakeCase          ::= [a-z] [a-z0-9]* { "_" [a-z0-9]+ }
ScreamingSnakeCase ::= [A-Z] [A-Z0-9]* { "_" [A-Z0-9]+ }
SuppressedVar      ::= "_" [a-z] [a-z0-9]* { "_" [a-z0-9]+ }
Wildcard           ::= "_"
QualifiedName    ::= Identifier { "::" Identifier }
```

Identifier grammatical roles obey the **Closed Casing Invariant**:

- **`PascalCase`**: Strictly reserved for types (`type`), ADT variant constructors, nominal wrappers, algebraic effects (`eff`), generic type parameters (`T`, `ItemType`), and module namespace identifiers (`Array`, `Channel`, `Geometry`).
   - **Acronym Title-Casing Rule**: Acronyms within `PascalCase` MUST be title-cased as regular words (`HttpServer`, `UserId`, `JsonParser`, NOT `HTTPServer`, `UserID`, `JSONParser`) (`E0102`).
- **`snake_case`**: Strictly used for runtime variables (local bindings, function parameters, reassignable variables `var`, and pinned mutable handles `let mut`), const generic parameters (`cap: int`), named functions (`fn`, `meta fn`), record fields, and module path segments (`ril/array`, `math/geometry`).
- **`SCREAMING_SNAKE_CASE`**: Strictly reserved for compile-time constants (`meta let`) and top-level immutable constants (`let`). Top-level mutable variables (`var`, `let mut`) MUST use `snake_case`.
- **Static Keys and Field Labels**: Static key binders (`K: keyof T`) and mapped-key binders (`[K in ...]`) use PascalCase. Ordinary field labels use snake_case, optionally with one leading underscore. A mapped record may expose valid PascalCase constructor labels; construction and projection against that mapped schema use those generated labels verbatim. This does not permit uppercase run-time variable bindings.
- **Wildcard & Suppression**: A single underscore `_` is strictly the wildcard discard pattern, not an identifier (`E0322`). An identifier with a leading underscore `_snake_case` declares an intentionally unused read-only variable or parameter. It does not waive mutable-authority use requirements (`E0527`).

```ril
type First { Shared }
type Second { Shared }
let first: First = First::Shared       -- OK: qualified constructor
-- let ambiguous: First = Shared      -- Error [E0206]: expected type does not resolve the abbreviation
type Maybe<T> = Option<T>
let value: Maybe<int> = Some(1)        -- OK: an alias adds no constructor candidate
```

Declarations and imports share one namespace. Same-scope duplicates are `E0203`; inner declarations may shadow outer ones, including the enclosing prelude.

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
fn start_worker() &{mut active_workers} { active_workers += 1 }
fn compute_area(width: f64) -> f64 { width * 2.0 } -- OK: function identifier
meta fn pad_align(size: int) -> int { size }       -- OK: compile-time function

-- SCREAMING_SNAKE_CASE: meta let and Top-Level Immutable Variables ONLY
meta let MAX_BUFFER_SIZE = 1024 * 64   -- OK: compile-time constant
let DEFAULT_TIMEOUT_MS = 5000          -- OK: top-level immutable constant

-- Wildcard and Unused Suppression
let _ = user_count                     -- OK: wildcard discard
fn on_event(ev: Event, _ctx: Context) { handle(ev) } -- OK: '_ctx' is intentionally unused

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

The following 34 tokens are reserved; they cannot be ordinary identifiers or field labels:

```
as       eff      else     false    fn
for      halt     if       in       is
keyof    last     let      loop     match
meta     module   mut      never    next
opaque   pub      resume   return   scoped
true     type     typeof   use      var
view     where    while    with
```

```ril
-- let while = 1                     -- Error [E0113]: reserved keyword in a binding position
-- type Record = { if: int }         -- Error [E0113]: reserved keyword as a field label
let while_count = 1                   -- OK
let capture = 1                       -- OK: capture is an ordinary identifier
let closure = 1                       -- OK: closure is an ordinary identifier
type Config = { capture: bool }       -- OK: capture is an ordinary field label
```

A reserved keyword used as an ordinary identifier or field label is `E0113`.

`capture` and `closure` remain ordinary identifiers. They act as contextual keywords in capability and state-group annotations: `&capture` is a capability annotation, `&closure` is a callable-type capability bound, and in a state group, a leading `closure` followed by a comma, or by a capture-owner name and a comma, is a contextual group header. This interpretation is fixed before name resolution; it never falls back to a list of global names. The state-group rules specify the remaining cases.

```ril
-- Reserved keywords in action:
pub opaque type Token = int            -- 'pub', 'opaque', 'type'
meta let COMPILE_ID = 101              -- 'meta', 'let'
eff Logger { log(str) -> () }          -- 'eff'
use ril/array::{push}                  -- 'use'
halt fn total_step() -> bool { true }  -- 'halt', 'true', 'fn'
use ril/file
use ril/io::{IoError}
fn manage_resource() -> Result<(), IoError> @Fiber {
    let scoped mut res = File::open("a.txt")?  -- 'scoped', '?' inside function frame
    let view v = res                       -- 'view' in handle binding
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

Value types have copy-by-value semantics. They cannot be borrowed as `mut` parameters.

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
-- Value types: independent copy-by-value semantics:
let a: int = 42
var b = a                              -- Independent copy; value types use 'var' for mutation
b += 1                                 -- Modifies 'b'; 'a' remains 42
assert(a == 42 && b == 43)

-- let mut bad_scalar = a              -- Error [E0402]: scalar value type 'int' has no interior mutability; use 'var'
-- fn bad_borrow(mut x: int) {}        -- Error [E0401]: value type 'int' cannot be borrowed as 'mut' parameter
```

### Reference Types

Reference types are allocated on the managed garbage-collected heap: arrays (`[]T`), maps (`[K: V]`), records, tuples, sets, and sum type instances.

```ril
-- Reference types: shared heap aliasing:
type Node = { mut val: int }
let mut n1 = Node.{ val: 10 }
let view n2 = n1                       -- 'n2' aliases the exact same heap record as a live view
n1.val = 99                            -- Mutate through 'n1'
assert(n2.val == 99)                   -- OK: 'n2' observes mutation due to reference aliasing

-- Mutating through read-only alias is strictly prohibited:
-- n2.val = 100                        -- Error [E0520]: cannot mutate field 'val' through read-only view 'n2'
```

### Record Types and Row Polymorphism

- Field `mut` permits replacing that slot. A projected reference retains its stored origin and permissions, limited by the permissions of the entire access path. Slot mutability neither upgrades a child reference nor makes its data immutable.
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
RecordField      ::= [ "mut" ] FieldLabel ":" TypeExpression
TypeProjection ::= PrimaryType "." ( Identifier | TupleIndex | "(" Expression ")" )
TupleIndex     ::= Digit { Digit }
RecordFieldList  ::= ".." PascalCase | RecordField { "," RecordField } [ "," [ ".." PascalCase ] ]
FieldLabel       ::= SnakeCase | SuppressedVar | PascalCase
```

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

Bracket syntax (`[...]`) defines linear arrays (`[]T`) and associative maps (`[K: V]`). Fixed-arity anonymous products are represented as tuples (`(T1, T2)`). Non-owning inspection uses the orthogonal `view` capability qualifier (`view []T`). The unique set type `Set<T>` and collection type extractors are standard library declarations, not dedicated core syntax.

```ebnf
ArrayType   ::= "[]" TypeExpression
MapType     ::= "[" TypeExpression ":" TypeExpression "]"
TupleType   ::= "(" TypeExpression "," TypeExpression { "," TypeExpression } [ "," ] ")"
TupleExpr   ::= "(" Expression "," Expression { "," Expression } [ "," ] ")"
ArrayExpr   ::= "[" [ Expression { "," Expression } [ "," ] ] "]"
MapExpr     ::= "[" ":" "]" | "[" MapEntry { "," MapEntry } [ "," ] "]"
MapEntry    ::= Expression ":" Expression
```

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
VariantField        ::= [ Identifier ":" ] TypeExpression
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
type Cell = { mut count: int }
let mut source = Cell.{ count: 1 }
let view observed = source
let mut independent = clone(observed)
let immutable: Immut<Cell> = clone_immut(observed)
independent.count = 2
source.count = 3
assert(observed.count == 3)
assert(independent.count == 2)
assert(immutable.count == 1)
-- let mut bad = immutable                -- Error [E0520]: immutable data cannot acquire write permission
```

- **Immutable Data**: `let` guarantees an immutable ordinary reachable graph, with sharing allowed. `Immut<T>` records this guarantee in the type; `Immut<Immut<T>> = Immut<T>`. Field declarations remain unchanged.
- **Ordinary Clone**: `clone` separates the copy's writable storage from its source, preserving internal aliases and cycles. The receiver may choose immutable publication, read-only `var`, writable `let mut`/`var mut`, or a declared [fresh-value storage input](#fresh-values-in-storage-calls). A writable copy with possible internal writable aliases requires the local `^mut` sharing marker; distinct paths inside the copy are not necessarily disjoint.
| Operation | Input | Result |
| :--- | :--- | :--- |
| `clone_immut` | `T` or `Immut<T>` | Independent immutable `Immut<T>` |
| `clone` | `Immut<T>` | Fresh `T`; explicit nested `Immut<U>` fields stay immutable |

Both accept eligible view data and preserve field declarations.
- **Copy Isolation**: Ordinary deep copying does not suspend, invoke user callbacks, or permit an overlapping write during the copy. Both operations preserve the source.
- **Eligibility (`E0530`)**: Check every reachable ordinary constituent. Retained closure environments, scoped resources, tasks, unique receivers, and other non-clonable values cannot be hidden by wrapping or views.
- Immutable environment-free function values are copyable. Opaque resources use only their explicit contracts.

```ril
type Cell = { mut count: int }
fn read(cell: Cell) -> int { cell.count }
let original = Cell.{ count: 1 }
let explicit: Immut<Cell> = original
assert(read(explicit) == 1)
-- let mut upgraded: Cell = explicit   -- Error [E0520]: removing a qualifier does not grant writes
let mut live = Cell.{ count: 1 }
live.count += 1
-- let invalid: Immut<Cell> = live     -- Error [E0535]: an ascription cannot freeze a live graph
```

| Ascription | Requirement |
| :--- | :--- |
| `Immut<T>` to read-only T | Preserve immutable provenance |
| T to `Immut<T>` | Entire ordinary reachable graph already proven immutable (`E0535` otherwise) |

Ascription never copies, freezes, consumes, grants writes, or makes a resource ordinary data.

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
| Record field | Mutable: invariant; read-only: covariant |
| Callable with identical parameter modes | Parameters contravariant; result covariant; actual obligations fit destination rows |
| `&^mut` row bound | Admits `&mut`; never changes parameter modes or handle permissions |
| Array / map | Element and key/value types invariant |
| Tuple | Components invariant; writable access permits slot replacement |
| Sum / nominal arguments | Invariant; transparent aliases retain the expanded type's identity |

Read-only access and Immut qualification add no container subtyping.



### Complete Provenance and Optional Annotations

```ril
fn identity<T>(value: T) -> T { value }
type Cell = { mut count: int }
let mut source = Cell.{ count: 0 }
let view packet = .{ item: identity(source) }
let view observed = identity(packet.item)
source.count += 1
assert(observed.count == 1)
-- let hidden = identity(packet.item)  -- Error [E0535]: source still has a surviving writer
-- let mut stolen = identity(observed) -- Error [E0528]: read-only return cannot grant write authority
```

- **Complete Static Provenance**: Track possible origins, permissions, immutable/live facts, aliases, retention/escape dependencies, and scope/task ownership for all storage, references, environments, and resources. Conservative judgments may overapproximate execution; obligations cannot be erased.
- **Propagation**: Preserve these facts through aggregates, projections, branches, recursion, returns, calls, opaque boundaries, handlers, cleanup, and modules. Existing-reference permissions may be preserved or reduced, never upgraded by these operations. Every handle in an access path and the stored constituent limit the resulting authority; a field's lack of slot-replacement permission does not itself reduce its child reference's permission. Independent scalar copies carry no reference authority; capturing a scalar cell retains its origin.
- **No Semantic Erasure**: An omitted annotation, plain `-> T`, abbreviated callable type, or ordinary call spelling does not discard these facts. Private source names need not become public identifiers; their semantic dependencies still participate in every access and boundary check. Anonymous captures and symbolic callback obligations remain inferred. Named definitions must declare their concrete invocation obligations; no return modes, symbolic callback-forwarding notation, or call-site annotation is required.
- **Conservative Alternatives**: Retain the union of possible origins, accesses, retention, and escape obligations, and only permissions common to all alternatives. Preserve origin relations between inputs and outputs and between output components: a relation established in every retained alternative remains established after the join. Prune only branches excluded by the specified static computations and typing rules. An unproved run-time condition is not evidence of uniqueness or impossible escape. Unknown overlap remains possible overlap; an incomplete proof cannot authorize a loan, immutable publication, or task crossing that requires it.
- **Recursive Dependencies**: Loop and recursive call dependencies retain possible origins and unresolved relationships, including termination conditions and finite-budget coverage. A cycle is not evidence of freshness, disjointness, non-escape, termination, or an empty callable row. An obligation may be discharged only by an established fact; unresolved dependencies remain obligations at every affected use. Apply the use's existing diagnostic when its required proof is absent.
- **Authority and Discharge**: Prove each permission from a declaration, a traced source, a fresh-data rule, or an explicitly specified resource contract. Local discharge requires all relevant authority roots and environments to be confined; a local variable name or locally handled effect is not evidence of confinement. Minimal concrete capabilities (`E0529`) are calculated under these conservative rules, not arbitrary run-time equivalence.
- **Source Annotations**: Binding modes, explicit mutable arguments, local writable-sharing markers, and required concrete invocation capabilities remain checked. Inference may determine their required spelling, but adding an annotation cannot supply absent authority or change sharing, object identity, or resource ownership. A completion that would require such a semantic change is not a valid annotation-only correction.
- **Diagnostic Provenance**: Semantic diagnostics MUST make the derived access, sharing, escape, and effect obligations and their source explanations available, including facts omitted from source. An explanation identifies the relevant origin or contract, propagation steps, involved use or boundary, and the rule that accepts or rejects it. Multiple possible origins and an unproved disjointness condition must be reported as such, not replaced with a fabricated exact origin. Explanations also apply to accepted programs and inferred obligations; their presentation is optional and cannot change validity.

For the `hidden` error above, the explanation connects `source`'s writer to the read-only `identity` argument and return, `packet.item`, the second return, and the prohibited immutable binding. For `stolen`, it identifies the read-only result permission. These explanations introduce no additional Ril source syntax.

```ril
type Cell = { mut count: int }
fn copy_cell(value: Cell) -> Cell { clone(value) }
fn swap(mut a: Cell, mut b: Cell) &mut {
    let saved = a.count
    a.count = b.count
    b.count = saved
}
let base = Cell.{ count: 0 }
let mut first = copy_cell(base)
let mut second = copy_cell(base)
swap(mut first, mut second)           -- OK: separate evaluations produce separate writable copies
let mut alias = ^mut first
alias.count += 1
-- swap(mut first, mut alias)         -- Error [E0523]: different names for the same writable object
```

- **Local Construction**: A fresh ordinary result may enter `let` when its construction scope or call ends and no external writer or active environment survives. A private fresh result may instead stay writable. Borrowed/external aliases retain their restrictions (`E0528`). Ordinary writable bindings retain their authority until their lexical scope ends; merely having no later textual use does not revoke it. Reassigning `var mut` replaces that binding's path but does not revoke other paths to the old value.

- **Fresh Evaluation**: Each successful ordinary allocation creates new storage distinct from pre-existing storage. A newly constructed aggregate may still contain references to pre-existing objects; freshness of its outer slots does not establish disjointness of its reachable graph. Each ordinary deep clone creates new writable regions isolated from the source and all pre-existing writable regions, preserving aliases within that one copy. Repeated evaluations of one expression do not denote one shared allocation. Calling an arbitrary function twice does not establish freshness; the function's actual return relation must supply it.

- **Initial Writable Reception**: [Fresh storage inputs](#fresh-values-in-storage-calls) may receive unpublished construction authority. Read-only bindings and parameters end this eligibility; allocation identity or last use cannot restore it.

```ril
-- Cell and swap have the preceding contracts; choose_order is a run-time bool input.
fn permute(flag: bool, ^mut a: Cell, ^mut b: Cell) -> (Cell, Cell) &^mut {
    if flag { (^mut a, ^mut b) } else { (^mut b, ^mut a) }
}
let mut left = Cell.{ count: 1 }
let mut right = Cell.{ count: 2 }
let mut pair = permute(choose_order, ^mut left, ^mut right)
swap(mut pair.0, mut pair.1)           -- OK: either ordering preserves the inputs' proven disjointness

let mut cells = [Cell.{ count: 0 }, Cell.{ count: 1 }]
cells[0].count += 1
-- i and j are unconstrained run-time integer inputs:
-- swap(mut cells[i], mut cells[j])   -- Error [E0523]: the indices may select the same writable origin
```

The two components returned by `permute` may each originate in either argument, but are disjoint whenever the two actual inputs are disjoint. That common relation survives the branch and return. Distinct parameter names alone establish no such relation. Unrelated run-time selections retain possible overlap unless an applicable rule proves otherwise.

```ril
type Cell = { mut count: int }
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

Escaped environments and stored writable paths survive their creating scope and still prevent immutable publication. Last-use rules for temporary loans or views do not implicitly consume an ordinary writable binding. Resource consumption follows only its listed contracts.

### Functional Updates via Derive

```ril
type Cell = { mut count: int }
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

- **Input (`E0536`)**: `derive` accepts immutable ordinary data; snapshot a live source with `clone_immut` first. Input `T` yields immutable `T`; input `Immut<T>` yields `Immut<T>`.
- **Draft**: The recipe receives `mut draft`, returns `()`, and may replace fields regardless of their original `mut` markers. An `Immut<T>` draft exposes T under this confined permission; output field declarations remain unchanged.
- **Identity**: Each source object has one draft counterpart, including newly inserted immutable references. Repeated references and cycles are preserved; all draft aliases see the same changes.
- **Sharing**: Copy every affected value/reference region, including changes needed to preserve graph identity. Unaffected immutable regions may be shared. Neither unique ownership nor a new root for a no-op recipe is guaranteed.
- **Insertion (`E0535`)**: Accept immutable references or recipe-local fresh data without outside writers. Inserted immutable objects enter the same draft correspondence before later writes; existing draft aliases retain their identity.
- **Confinement (`E0607`)**: Draft references cannot escape through returns, assignments, containers, or published closures. Non-escaping helper calls are allowed. Publish the immutable result only after normal recipe completion.
- **Abort**: Forward recipe effects and external-state obligations; discharge draft-local writes. Panic/abort publishes no result and preserves all immutable inputs. Unrelated external writes remain committed.

```ril
let mut current = Cell.{ count: 0 }
let view live = current
-- let invalid = live |> derive \mut draft -> { draft.count += 1 }
-- Error [E0536]: derive requires immutable input
let snapshot = clone_immut(live)
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
RecordConstraintField ::= [ "mut" ] Identifier ":" TypeExpression
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
- **Static Value Sorts**: Const parameters admit scalar values and finite immutable aggregate values whose constituents have no resource or callable authority. `ValueType` in the parameter grammar denotes such an admissible value sort, not permission to pass a run-time or live value.
- **Const Generic Evaluation & Purity Invariant (`E0814`, `E0323`)**: Const generic arguments evaluate at compile time within the pure symbolic domain ($\mathbf{Eff} = \emptyset, \mathbf{Cap} = \emptyset$). Non-constant runtime expressions passed to const parameters trigger `E0814`. Arguments failing sort constraints trigger `E0323`.
- **No Untagged Literal or Storage Union Types (`E0318`)**: Concrete values (strings, integers, booleans) and untagged value unions (`int | str`) cannot serve as storage, variable, or binding types (`E0318`). Discrete domain states MUST be modeled via tagged sum types (`type HttpMethod { Get, Post }`). Concrete values enter the type system strictly as compile-time arguments to const parameters (`Buffer<u8, 1024>`, `Matrix<f64, 4>`). Finite type sets (`T: int | f64`) are permitted exclusively as static domain constraints on generic parameters (`TypeSetSort`), which are monomorphized to single rigid types.
- **Function Generic Default Prohibition (`E0317`)**: Function generic parameters cannot declare defaults (`fn f<T = int>` is rejected); function types are inferred bidirectionally at call sites.

```ril
-- Closed Type Set Constraint:
fn add<T: int | f64>(a: T, b: T) -> T { a + b }
assert(add(1, 2) == 3)
assert(add(1.5, 2.5) == 4.0)
-- let bad_add = add("a", "b")          -- Error [E0301]: type 'str' does not satisfy constraint 'int | f64'

-- Pipeline Type Function Constraint:
type Numeric = \T -> match type<T> {
    type<int> | type<i64> | type<f64> -> type<T>,
    _ -> type<never>,
}
fn multiply<T |> Numeric>(a: T, b: T) -> T { a * b }
assert(multiply(3, 4) == 12)
-- let bad_mul = multiply("x", "y")     -- Error [E0301]: type 'str' does not satisfy constraint 'Numeric'

-- Composed Structural and Pipeline Constraint:
type NonZero = \T -> match type<T> {
    type<{ val: int, ..let _ }> -> type<T>,
    _ -> type<never>,
}
fn get_val<T: { val: int, ..R } |> NonZero>(item: T) -> int { item.val }
assert(get_val(.{ val: 42, label: "ok" }) == 42)

type Token<value: f64>(int)
meta let _ = assert(type<Token<0.0>> != type<Token<-0.0>>)
meta let _ = assert(type<Token<0.0 / 0.0>> == type<Token<0.0 / 0.0>>)

type Choose = \entries: [str: int] ->
    if Map::keys(entries)[0] == "a" { type<int> } else { type<str> }
type FirstOrder = Choose<["a": 1, "b": 2]>  -- int
type OtherOrder = Choose<["b": 2, "a": 1]>  -- str
```

Static argument equivalence determines type and effect instantiation identity. It is distinct from run-time `==`. Arguments must first have the same admitted sort.

| Static value | Equivalence |
| :--- | :--- |
| Booleans, integers, strings, bytes, unit | Exact value; strings are exact scalar sequences |
| Floating values | Canonical IEEE bit representation; signed zeros differ, canonical NaNs agree |
| Records | Same labels and recursively equivalent fields; written field order is irrelevant |
| Arrays / tuples | Same length and recursively equivalent positional values |
| Maps / sets | Same insertion-ordered entries/members, recursively equivalent |
| Sums / nominal or ordinary opaque values | Same declaration/instance identity and tag where present, then equivalent representation constituents |
| Integer ranges | Same endpoint type, endpoints, and inclusive/exclusive flag |

Sharing multiplicity and allocation identity do not distinguish static arguments. For eligible finite cyclic graphs, use the greatest relation satisfying the table's constituent rules. Live values, callable authority, and resources remain ineligible. Type equality compares these instantiation identities; it does not substitute ordinary collection or floating-point equality.

```ril
-- type TooMany = Option<int, str>    -- Error [E0340]: Option has one generic parameter
fn make_empty<T>() -> []T { [] }
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
fn check_buf(runtime_size: int) {
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
type StateNode = { mut count: int, tag: str }
type ReaderFn = fn() -> str @Io
type AsyncWorker<T> = fn(T) -> () @AsyncIo
type Mutator<T> = fn(mut target: T) -> () &mut
type SharedLogger = fn(str) -> () &closure &^mut
type SocketHandler =
    fn(mut buffer: []u8, timeout_ms: int) -> Result<int, IoError> @Fiber &mut

type TaskStatus {
    Pending,
    Running(fn() -> () @Async),
    Mutating(fn(mut StateNode) -> () &mut),
    Suspended({ duration_ms: int }),
    Completed(int),
}
let status: TaskStatus = Running(\-> Fiber::yield())
assert(status is Running)

type ValidChannel = {
    mut buffer: []u8,
    stream: fn() -> str @Io,
    writer: fn(mut []u8) -> () &mut,
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

fn test_valid_binding() @Io {
    let result: str = Io::read_line() -- The call has Io; the resulting str has no effect suffix
    assert(result == "ready")
}
assert(ch.stream() == "ready")
test_valid_binding()

halt type MakeNullable = \T -> type<?T>
type NullableInt = MakeNullable<int>
```

```ril
-- Io has the preceding declaration. Module storage for the named-state cases:
var app_cache = 0
fn update_cache() &{mut app_cache} { app_cache += 1 }

-- type BadEffect = @Io               -- Error [E0330]: a single effect is not a data type
-- type BadCombined = @Io + Async     -- Error [E0330]: neither is an effect set
-- type BadMut = &mut                 -- Error [E0331]
-- type BadShare = &^mut              -- Error [E0331]
-- type BadGlobal = &{mut app_cache}   -- Error [E0331]
-- type BadClosure = &closure         -- Error [E0331]

-- type BadVariant { Running @Async } -- Error [E0332]: tag annotation
-- type BadMutableVariant { Mutating &mut } -- Error [E0332]: capability on a tag
-- type BadPayload { Suspended(int) @Fiber } -- Error [E0332]: payload does not permit a suffix
-- type BadField = { value: str @Io } -- Error [E0333]
-- type BadMutableField = { buffer: []u8 &mut } -- Error [E0333]: field type is not a callable
-- type BadNamedField = { value: int &{mut app_cache} } -- Error [E0333]
-- type BadTuple = (str @Io, int)     -- Error [E0333]
-- type BadArray = []int @Async       -- Error [E0613]

-- type BadEffectBound<T: @Io> = T    -- Error [E0334]
-- type BadStateBound<T: &mut> = T    -- Error [E0334]
-- halt type BadTypeFn = \T -> type<T> @Io -- Error [E0335]
-- type BadTypeState = \T -> type<T> &mut  -- Error [E0335]
-- halt type BadTypeBoth = \T -> type<T> @Async &closure -- Error [E0335]
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
                   | "type" "<" TypeExpression ">"
                   | MappedRecordType | MappedTupleType
PrimaryType      ::= PrimitiveType | NominalRef | "(" TypeExpression ")"
NominalRef       ::= QualifiedName [ GenericArgs ]
```

| Position | Rule |
| :--- | :--- |
| Data types | Inert shapes: structural products/collections, sums and GADTs, nominal wrappers, opaque types, or pure type-function results |
| Record field `mut` | Slot-replacement permission in the shape; no ambient capability |
| Callable arrow | Carries latent effects and capabilities; callable values may be stored, passed, returned, and nested in data |
| Bare `@Eff` / `&Cap` as a type | `E0330` / `E0331`; effects use `eff` declarations, capabilities are not standalone values or types |
| Direct effect/capability suffix on a variant | `E0332`, with or without a payload |
| Direct effect/capability suffix on a record field or tuple component | `E0333`; a callable constituent may carry its own suffix |
| Effect/capability constraint on a generic parameter | `E0334`; shape, kind, const, and static-key constraints remain allowed |
| Effect/capability annotation on a type function | `E0335` |
| Effect annotation on a value binding or non-callable array expression | `E0613` |

Binding and origin permissions govern access. Effects govern evaluation and handler dispatch; completed passive values have no direct effect annotation. Stored callables retain invocation obligations. Termination and finite-budget coverage remain separate invocation judgments, not types, capabilities, or effect labels.

## Declarations and Bindings

### Binding Permissions and Storage Matrix

| Binding | Slot reassignment | Writes through this binding | Data guarantee |
| :--- | :---: | :--- | :--- |
| `let` | No | No | Entire ordinary reachable graph immutable; sharing permitted |
| `let mut` | No | Granted interior/environment writes | Pinned reference; not necessarily unique |
| `var` | Yes | No interior/environment writes | Referenced data remains read-only; immutable/live facts are preserved |
| `var mut` | Yes | Granted interior/environment writes | Each assigned value must supply write authority; no permission upgrade |
| `let view` | No | No | Live observation of stable permitted origins; not immutable |

- **Authority Use (`E0527`)**: A mutable binding/parameter must perform a write, reassignment, mutable invocation, retention, or authorized transfer on a statically possible path. An annotation or ineffective forwarding alone does not count. This does not require a write on every execution.

```ril
type Document = { mut title: str }
let document = Document.{ title: "Guide" }
let alias = document                   -- Immutable sharing
let mut draft = clone(document)        -- Independent writable graph
draft.title = "Draft"
let view observer = draft              -- Live observation
draft.title = "Published"
assert(observer.title == "Published" && alias.title == "Guide")
var selected = document
selected = alias                      -- Rebinds an immutable reference; no interior write permission
```

### Immutable Bindings

```ril
type Counter = { mut count: int }
let mut source = Counter.{ count: 0 }
let view observer = source
-- let bad = source                    -- Error [E0535]: a surviving writer prevents immutable publication
-- let hidden = .{ child: observer }   -- Error [E0535]: wrapping a live reference does not make it immutable
source.count += 1
let copied_count = observer.count      -- OK: independent scalar value
assert(copied_count == 1)
```

- **Binding to let (`E0535`)**: Accept immutable data or a fresh ordinary graph without surviving external writers. Reject live views, captured live cells, and mutable environments. Binding neither clones data nor revokes another writer.

```ril
fn make_items() -> []int {
    let mut items: []int = []
    items !> Array::push(1)
    items
}
let items = make_items()               -- OK: construction authority ended; immutable publication
let alias = items                     -- OK: multiple references to immutable data
-- let mut stolen = items             -- Error [E0520]: ordinary aliasing cannot recover write permission
```

```ebnf
LetDecl ::= [ "pub" ] "let" Pattern [ ":" TypeExpression ] "=" Expression [ "else" Block ]
```

```ril
let x = 10                             -- Immutable integer binding
let (a, b) = (1, 2)                    -- Destructuring tuple binding
-- x = 20                              -- Error [E0501]: cannot reassign immutable binding 'x'

type Config = { capacity: int, items: []int }
let cfg = Config.{ capacity: 64, items: [] }
let .{ var capacity, items: _ } = cfg
capacity += 1                         -- OK: independent scalar copy
-- let .{ capacity: _, mut items } = cfg -- Error [E0521]: immutable reference cannot acquire write permission
```

### Pinned Mutable Handles

`let mut` supplies the pinned interior/environment authority in the [binding matrix](#binding-permissions-and-storage-matrix).

#### Normative Rules for Pinned Handles
- **Pinned Handle Invariant (`E0502`)**: A `let mut` handle is permanently pinned to its initial heap allocation. Reassigning the identifier (`handle = new_obj`) is statically rejected under `E0502: PinnedHandleReassignmentError`.
- **Value Type Prohibition (`E0402`)**: Primitive value types (`int`, `bool`, `f64`, etc.) have no interior mutable fields. Declaring a value type as `let mut` is statically rejected under `E0402: ValueTypePinnedMutError`; mutable value types MUST be declared with `var`.
- **Live View Stability**: Pinned mutable handles provide guaranteed reference stability as roots for live views (`let view`).

```ebnf
LetMutDecl ::= "let" "mut" Pattern [ ":" TypeExpression ] "=" Expression
```

```ril
type Buffer = { mut items: []int }
let mut buf = Buffer.{ items: [1, 2] }

-- In-place interior mutation is permitted:
buf.items !> Array::push(3)            -- OK: in-place write to pinned buffer

-- Handle reassignment is statically rejected:
-- buf = Buffer.{ items: [] }          -- Error [E0502]: use 'var mut' for both reassignment and interior writes

-- Value types under let mut are rejected:
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

`var` and `var mut` use the [binding matrix](#binding-permissions-and-storage-matrix); every replacement is checked against its actual origins.

#### Normative Rules for Reassignable Variables
- **Replacement (`E0520`)**: Every `var mut` assignment must supply writable authority under [provenance](#complete-provenance-and-optional-annotations); an additional local writable alias requires `^mut`.
- **Value Types (`E0402`)**: Scalars use plain `var`; `var mut` requires reference data or a writable callable environment.
- **Read-Only Live Values**: Plain `var` may hold a live read-only reference without making it immutable. Neither `var` nor `var mut` is a stable origin for `let view` (`E0531`), including through intermediate aliases.
- **Authority Use (`E0527`)**: Plain `var` must exercise reassignment on a statically possible path. `var mut` must exercise both its reassignable slot and its interior/environment authority; use `let mut` when only pinned interior authority is needed. Uses follow the [binding authority rules](#binding-permissions-and-storage-matrix).

```ebnf
VarDecl ::= [ "pub" ] "var" [ "mut" ] Pattern [ ":" TypeExpression ] "=" Expression [ "else" Block ]
```

```ril
-- Reassignable primitive scalar:
var counter = 0
counter += 1                           -- OK: reassignable scalar
counter = 10                           -- OK: direct reassignment
assert(counter == 10)

-- Fully mutable reference variable:
var mut active_buf = Buffer.{ items: [1] }
active_buf.items !> Array::push(2)     -- OK: in-place mutation
active_buf = Buffer.{ items: [10, 20] } -- OK: handle reassignment permitted on 'var mut'
assert(len(active_buf.items) == 2)

var readonly_buf = Buffer.{ items: [] }
readonly_buf = Buffer.{ items: [1] }  -- OK: replaces the slot
-- readonly_buf.items !> Array::push(2) -- Error [E0520]: plain var grants no interior write authority
-- var mut scalar = 0                -- Error [E0402]: scalar mutation uses plain var

-- Read-only cursor over immutable structures:
type Node = { val: int, following: ?Node }
let ro_node2 = Node.{ val: 2, following: None }
let ro_node1 = Node.{ val: 1, following: Some(ro_node2) }

var cursor = ro_node1                  -- OK: 'cursor' is a reassignable ReadOnly handle
assert(cursor.val == 1)
cursor = ro_node2                      -- OK: reassignment permitted to matching ReadOnly type
-- cursor.val = 99                     -- Error [E0520]: cannot mutate field 'val' through read-only handle 'cursor'

-- Pattern-level var destructuring:
var (start_idx, end_idx) = (0, 10)
start_idx += 1; end_idx -= 1           -- OK: both variables reassignable

-- Definite Mutation Invariant:
-- var unused_var = 100                -- Error [E0527]: variable 'unused_var' declared 'var' but never modified or reassigned
```

### Scoped Resource Bindings

```ril
type Resource = { mut name: str, mut on_close: fn() -> () }
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
| Ordinary resource | Accessible `on_close: fn() -> ()` required (`E0541`) |
| Opaque resource | Requires an explicit scoped-cleanup contract; opacity alone supplies none (`E0541`) |
| Registration | After successful initialization; per binding and per loop activation; failed initialization registers nothing |
| Exit | Invoke once in reverse registration order, including cancellation/abort; double-fault exception below |
| Callback selection | Read the current `on_close` at exit; retain no earlier snapshot. Opaque resources use their specified action |
| Initialization/replacement | Preserve cleanup eligibility and permissions; no residual effects (`E0616`), and prove finite cleanup (`E0617`) |
| Mutable cleanup environment | Requires `let scoped mut` and a mutable `on_close` field; cleanup invocation satisfies `E0527` |
| Other binding modes | Plain `let scoped` requires immutable data; rebinding: `E0502`; `var`/`var mut`: `E0532` |
| Invocation | Internal handlers and permitted writes allowed; check exclusivity then, not as a continuous registration loan |
| Escape | Views, closures, containers, and transfer cannot carry scoped authority out (`E0604`); detached ordinary-data copies are exempt |
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
ScopedDecl ::= "let" "scoped" [ "mut" ] Identifier [ ":" TypeExpression ] "=" Expression
```

### Live View Bindings

```ebnf
LetViewDecl ::= "let" "view" Identifier [ ":" TypeExpression ] "=" Expression
VarViewDecl ::= "var" "view" Identifier [ ":" TypeExpression ] "=" Expression
```

```ril
type Cell = { mut count: int }
let mut cell = Cell.{ count: 1 }
let view observed = cell
let view read_count = \-> observed.count
cell.count = 2
assert(read_count() == 2)
-- let bad_reader = \-> observed.count -- Error [E0535]: the captured live origin is not immutable
-- mutate(mut observed)               -- Error [E0520]: a view cannot supply mutable authority
-- let view bad_fresh = Cell.{ count: 0 } -- Error [E0543]: fresh initializers cannot bind directly to view
let snapshot = clone_immut(observed)   -- OK: snapshot, not a live alias
```

- **Origins and Capabilities**: `view` is an orthogonal read-only capability applied to GC-managed reference types (`[]T`, `[K: V]`, records, and sum types). It grants non-owning inspection over existing storage. Fresh initializers (`new T`) cannot bind directly to `let view` or `var view` (`E0543: FreshTargetViewError`); passing `new T` to a `view` parameter materializes an anonymous temporary. Taking `view` over a primitive scalar is rejected (`E0402`).
- **Single Evaluation**: Keep the initializer's resulting reference, not a reactive expression. Replacing `parent.child` leaves an existing child view safely observing the old heap object (preserved via GC root tracking). Reachable data outlives the root identifier.
- **Observer Closure**: It may read pinned live origins but cannot write captures. Effects remain independent obligations; read-only observation needs no artificial mutation for `E0527`.
- **Permissions**: A view cannot supply `mut`/`^mut` (`E0520`) or become immutable through aliasing without an explicit `clone` (`E0535`). Scalars copy independently; references keep their origins. Eligible view data supports `clone`/`clone_immut`, but not `derive` (`E0536`).
- **Task Confinement (`E0601`)**: A live view, or any closure/container containing it, cannot cross a concurrent task boundary. Deeply immutable data can cross it.

```ril
type Parent = { mut child: Cell }
let mut parent = Parent.{ child: Cell.{ count: 1 } }
let view child = parent.child
parent.child = Cell.{ count: 9 }
assert(child.count == 1)                -- Keeps the original child, not a reactive projection

type TaskStatus { Pending(str), Finished(int) }
let mut tasks: []TaskStatus = [TaskStatus::Pending("waiting")]
let view v = tasks[0]                   -- 'v' holds a read-only view of the Pending object
tasks[0] = TaskStatus::Finished(42)     -- Slot 0 is updated; 'v' safely keeps the original object
```

### Type Declarations and Opaque Types

```ebnf
TypeDecl         ::= [ "pub" ] [ "halt" ] "type" PascalCase [ GenericParams ] [ WhereClause ] "=" TypeExpression
OpaqueTypeDecl   ::= [ "pub" ] "opaque" "type" PascalCase [ GenericParams ] [ WhereClause ] "=" TypeExpression
LocalTypeDecl    ::= TypeDecl | OpaqueTypeDecl | NominalDecl | SumTypeDecl
WhereClause      ::= SignatureWhereClause
TypeList         ::= TypeExpression { "," TypeExpression } [ "," ]
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
                     "(" [ ParameterList ] ")" [ ReturnType ]
                     [ EffectAnnot ] [ StateAnnot ]
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
- **Ordinary Exchange**: Ordinary inputs, outputs, and constants must be scalars or deeply immutable ordinary data with no surviving foreign writer. They cannot contain live views, callables, tasks, or resources. This excludes even immutable environment-free function values: only a separate callback parameter receives the temporary callback contract below. An immutable returned graph may share immutable storage; a plain return type does not establish freshness or write permission (`E0528`).
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
pub fn query_selector(win: DomWindow, sel: str) -> Result<DomElement, DomError> @Fiber
pub fn read_attribute(elem: DomElement, key: str) -> Result<?str, DomError> @Fiber

-- Body prohibition in .d.ril (E0901):
-- pub fn bad_body() -> int { 42 }     -- Error [E0901]: functions in '.d.ril' cannot have an implementation body
-- pub let BAD_CONST: int = 100        -- Error [E0901]: constants in '.d.ril' cannot have an initializer expression

-- Opaque penetration prohibited (E0907):
-- fn test_penetrate(elem: DomElement) {
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
pub fn transform_text(text: str, transform: Transformer) -> str @{} &{}
where
    type Transformer = fn(str) -> str

-- pub fn edit(mut items: []int) @Fiber &mut
-- Error [E0908]: no listed contract grants ordinary mutable-data exchange
-- pub fn keep(^mut callback: fn() -> () &closure) &^mut
-- Error [E0908]: default callback authority cannot be retained
-- pub fn hidden_callback() -> { action: fn() -> () }
-- Error [E0908]: ordinary returned data cannot conceal callable authority
-- pub fn use_writer(callback: fn(mut []int) -> () &mut)
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
                  | CallExpr | AnonFnExpr | AccessorExpr | MatchExpr | TypeMatchExpr
                  | IfExpr | LoopExpr | WhileExpr | ForExpr | ControlTransfer
                  | ResumeExpr | AssignmentExpr | UnaryExpr | BinaryExpr | SharingExpr
                  | MemberExpr | IndexExpr | RangeExpr | IsExpr
                  | Expression "?" | "type" "<" TypeExpression ">" | "keyof" TypeExpression
UnaryExpr       ::= ( "-" | "!" | "~" ) Expression
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
| **1** | `.` `?.` `?[` `[]` `()` `::` postfix `?` | Left | Member access (field or tuple index), safe navigation, indexing, invocation, postfix `?` |
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
assert(Map::keys(ordered) == ["b", "a"]) -- Replacing a value preserves its key's position
-- let bad_keys: [f64: int] = [nan: 1] -- Error [E0328]: floating-point keys are not admitted
-- let graph_key = [.{ id: 1 }: 0]    -- Error [E0328]: immutable records are still reference-type keys
```

`!=` negates `==`. Equality requires compatible same-typed values (`E0301` otherwise), except the Option/None tag test below.

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
| Floats, reference graphs (even Immut), callables, resources | `E0328` |

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

### Range and Slicing Expressions

Only sequence sub-range indexing permits omitted range endpoints.

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
let sub = arr[1..4]                   -- Evaluates to new []int containing [20, 30, 40]
let prefix = arr[..3]                 -- [10, 20, 30]
let suffix = arr[2..]                 -- [30, 40, 50]
let empty = arr[len(arr)..len(arr)]   -- OK: empty sub-array at the end
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

Ranges are finite even when their integer cardinality exceeds `int`. Their value representation does not allocate one element per member. Sub-range indexing instead uses `int` endpoints (`E0301` for another type) and the bounds below; reversed bounds panic.

```ril
let mut source: []int = [1, 2, 3]
let sub: []int = source[0..2]         -- Constructs an independent new []int [1, 2]
source !> Array::push(4)              -- Modifying source does not affect sub
assert(len(source) == 4 && len(sub) == 2)

let view observer = source            -- Read-only view over source dynamic array
assert(observer[0] == 1)
-- observer[0] = 9                    -- Error [E0520]: a view grants no write authority

-- Mutable element sharing marker (^mut):
type Cell = { mut count: int }
let mut cells: []mut Cell = [mut Cell.{ count: 1 }, mut Cell.{ count: 2 }]
let mut sub_cells = ^mut cells[0..1]  -- OK: '^mut' acknowledges duplicated writable paths
-- let mut bad = cells[0..1]          -- Error [E0510]: new local writable alias needs '^mut'

-- Primitive sub-sequences:
let s = "hello, 世界"
let s_sub: str = s[0..5]              -- "hello" (Unicode scalar coordinates)
assert(s[0..len(s)] == s)             -- Coordinate alignment ensures safe full slicing

let b: bytes = b"RIFF\x00\x01"
let b_sub: bytes = b[0..4]            -- b"RIFF" (byte sub-sequence)
let view b_view: []u8 = b             -- OK: O(1) zero-copy view coercion
```

- **Independent Sub-Array Allocation**: Indexing an array with a range expression `arr[a..b]` or `arr[a..=b]` evaluates bounds once and constructs an independent, fresh dynamic array of static type **`new []T`**. Modifications to the sub-array's structure (`push`, `pop`, `insert`, `clear`) never affect the original array, and vice versa.
- **Bounds**: For length N, a half-open range requires `0 <= lower <= upper <= N`; equal bounds produce an empty sub-array, including at N. Omitted lower bounds mean zero; an omitted upper bound denotes the exclusive end N. A written inclusive upper bound h requires `0 <= lower <= h < N` and selects through h. Negative, reversed, or out-of-range bounds panic; bounds are never clamped. Safe sub-range lookup (`arr?[a..b]`) returns `?[]T` (`None` when out of bounds).
- **Element Reference Semantics & Sharing Marker (`E0510`)**: Deeply immutable elements are shallow-copied as shared immutable references without markers. When element type `T` contains mutable references, creating a new sub-array duplicates writable paths to existing heap objects, requiring the explicit `^mut` sharing marker (`E0510`) when binding to `let mut`.
- **Primitive Sub-Sequences**:
  - `str[a..b]` and `str[a..=b]` evaluate to an independent `str` based on Unicode scalar (code point) indices ($0 \le a \le b \le \text{scalar\_len}$). Slicing and string length share the same Unicode scalar coordinate system; `s[0..len(s)]` safely selects the entire text.
  - `bytes[a..b]` and `bytes[a..=b]` evaluate to an independent `bytes` byte sub-sequence ($0 \le a \le b \le \text{byte\_len}$).
- **Observation via `view`**: Non-owning inspection of an entire array without copying is achieved via the `view` capability qualifier (`view []T`). Modifying an array structurally (`push`/`pop`/`clear`) while actively iterating over it is statically rejected under `E0526`.

### Pipeline Operators

- **Linear Pipeline (`|>`)**: Passes the left expression as the first argument to the right callable: `x |> f` desugars to `f(x)`.
- **Mutating Pipeline (`!>`)**: Passes the mutable left lvalue to the right mutating callable: `x !> f` desugars to `f(mut x)`. It never supplies `^mut` implicitly.
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
| `Result<T, E> ?? handler` | Unwrap T; skip handler | Evaluate and invoke `fn(E) -> T` once; raw T is `E0711` |

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
| Range index | Use ordinary sub-range syntax and bounds rules |

### Record Construction and Functional Update

```ebnf
RecordExpr      ::= [ TypeReference ] ".{" [ RecordValueField { "," RecordValueField } [ "," ] ] "}"
RecordValueField ::= FieldLabel [ ":" Expression ] | ".." Expression
```

Explicit fields override equally named fields from a value spread, independent of their written position. Multiple explicit definitions of one field are `E0210`; conflicting spread sources without an explicit override are `E0211`. A spread copies values and references with their existing permissions; it does not deep-clone live data or make it immutable.

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
type Buffer = { mut capacity: int }
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
                      | VarDecl
                      | ScopedDecl
                      | LetViewDecl
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
    fn read_value() -> int &{closure, value} { value }
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
    fn walk_grid(g: [][]int) @Search {
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
-- fn bad_effect_leak() -> int @LocalStep { -- Error [E0618]: local effect 'LocalStep' cannot escape enclosing block to function signature
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

Evaluate the source once. Read each collection entry when visited; a later element replacement can be observed, but structural mutation during traversal remains `E0526`. Element patterns receive read-only access with the source's actual immutable/live facts. They do not publish live references as immutable data or grant element writers (`E0521`); independent scalar `var` pattern copies remain permitted. Existing source permissions and origins survive destructuring.

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
fn log_positive(val: int) @Fiber {
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
    let Some(id) = data["account_id"] else {
        return Err("missing account_id") -- OK: diverges via 'return', binds variable 'id'
    }
    let Some(user) = fetch_user(id)? else {
        return Err("missing user")     -- OK: propagates error via '?' or diverges via 'return'
    }

    -- Non-diverging 'else' is statically rejected:
    -- let Some(name) = data["name"] else {
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
                     | TuplePattern | ArrayPattern | RecordPattern | ConstructorPattern | RangePattern
BindingModifier    ::= "mut" | "var" [ "mut" ]
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

A tuple or array pattern without a rest requires exactly its written number of elements. With a rest, its subject must contain at least the number of non-rest elements; prefix and suffix patterns select from their corresponding ends, and the rest may be empty. Tuple rests are anonymous. In an array pattern, a named rest `..rest` binds the remaining elements as an independent sub-array `new []T` (or `view []T` when matching over a view).

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
let [x, y, z] = numbers[0..3]                  -- OK: matching 3-element sub-array
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
   - `let mut`: Tag identity is pinned (`E0502`); `mut` fields invalidate upon write.
- **Transitive Latent Havoc**: Invoking a callable whose effective writes reach v, through a global or captured group, a contract reference, a callback, or an active handler, resets the affected refinement to $T_{\text{root}}$. Group spelling does not change the actual write origin.
- **Anti-Aliasing (`E0533`)**: Preserving a live-origin refinement across a call requires proof that the call's possible writes are independent of that origin. Unknown overlap uses `E0533`; a known write invalidating an established refinement uses `E0310`. A view does not supply independence. The examples below contrast both failures with an immutable snapshot.
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
type Cell = { mut value: ?int }

-- E0533: the callback's possible writes are not known to be independent.
-- An omitted state row on fn() -> () preserves actual obligations; it does not promise purity.
fn unknown_writer(mut cell: Cell, action: fn() -> ()) &mut {
    if cell.value != None {
        let before = cell.value + 1           -- OK: narrowed to int
        action()                              -- Cannot prove that cell.value stays unchanged
        -- let after = cell.value + 1         -- Error [E0533]: unknown overlap with the live origin
    }
    cell.value = None
}

-- E0310: this callee is known to write the very field that was narrowed.
fn clear(mut cell: Cell) &mut { cell.value = None }
fn known_writer(mut cell: Cell) &mut {
    if cell.value != None {
        clear(mut cell)                       -- Known write invalidates cell.value's refinement
        -- let after = cell.value + 1         -- Error [E0310]: the earlier narrowing no longer applies
    }
}

-- OK: the same unknown callback cannot change an independent immutable snapshot.
fn snapshot_before_callback(mut cell: Cell, action: fn() -> ()) &mut {
    let snapshot = clone_immut(cell)
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
fn test_invalidation() {
    var opt: ?int = Some(42)
    if opt != None {
        let _ = opt + 1                        -- OK: opt is int
        opt = None                             -- Reassignment: refinement invalidated
        -- let bad = opt + 2                   -- Error [E0310]: variable 'opt' was narrowed to 'int', but refinement was invalidated by reassignment; current flow type is '?int'
    }
}

-- Contradictory narrowing rejection (E0311):
fn test_contradiction(g: Geometry) {
    if g is Geometry::Circle {
        -- if g is Geometry::Rect {            -- Error [E0311]: condition 'g is Geometry::Rect' is statically unsatisfiable; target is already narrowed to 'Geometry::Circle'
        --     println("unreachable")
        -- }
    }
}

-- Reassignable roots cannot be laundered into pinned views:
fn test_aliased_hazard() {
    var raw: ?int = Some(10)
    -- let view v = raw                        -- Error [E0531]: a var slot is not a pinned view origin
    raw = None                                -- Exercises the reassignable slot
}

-- is reads existing names and narrows the subject without binding payload names:
fn test_non_binding_predicate(g: Geometry) {
    if g is Geometry::Circle && g.0 > 5.0 {
        let radius = g.0                       -- OK: payload access via .0
        -- let escaped = r                     -- Error [E0204]: is introduced no r
    }
}

-- Transitive Latent Havoc via mutating call:
fn test_latent_havoc() {
    var count: ?int = Some(10)
    if count != None {
        let mut step = \-> &{closure, mut count} { count = None }
        step()                                 -- Mutating call invalidates 'count'
        -- let bad_use = count + 1             -- Error [E0310]: variable 'count' was narrowed to 'int', but refinement was invalidated by mutating call 'step()'; current flow type is '?int'
    }
}

-- Generic confinement: bare type parameter rejected:
fn test_generic_confinement<T>(x: Geometry) {
    -- if x is T {                             -- Error [E0301]: cannot test unconstrained generic type parameter 'T' in narrowing predicate
    --     println("invalid")
    -- }
}

-- Dead-path mutation phase ordering:
fn test_dead_write_phase_ordering() {
    -- var unused: ?int = Some(10)            -- Error [E0527]: variable 'unused' declared 'var' is never modified along reachable paths
    -- if false {
    --     unused = Some(20)                  -- Write in statically unreachable branch does not satisfy Definite Mutation Invariant
    -- }
}

-- Path depth bound (depth <= 3 tracked; depth > 3 requires local 'let' anchor):
fn test_bounded_path_depth(root: { a: ?{ b: ?{ c: ?{ d: int } } } }) {
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
                         "(" [ ParameterList ] ")" [ ReturnType ] [ EffectAnnot ] [ StateAnnot ]
                         [ SignatureWhereClause ] Block
SignatureWhereClause ::= "where" SignatureWhereItem { Separator SignatureWhereItem } [ Separator ]
SignatureWhereItem   ::= LocalTypeDecl
ParameterList        ::= Parameter { "," Parameter } [ "," ]
Parameter            ::= [ ParameterMode ] Identifier [ ":" TypeExpression ] [ "=" Expression ]

Argument             ::= [ Identifier ":" ] ( ParameterMode AssignTarget | Expression )
ArgumentList         ::= Argument { "," Argument } [ "," ]
CallExpr             ::= Expression "(" [ ArgumentList ] ")" [ TrailingClosure ] | Expression TrailingClosure
TrailingClosure      ::= AnonFnExpr
CallableType     ::= "fn" "(" [ ParameterTypeList ] ")" [ "->" TypeExpression ] [ EffectAnnot ] [ StateAnnot ]
ParameterTypeList::= ParameterTypeItem { "," ParameterTypeItem } [ "," ]
ParameterTypeItem ::= [ ParameterMode ] [ SnakeCase ":" ] TypeExpression
ReturnType       ::= "->" TypeExpression
```

Leading `mut`/`^mut` arguments require assignable targets (`E0410` for `f(^mut clone(x))`). A parenthesized sharing expression is an ordinary argument: it cannot satisfy a mutable formal (`E0405`) or retain an existing writer. [Fresh storage inputs](#fresh-values-in-storage-calls) may receive its initial construction authority; other ordinary parameters remain read-only. Constructors follow the aggregate sharing rules.

```ril
type DeferredFactory = fn() -> fn() -> int @Io -- Io belongs to the returned callable
type EffectfulFactory = fn() -> (fn() -> int) @Io -- Io belongs to the factory
type CapturingFactory = fn() -> (fn() -> int &closure) &capture
```

Arrows associate right; effect/state suffixes bind to the nearest callable not closed by parentheses. Omitted returns mean `-> ()` on named functions, callable types, and effect operations. Anonymous results are inferred.

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
) -> Result<[]R, E> @Async &mut &{mut audit_log}
where
    type TransformFn<In, Out, Err> = fn(In) -> Result<Out, Err> @Async
    type AuditSink<Item>           = fn(Item) -> () &{mut audit_log} &closure
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
| **Environment Capture** | Explicit named origins; block-local values can retain an environment | None (no captured state) | Actual lexical environment, abbreviated in types by `&closure` |
| **Type Representation** | Item identity / `fn(P) -> R` | `fn(P) -> R` | `fn(P) -> R &closure` |
| **Handle Requirement** | Direct declaration call; stored values follow actual environment permissions | Callable via `let` handle | `let` (immutable), `let view` (live observer), or writable handle (mutable environment) |

### Callable Contracts

```ril
fn next_value(n: int) -> int {
    var result = n
    result += 1
    result
}
var global_count = 0
fn tick() &{mut global_count} { global_count += 1 }
fn visible() &{mut global_count} { tick() }
-- fn hidden() { tick() }             -- Error [E0510]: the ordinary wrapper has undeclared concrete state

eff Log { write(str) -> () }
fn logged() @Log { Log::write("event") }
-- fn hidden_effect() { logged() }    -- Error [E0612]: concrete residual effects require declaration
```

- **Named Definitions**: Module-level and block-local `fn` definitions obey the same rule. After lawful handling and local discharge, their current invocation has no concrete state or residual effect obligations unless explicitly declared. Known obligations inherited from another callable are concrete too; missing state is `E0510`, and missing effects are `E0612`.
- **Local Purity**: Mutation of confined local storage, immutable publication of eligible construction results, and call-local environments do not by themselves require outward state annotations. Creating a surviving environment or an additional surviving writer still requires the applicable `&capture`, `&^mut`, or named-source declaration.
- **Callback Dependence**: Obligations that genuinely depend on callable values supplied through formal parameters may be inferred and forwarded symbolically. This includes callable constituents reached through a parameter's fields, elements, projections, or preserved aliases; the dependency remains tied to the actual parameter value. Having such a parameter or returning a callable is not permission to infer unrelated concrete obligations. A caller that supplies a known callable, directly or inside an aggregate, must declare the resulting concrete obligations after its own handling and local discharge.
- **Anonymous Definitions**: Anonymous functions may infer their obligations, including captures. Those obligations remain checked at every use and cannot conceal concrete state or effects from an enclosing named invocation. Latent body operations are obligations of the later invocation; creating a callable does not execute them.

```ril
fn invoke(action: fn() -> ()) { action() }
fn declared_state() &{mut global_count} { invoke(tick) }
fn declared_effect() @Log { invoke(logged) }
-- fn hidden_through_callback() { invoke(tick) } -- Error [E0510]: this caller's dependency is concrete
-- fn hidden_through_alias() { let action = tick; action() } -- Error [E0510]
-- fn fixed_conflict(action: fn() -> ()) &{} { tick(); action() }
-- Error [E0534]: a closed definition already contains concrete state
fn invoke_pure(action: fn() -> ()) @{} &{} { action() }
fn nothing() {}
invoke_pure(nothing)                  -- OK
-- invoke_pure(tick)                 -- Error [E0534]: total state is not empty
-- invoke_pure(logged)               -- Error [E0534]: total effect row is not empty

type Actions = { run: fn() -> () }
fn invoke_field(actions: Actions) { actions.run() }
fn declared_field() &{mut global_count} { invoke_field(.{ run: tick }) }
-- fn hidden_field() { invoke_field(.{ run: tick }) } -- Error [E0510]: wrapping the known callback does not erase state
```

#### Empty Rows on Higher-Order Signatures

```ril
fn plain() {}                              -- Ordinary named functions use default purity
halt fn answer() -> int { 42 }             -- halt also needs no empty rows
type Action = fn() -> ()                   -- First-order callable types preserve actual obligations

fn effects_closed(action: Action) @{} { action() }
fn state_closed(action: Action) &{} { action() }
fn both_closed(action: Action) @{} &{} { action() }
type PureInvoker = fn(Action) -> () @{} &{} -- The annotated arrow itself is higher-order
let invoke_anonymously = \action: Action -> @{} &{} action()

-- fn noisy_effect() @{} {}                -- Error [E0542]
-- fn noisy_state() &{} {}                 -- Error [E0542]
-- fn noisy_both() @{} &{} {}               -- Error [E0542]
-- halt fn noisy_halt() @{} {}              -- Error [E0542]
-- let noisy_lambda = \-> &{} ()            -- Error [E0542]
-- type ClosedAction = fn() -> () @{} &{}   -- Error [E0542]: first-order arrow, including in an alias
-- fn bad_parameter(action: fn() -> () @{}) { action() }
-- Error [E0542]: the callback arrow is first-order; annotate the enclosing function instead
```

A higher-order signature receives or returns callable values, directly or through transparent aliases and visible aggregate shapes. Empty rows apply to that signature's own arrow.

```ril
type Jobs = { run: Action }
fn run_job(job: Jobs) @{} &{} { job.run() } -- Callback constituents count
type JobRunner = fn(Jobs) -> () @{} &{}

type Factory = fn() -> (fn() -> ()) @{} &{} -- Rows belong to the higher-order factory
fn give_action() -> Action @{} &{} { plain }
-- type BadFactory = fn() -> fn() -> () @{} &{}
-- Error [E0542]: without parentheses, the rows belong to the returned first-order arrow

-- fn known_call_only() @{} { plain() }    -- Error [E0542]: calling a known function is not higher-order
-- fn unknown_shape<T>(value: T) &{} {}    -- Error [E0542]: unconstrained T does not establish a callable shape
-- In a .d.ril declaration fixture:
-- pub fn noisy_foreign() @{}             -- Error [E0542]: first-order external declaration
```

`@{}` closes the invocation's effect row; `&{}` closes its capability row, including captures and inherited access. Returned callables retain their own inferred rows.

```ril
-- Log and logged have the preceding contracts.
fn give_logged() -> Action @{} &{} { logged } -- Returning an existing callable performs no Log operation
-- fn hidden_returned_effect() { give_logged()() } -- Error [E0612]: the later invocation still requires Log
-- both_closed(logged)                       -- Error [E0534]: valid higher-order constraint, incompatible callback
```

#### Callable Type Bounds

```ril
type Action = fn() -> ()
type PureInvoker = fn(Action) -> () @{} &{}
eff Log { write(str) -> () }
fn plain() {}
fn logged() @Log { Log::write("event") }
fn invoke(action: Action) { action() }
fn closed(action: Action) @{} &{} { action() }
let action: Action = logged           -- OK: first-order ascription keeps the actual Log obligation
closed(plain)                        -- OK: no residual obligation
-- closed(action)                    -- Error [E0534]: omitted rows did not erase Log
let checked: PureInvoker = closed
-- checked(logged)                    -- Error [E0534]: ascription preserves the closed constraint
let selected: Action = if choose_log { plain } else { logged }
-- closed(selected)                   -- Error [E0534]: a run-time alternative retains Log
fn call_plain() { invoke(plain) }      -- Each Action value has its own dependencies
fn call_logged() @Log { invoke(logged) }
fn call_logged_alias() @Log {
    let alias: Action = logged
    invoke(alias)
}
-- fn missing_log() { let alias: Action = logged; invoke(alias) }
-- Error [E0612]: a value alias cannot hide the named caller's effect obligation
```

| Callable contract | Rule |
| :--- | :--- |
| Omitted type rows | Preserve each actual value's effects, environment mode, named origins, and sharing obligations, including across modules and private abstractions |
| Alternatives | Retain every possible obligation under [provenance](#complete-provenance-and-optional-annotations) |
| Nonempty type rows | Total upper bounds; parameter modes and handle permissions do not change |
| Higher-order empty rows | Constrain total invocation obligations, including concrete and symbolic callback dependencies |
| Definition annotations | Declare concrete obligations; still-symbolic callback dependencies continue to forward |
| Closed-constraint failure | Incompatible actual argument: E0534; fixed incompatible body: reject the definition |
| Bodyless foreign declarations | Omitted effect/state rows are closed; no termination or budget-coverage guarantee |
| `&closure` | Abstract capture details; cannot erase actual retained publication `&^mut` (E0534) |

Invoking already shared storage does not itself publish another writer. Actual environment mode still determines whether a callable needs a writable handle. Termination and budget-coverage conditions remain separate from both rows; type ascription preserves them. Returns and symbolic forwarding require no extra source annotation. Provenance diagnostics retain facts omitted from source.

```ril
-- Action, plain, and logged have the preceding contracts.
fn repeat(n: int, action: Action) {
    if n > 0 { action(); repeat(n - 1, action) }
}
fn repeat_plain() { repeat(2, plain) }
fn repeat_logged() @Log { repeat(2, logged) }
-- fn erase_recursive() { repeat(2, logged) } -- Error [E0612]
```

Recursive descent does not discharge callback obligations. `repeat_plain` is finite; `repeat_logged` retains Log and the selected handler's termination condition. A possibly non-terminating callback adds no effect label.

```ril
type StashingWorker = fn(^mut Entry) -> () &closure &^mut
type TemporaryWorker = fn(mut Entry) -> () &closure &mut
-- Their retained and temporary parameter modes are not interchangeable.
```

#### Higher-Order Calls

```ril
fn apply<T, R>(value: T, f: fn(T) -> R) -> R { f(value) }
eff Logger { log(str) -> () }
fn logged_square(n: int) -> int @Logger {
    Logger::log("calculating")
    n * n
}
fn call_square() -> int @Logger { apply(5, logged_square) }
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
fn invoke_mut(mut f: fn() -> int &closure) -> int &mut { f() }
let mut counter = create_counter(0)
let first = invoke_mut(mut counter)

fn apply_to_cell(mut cell: Cell, f: fn(mut Cell) -> () &mut) &mut {
    f(mut cell)
}
let mut cell = Cell.{ count: 0 }
apply_to_cell(mut cell, bump)
-- apply_to_cell(mut cell, \target -> ()) -- Error [E0407]: callback data mode differs
```

Forwarding preserves the contract above. Callback-handle authority and callback data-parameter modes remain distinct: an ordinary callback argument cannot invoke a mutable environment; that handle needs explicit `mut`.

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

- **Mandatory Inference**: Apply the same finite-computation rules to ordinary named functions, anonymous functions, and `halt` definitions. Ordinary functions may be `MayDiverge` without any annotation. Neither default purity nor admitted higher-order empty-row constraints supply a termination proof. `@Div` denotes only the separate budget-exhaustion effect; writing it neither authorizes nor proves divergence.
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
-- halt fn bad_io() @Fiber { Fiber::yield() }     -- Error [E0821]: outward effect

var outside_count = 0
-- halt fn bad_state() &{mut outside_count} { outside_count += 1 }
-- Error [E0821]: outward capability

fn invoke(action: fn() -> ()) { action() }
halt fn invoke_finite(action: fn() -> ()) { action() }
fn done() {}
fn forever() { loop {} }
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

fn stuck(n: int) { if n > 0 { stuck(n) } }       -- MayDiverge: no descent
fn skipped_progress(n: int) {
    var i = 0
    while i < n { if i == 0 { next }; i += 1 }
}                                               -- MayDiverge: next bypasses progress
-- halt fn bad_loop() { skipped_progress(1) }    -- Error [E0820]

type Link = { mut following: ?Link }
fn follow(node: Link) {
    match node.following { Some(child) -> follow(child), None -> () }
}                                               -- MayDiverge: Link need not be acyclic
-- halt fn bad_follow(node: Link) { follow(node) } -- Error [E0820]

fn closed_but_infinite(action: fn() -> ()) @{} &{} { action(); loop {} }
-- Closed higher-order rows still permit divergence.
fn inferred_alias() {
    let action: fn() -> () = forever
    action()
}                                               -- Ascription preserves MayDiverge
-- halt fn invalid_alias() { inferred_alias() }  -- Error [E0820]
```

Uncertified loops or recursion give `MayDiverge`, not an effect. The special [finite-evaluation contract](#finite-evaluation-with-div) can certify a bounded invocation without certifying its unbounded action. Merely handling `Div::exhausted`, counting selected user operations, or imposing a static-evaluation budget supplies no such proof for an arbitrary run-time call.

### Parameter Modes, Caller Obligations, and Defaults

```ril
type Cell = { mut count: int }
fn bump(mut cell: Cell) &mut { cell.count += 1 }
let mut cell = Cell.{ count: 0 }
bump(mut cell)
cell !> bump()
-- bump(cell)                          -- Error [E0405]: explicit mutable argument required
let view observed = cell
-- bump(mut observed)                  -- Error [E0520]: view has no write permission
```

| Parameter mode | Caller form | Authority |
| :--- | :--- | :--- |
| `p: T` | `expression` | Read-only access; preserves immutable/live origin facts |
| `mut p: T` | `mut target` | Temporary interior/environment write access; no retained writable path after the call |
| `^mut p: T` | `^mut target` | Write access plus permission to retain a writable path beyond the call |

- Mutable parameters require reference data or a mutable callable environment (`E0401`), remain pinned (`E0502`), and cannot use `var` (`E0403`).
- Annotations, forwarding, and subtyping do not infer parameter modes. Retaining an existing writer requires `^mut` and its capability (`E0510`); `!>` supplies only `mut`. A declared [fresh-value storage input](#fresh-values-in-storage-calls) may receive new construction authority without retaining an existing writer.

When a known parameter requires `mut` or `^mut`, supplying an ordinary argument without the required argument marker is `E0405`. An explicitly supplied argument mode that does not match the declared parameter mode is `E0406`. An explicitly mutable argument must designate an addressable target (`E0410`). A correct marker cannot grant missing authority (`E0520`). Callable types with incompatible data-parameter modes use `E0407`; callback-handle authority remains a separate requirement.

```ril
type Cell = { mut count: int }
fn bump(mut cell: Cell) &mut { cell.count += 1 }
fn inspect(cell: Cell) -> int { cell.count }
let mut cell = Cell.{ count: 0 }
-- inspect(mut cell)                 -- Error [E0406]: parameter is read-only
-- let reader: fn(Cell) -> () &mut = bump -- Error [E0407]: callable parameter modes differ
bump(mut cell)                        -- OK
```

A callback's parameter list and the mode of the callback handle are distinct. `f: fn(mut T) -> R` is a read-only function handle accepting a mutable *data argument*. `mut f: fn(T) -> R` grants permission to invoke a mutable *captured environment*. Both can be required by the same function. Mutable inline closures must first be bound to an appropriate writable handle before being passed with `mut`.

```ebnf
ParameterMode    ::= "mut" | "^mut"
```

Mutable modes do not apply to static key arguments.

#### Fresh Values in Storage Calls

```ril
type Cell = { mut count: int }
fn copy_cell(cell: Cell) -> Cell { clone(cell) }
fn build_cell() -> Cell {
    let mut cell = Cell.{ count: 0 }
    cell.count += 1
    cell                               -- OK: private construction authority ends on return
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

Only `value` in `Array::push`, `Array::insert`, and `Map::set` has this initialization contract. It adds no parameter mode; ordinary formals remain read-only.

```ril
-- Cell, original, and copy_cell have the preceding declarations/contracts.
fn identity(cell: Cell) -> Cell { cell }
fn frozen_cell() -> Cell { let cell = Cell.{ count: 1 }; cell }
fn append(mut target: []Cell, cell: Cell) &mut { target !> Array::push(cell) }

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

fn append_copy(mut target: []Cell, source: Cell) &mut {
    target !> Array::push(copy_cell(source)) -- OK: constructs a new result; &mut suffices
}
let push: fn(mut []Cell, Cell) -> () &mut = Array::push
push(mut cells, clone(original))       -- OK: alias preserves the operation's contract
cells[4].count += 1
```

```ril
type Cell = { mut count: int }
type Holder = { child: Immut<Cell> }
let mut shared = Cell.{ count: 1 }
let mut cells: []Cell = []
cells !> Array::push(shared)            -- OK: ordinary read-only insertion
-- cells[0].count += 1                -- Error [E0522]: existing writer needs an argument marker
cells !> Array::push(^mut shared)      -- OK: explicit retained writer
cells[1].count += 1
assert(shared.count == 2)

let mut holders: []Holder = []
holders !> Array::push(Holder.{ child: clone_immut(shared) })
-- let mut child = ^mut holders[0].child -- Error [E0520]: fresh outer data preserves nested Immut
```

```ril
type Cell = { mut count: int }
let original = Cell.{ count: 1 }
let repeated = (original, original)
let mut pairs: [](Cell, Cell) = []
pairs !> Array::push((^mut clone(repeated))) -- OK: marks internal sharing, not an argument mode
pairs[0].0.count += 1
assert(pairs[0].1.count == 2 && original.count == 1)
-- pairs !> Array::push(clone(repeated)) -- Error [E0510]: internal writable sharing is unmarked
-- pairs !> Array::push(^mut clone(repeated)) -- Error [E0410]: argument mode requires a target
```

| Check | Requirement |
| :--- | :--- |
| Eligible regions | Newly constructed ordinary writable storage, isolated from pre-existing writable regions, with no surviving outside observer, writer, or active environment |
| Established paths | Bindings select permissions; `let`, plain `var`, views, and read-only parameters end eligibility. Existing writers, including retained returns, need `^mut` arguments |
| Expressions / returns | Parentheses, blocks, and verified returns preserve actual provenance. Joins require eligibility in every possible alternative; unknown facts prove none |
| Constituents | Preserve field declarations, nested Immut and nonfresh permissions. Immutable children may be shared; fresh outer data cannot retain concealed existing writers |
| Operation identity | Imports, aliases and type ascriptions preserve contracts; matching names/signatures do not create them |
| Reception | Evaluate once in ordinary order. Success installs initial authority; failure installs no path. No additional standalone &^mut; other effects/state and access checks still apply |
| Other obligations | Internal aliases obey exclusivity; traversal/window stability and Result inspection remain checked. Foreign exchange, resources and retained callable environments gain no exemption |

#### Default Parameters and Named Arguments

```ril
fn pair(a: int = 1, b: int = 2) -> (int, int) { (a, b) }
assert(pair(b: 20, 10) == (10, 20))
assert(pair(a: 10, 20) == (10, 20))
-- pair(10, a: 20)                     -- Error [E0325]: a is already bound
```

- Defaults have no residual effects or state obligations. Mutable parameters cannot have defaults (`E0404`).
- Explicit arguments evaluate in written left-to-right order; omitted defaults follow in parameter order. A default may use earlier parameters, not itself or later parameters.
- Bind arguments in written order: a positional argument selects the first unbound parameter in declaration order; a named argument selects its named parameter. Selecting an already bound parameter is `E0325`. Binding selection does not reorder evaluation.
- Function generic defaults are prohibited (`E0317`).

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
-- fn impure_default(value: int = DefaultSource::read()) -> int @DefaultSource { value }
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
| Direct named call / unannotated value alias | Preserve that declaration's labels and defaults |
| Callable-type ascription or typed parameter/field/element/return position | Use the destination signature's labels by position; no source defaults are imported |
| Unnamed type parameter position | Positional calls only; a supplied label is `E0339` |
| Callable alternatives | Retain a label only when every alternative has it at that position; retain a default only when every alternative preserves the same declaration's default and environment |
| Subtyping / type identity | Labels are call-site metadata, not additional type-identity constraints; parameter modes, types, and obligation bounds remain checked |

Callable types admit no default-expression syntax. An ascription may rename labels by position, but never changes the called body, parameter order, permissions, effects, or provenance. A call that uses a preserved default retains that default's evaluation, termination, and dependency checks. Duplicate labels in one signature are `E0203`.

### Anonymous Functions, Trailing Closures, and Projection Accessors

```ebnf
AnonFnExpr    ::= "\" [ AnonParams ] "->" [ EffectAnnot ] [ StateAnnot ] ( Expression | Block )
AnonParams    ::= AnonParam { "," AnonParam } [ "," ]
AnonParam     ::= [ ParameterMode ] Identifier [ ":" TypeExpression ]
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
type Adder = fn(int) -> int &closure
fn make_adder(base: int) -> Adder &capture { \x -> base + x }
let add5 = make_adder(5)                -- Immutable captured value
assert(add5(10) == 15)

type Step = fn() -> int &closure
fn create_counter(start: int) -> Step &capture {
    var count = start
    \-> { count += 1; count }
}
let mut counter = create_counter(0)
assert(counter() == 1)
-- let immutable_counter = create_counter(0) -- Error [E0535]: persistent mutable environment cannot become immutable
```

```ril
type Cell = { mut count: int }
type Step = fn() -> int &closure
fn make_shared_step(^mut cell: Cell) -> Step &capture &^mut {
    \-> { cell.count += 1; cell.count }
}

let mut cell = Cell.{ count: 0 }
let mut step = make_shared_step(^mut cell)
assert(step() == 1)
cell.count += 1
assert(step() == 3)                   -- Both authorities still reach the same cell
-- let frozen = make_shared_step(^mut cell) -- Error [E0535]: retained mutable environment
```

- **Abstraction**: `&closure` follows [callable type bounds](#callable-type-bounds); direct named capture access still requires source groups.
- **Definitions (`E0534`)**: Named definitions cannot replace direct source groups with standalone `&closure`. Parameter/return callable types may use it; anonymous captures remain inferred and explicit annotations remain checked.
- **Creation**: New environments surviving the enclosing callable's return require `&capture`, including those nested in returned aggregates. Forwarding existing environments or using call-local ones does not.
- Anonymous functions capture free value bindings, including module bindings. Module-level named functions use declared external access; escaping block-local functions retain their required lexical environments.
- **Binding Choice**: A immutable environment can be bound with `let`. An environment that only observes live pinned roots can be bound with `let view`. A persistent mutable environment requires a writable handle. These are environment facts, not consequences of the visible `&closure` spelling.
- **Sharing**: A private cell exposed only through one new closure requires `&capture`. Exposing another authority to that cell also requires `&^mut`.



## State and Capability Tracking

### Local Mutation Purity and Local Capability Discharge

A function that mutates locally allocated variables that do not escape retains a purely functional external interface. Capability obligations for frame-confined variables are **discharged locally**:

```ril
type Buffer = { mut items: []int }
fn append_val(mut b: Buffer, v: int) &mut { b.items !> Array::push(v) }

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
fn link(mut hub: NodeHub, node: int) &mut { hub.nodes !> Array::push(node) }

fn test_internal_hub() -> int {
    let mut local_hub = NodeHub.{ nodes: [] }
    let local_node = 42
    link(mut local_hub, local_node)    -- &mut discharged locally: the scalar is copied
    len(local_hub.nodes)               -- Pure: signature carries no external mutation obligation
}
```

### Parameter Mutation

A function mutating any borrowed parameter MUST declare at least `&mut`; anonymous `&^mut` includes this parameter-mutation obligation. Named external mutation still requires the corresponding named capability and cannot be concealed by an anonymous annotation.

```ril
fn clear_items(mut list: []int) &mut {
    list !> Array::truncate(0)         -- OK: declared &mut
}

-- Missing capability annotation is statically rejected:
-- fn bad_clear(mut list: []int) {     -- Error [E0510]: mutating operation requires caller signature to declare '&mut'
--     list !> Array::truncate(0)
-- }
```

### Retained Mutable Sharing

`^mut` has unary prefix precedence; it evaluates its operand once and preserves identity and permissions under the contracts below.

```ebnf
SharingExpr     ::= "^mut" Expression
```

```ril
type Entry = { mut id: int }
type Hub = { mut entries: []Entry }
let mut global_hub = Hub.{ entries: [] }

fn register_entry(mut hub: Hub, ^mut entry: Entry) &^mut {
    hub.entries !> Array::push(^mut entry)
}
fn publish_entry(^mut entry: Entry) &^mut &{mut global_hub} {
    global_hub.entries !> Array::push(^mut entry)
}
-- The retained origin is entry. Merely inserting it does not create a new authority to global_hub.
```

- **Retention**: `&^mut` publishes another independent writable authority, including sharing newly created local state among multiple surviving authorities. A `^mut source` item names a retained global or captured source in its corresponding group and includes that source's write access; a destination merely receiving data uses a `mut destination` item. Standalone `&capture` and `&^mut` remain separate annotations, never group entries.
- **Arguments**: Retaining a borrowed writer requires `^mut` on both parameter and argument. Ordinary `mut` loans end at return. Indirection preserves retained permissions and source identities.

```ril
type Cell = { mut count: int }
type Holder = { mut child: Cell }
let mut source = Cell.{ count: 0 }
let mut alias = ^mut source
let mut holder = Holder.{ child: ^mut source }
alias.count += 1
holder.child.count += 1
source.count += 1
assert(source.count == 3)
-- let mut hidden = source             -- Error [E0510]: new local writable alias needs ^mut
-- let mut hidden_block = { source }   -- Error [E0510]: a plain block cannot hide the local alias creation
-- let mut hidden_box = Holder.{ child: source } -- Error [E0510]: stored writable alias needs ^mut

let immutable = Cell.{ count: 0 }
let view observed = source
-- let mut bad = ^mut immutable        -- Error [E0520]: marker cannot grant write permission
-- let mut bad_view = ^mut observed    -- Error [E0520]: marker cannot upgrade a live view

let repeated = (immutable, immutable)
let mut copied = ^mut clone(repeated)
copied.0.count += 1
assert(copied.1.count == 1)             -- Internal aliases survive the isolated copy
-- let mut hidden_copy = clone(repeated) -- Error [E0510]: writable internal sharing must be marked
```

- **Local Sharing Marker (`E0510`)**: A new local writable path to existing ordinary storage or an existing callable environment requires `^mut expression` at its binding, assignment, aggregate insertion, or destructuring site. The marker may cover one constituent or a whole construction/destructuring source; every constituent retains its own permissions. A writable reception of a deep copy with possible internal writable aliases also requires this marker. Proven immutable sharing needs none.
- **Checked Meaning**: The marker evaluates its operand once and preserves identity. It neither clones nor freezes, transfers ownership, grants missing permissions, revives invalid resources, or extends a temporary loan. Missing markers and invalid authority are distinct errors; adding a marker cannot repair `E0520`–`E0528` violations. Possible internal aliases need not be resolved to one exact graph, but remain subject to all overlap checks.
- **No Duplicate Boundary Spelling**: Receiving an authority already produced under a checked callable retention contract does not require another local marker. Callable return/tail expressions, inferred lexical captures, and handler environments keep their existing rules; no new return or capture syntax is required. A plain block is not a callable retention boundary. Aliasing an already created mutable closure locally still requires the marker. A `clone` source/copy isolation contract does not itself mark the copy's possible internal writable aliases, including at a [fresh-value storage input](#fresh-values-in-storage-calls).
- **Confinement**: Local `^mut` does not by itself add external `&^mut` to the enclosing function. Conversely, local discharge does not remove required markers at local data-sharing sites. Captured and returned sharing still contributes its actual authority roots whether or not its facts are written explicitly.

```ril
fn retain(^mut cell: Cell) -> Cell &^mut { cell }
let mut original = Cell.{ count: 0 }
let mut returned = retain(^mut original) -- Retention already marked at the call boundary
returned.count += 1
original.count += 1
-- let mut hidden = retain(original)  -- Error [E0405]: ordinary argument lacks the retention marker
-- let mut hidden = retain((^mut original)) -- Error [E0405]: sharing expression is not an argument-mode marker
-- let mut hidden = retain(^mut clone(original)) -- Error [E0410]: mutable argument must be an assignable target
```

| Surviving references | Sharing obligation |
| :--- | :--- |
| Repeated fields/cycles inside one fresh passive result graph | No additional external authority; still check internal aliasing |
| Borrowed/external origin retained elsewhere | `&^mut` or its named form |
| One cell exposed through a closure and a direct graph reference | `&^mut`, even inside one returned tuple |
| One cell exposed through multiple mutable closures | `&^mut` |

Each surviving borrowed/external root, escaped mutable environment, and separately exposed passive graph is an authority root; repeated graph traversal does not add roots.
- **Local Discharge**: Retention whose origins and authority roots all remain confined to the current frame is discharged locally. Mutation of already shared storage does not itself create another retention obligation. Existing sharing remains a provenance fact; it is not a repeated publication on every invocation.
- **Bounds**: Concrete definitions cannot overstate capabilities (`E0529`); callable types may declare upper bounds. Bounds do not change parameter modes. Actual retention satisfies `E0527` for `^mut`.

```ril
type Step = fn() -> int &closure
fn make_private_ticker() -> Step &capture {
    var count = 0
    \-> { count += 1; count }
}
fn make_shared_ticker(^mut cell: Cell) -> Step &capture &^mut {
    \-> { cell.count += 1; cell.count }
}
fn make_dual_ticker() -> (Step, Cell) &capture &^mut {
    let mut cell = Cell.{ count: 0 }
    let mut step = \-> { cell.count += 1; cell.count }
    (^mut step, ^mut cell)
}
```

```ril
var active_connections = 0
type Ticker = fn() -> int &closure
fn share_connections() -> Ticker &capture &{^mut active_connections} {
    \-> { active_connections += 1; active_connections }
}
```

A writable container never upgrades an immutable/view element (`E0522`). Retaining an inserted existing writer requires `^mut` and the corresponding retention capability. Receiving an unpublished fresh value under its storage contract supplies initial construction authority, subject to the same internal-alias checks.

### External State Tracking

```ril
let APP_CONFIG_NAME = "Production"
var transaction_count = 0

-- Read-only external access:
fn get_config_name() -> str &{APP_CONFIG_NAME} {
    APP_CONFIG_NAME                    -- OK: declared &{APP_CONFIG_NAME}
}

fn read_transaction_count() -> int &{transaction_count} {
    transaction_count                 -- Live source; scalar result is an independent value
}

-- Mutable external access:
fn record_transaction() -> () &{mut transaction_count} {
    transaction_count += 1             -- OK: declared &{mut transaction_count}
}

-- Static errors on missing annotations:
-- fn bad_read() -> str { APP_CONFIG_NAME }          -- Error [E0510]: accessing external state requires caller signature to declare capability '&{APP_CONFIG_NAME}'
-- fn bad_write() { transaction_count += 1 }        -- Error [E0510]: mutating external state requires caller signature to declare capability '&{mut transaction_count}'

-- Prohibition of Anonymous Concealment:
-- fn conceal_write() &mut { transaction_count += 1 } -- Error [E0510]: cannot use anonymous '&mut' to conceal external state 'transaction_count'
```

```ril
-- Use record_transaction, read_transaction_count, and transaction_count initialized above.
fn direct_call() &{mut transaction_count} { record_transaction() }
fn alias_call() &{mut transaction_count} {
    let action = record_transaction  -- Immutable callable descriptor; named state still applies
    action()
}
fn invoke_action(action: fn() -> ()) { action() }
fn parameter_call() &{mut transaction_count} { invoke_action(record_transaction) }

direct_call()
alias_call()
parameter_call()
assert(read_transaction_count() == 3)

-- fn hidden_call() { record_transaction() } -- Error [E0510]
-- fn hidden_alias() { let action = record_transaction; action() } -- Error [E0510]
-- fn hidden_parameter() { invoke_action(record_transaction) } -- Error [E0510]
-- fn falsely_closed(action: fn() -> ()) &{} { alias_call(); action() }
-- Error [E0534]: the closed signature cannot admit the concrete callee's state
```

These forms use the same [callable contracts](#callable-contracts); spelling the call differently does not change its concrete origins.

Accessing module-level or captured bindings requires the corresponding named source group. A named definition must also declare concrete named obligations inherited from calls, either with a matching source group or an admissible function state contract reference. Only genuine callable-parameter dependencies retain implicit symbolic forwarding.

This includes reading a module-level `meta let NAME` in a run-time value expression: the named definition declares `&{NAME}`. Compile-time evaluation and immutability do not erase that named source. Reads performed in the static/type domain are exempt from this run-time state obligation, including type expressions and static arguments.

Within either kind of source group, a bare item permits read-only access, whether its actual data is immutable or live. It does not promise deep immutability or create a `let view` binding. `mut name` adds writes; `^mut name` additionally permits retained writable sharing. Each mode applies only to its own item.

Direct access includes storage access in the named definition's lexical anonymous functions and handler arms when those operations contribute to its current invocation, and mutable argument permissions it supplies. Direct access requires its own declarations after local discharge; a contract reference cannot replace them. Referencing a named function declaration is not itself a read of storage; accessing a stored external callback is. Future operations of a returned callable remain latent, while its creation, capture, and retention obligations are checked separately.

### State Groups and Captured Layers

```ebnf
StateAnnot       ::= StateCapability { StateCapability }
StateCapability  ::= "&mut"
                   | "&^mut"
                   | "&closure"
                   | "&capture"
                   | "&{" "}"
                   | GlobalStateGroup
                   | CapturedStateGroup
                   | StateContractRef
GlobalStateGroup ::= "&{" StateItemList "}"
CapturedStateGroup ::= "&{" "closure" [ CaptureOwner ] "," StateItemList "}"
CaptureOwner     ::= SnakeCase
StateItemList    ::= StateItem { "," StateItem } [ "," ]
StateItem        ::= [ StateMode ] QualifiedName
StateMode        ::= "mut" | "^mut"
StateContractRef ::= "&" QualifiedName
```

```ril
var global_count = 0
let GLOBAL_SCALE = 2
fn tick() -> int &{mut global_count, GLOBAL_SCALE} {
    global_count += GLOBAL_SCALE
    global_count
}

fn outer() -> int {
    var count = 0
    inner()
where
    fn inner() -> int &{closure, mut count} {
        count += 1
        count
    }
}
```

- **Global Groups (`E0538`)**: A nonempty group without a `closure` header contains only module storage bindings. Qualified names and declaration imports follow ordinary name resolution; importing a binding does not create new local storage. A named function declaration itself is not a storage item.
- **Captured Groups (`E0538`)**: A group beginning with `closure` contains captured bindings from one enclosing callable layer. The current layer is the annotated callable's directly enclosing function or lambda. Its name may be omitted. A farther named layer requires its function name; a farther anonymous layer still uses the bare `closure` header. An explicit owner must match the actual source layer.
- **Resolution Before Classification**: Resolve each item to its ordinary lexical binding first, then check its owner and the group's kind. A header cannot bypass shadowing, select another same-spelled variable, or rebind a local source to a global. The owner name verifies the already resolved layer; its spelling is not a dynamic environment identity.
- **Layer and Identity**: Named functions and lambdas introduce callable layers; ordinary blocks, loop bodies, and handler arms do not introduce additional function layers. Their distinct bindings, activations, lifetimes, and handler identities nevertheless remain distinct. A binding may point into another layer, a caller, or global storage; those possible object origins do not change the binding's declaration layer.
- **Grouping**: Items from one resolved layer may share a group. Items from different layers must not share one, even when both groups have the identical bare `closure` spelling. `mut` and `^mut` do not extend across commas. Grouping preserves every binding, access path, dynamic instance, alias relation, and transitive obligation.

```ril
fn outer_layer() -> int {
    var count = 0
    middle()
where
    fn middle() -> int &{closure, mut count} {
        inner()
    where
        fn inner() -> int &{closure outer_layer, mut count} {
            count += 1
            count
        }
        -- Omitting outer_layer here is E0538: the source is a farther named layer.
    }
}

let run = \-> {
    var x = 0
    let mut nested = \-> {
        var y = 0
        leaf()
    where
        fn leaf() -> int &{closure, mut x} &{closure, mut y} {
            x += 1
            y += 1
            x + y
        }
        -- &{closure, mut x, mut y} is E0538: the two sources belong to different anonymous layers.
    }
    nested()
}
assert(run() == 2)
```

Anonymous functions may omit source groups and infer all their actual obligations. If they write a group, its names, modes, and layer must still be correct. Source groups in callable types bind names at the type's declaration site and form state upper bounds; an ascription cannot rebind them to similarly named captures in the assigned value. Unknown environments retain the existing `&closure` abstraction instead of inventing source names.

```ril
var count = 0
fn bump_global() &{mut count} { count += 1 }
fn shadowed() -> int {
    var count = 10
    inner()
where
    fn inner() -> int &{closure, mut count} { count += 1; count }
    -- Replacing the group with &{mut count} is E0538, not a reference to the global count.
}

-- capture and closure are ordinary identifiers, not reserved keywords:
let capture = 10
var closure = 0
var x = 0
fn bump_names() &{mut closure, mut x} { closure += 1; x += 1 }
fn read_closure() -> int &{closure} { closure }
fn read_both() -> int &{x, closure} { x + closure }
-- &{closure, x} is always a capture group; it cannot denote these two global reads.
-- &{closure,} is Error [E0538]: a captured group requires a real item.
```

Standalone `&capture`, `&mut`, `&^mut`, and the callable-type abstraction `&closure` are not group entries. `&{}` follows the [higher-order empty-row rules](#empty-rows-on-higher-order-signatures). No group declares that storage is unique, consumes authority, or merges a retained handler definition; those obligations retain their existing checks.

The contextual `closure` group header takes precedence over the global-list production. A captured group requires at least one item: `&{closure,}` is `E0538`, while `&{closure}` reads a global binding named `closure`. Built-in `&mut`, `&^mut`, `&capture`, and `&closure` retain their meanings ahead of the reference production. A state contract reference is permitted only on an ordinary named function definition, subject to [its reference rules](#named-function-state-contract-references); the common grammar does not authorize it in other annotation positions.

### Named Function State Contract References

```ril
-- counter.ril
var private_count = 0
pub fn advance() &{mut private_count} { private_count += 1 }
fn private_advance() &{mut private_count} { private_count += 1 }
pub type Step = fn() -> int &closure
pub fn make_step() -> Step &capture &{mut private_count} {
    private_count += 1
    var local_count = 0
    \-> { local_count += 1; local_count }
}
pub type Cell = { mut count: int }
pub fn retain(^mut cell: Cell) -> Cell &^mut &{mut private_count} {
    private_count += 1
    cell
}

-- client.ril
use counter
fn wrapper() &Counter::advance { Counter::advance() }
fn through_alias() &Counter::advance {
    let action = Counter::advance
    action()
}
fn invoke(action: fn() -> ()) { action() }
fn through_callback() &Counter::advance { invoke(Counter::advance) }
fn make_wrapped() -> Counter::Step &capture &Counter::make_step {
    Counter::make_step()
}
fn retain_wrapped(^mut cell: Counter::Cell) -> Counter::Cell &^mut &Counter::retain {
    Counter::retain(^mut cell)
}
-- fn missing_state() { Counter::advance() } -- Error [E0510]
-- fn missing_creation() -> Counter::Step &Counter::make_step { Counter::make_step() }
-- Error [E0510]: the reference does not include the surviving environment's &capture obligation
-- fn missing_retention(^mut cell: Counter::Cell) -> Counter::Cell &Counter::retain { Counter::retain(^mut cell) }
-- Error [E0510]: the reference does not include this parameter's independent &^mut obligation
-- fn read_private() -> int &Counter::advance { Counter::private_count }
-- Error [E0201]: a contract reference does not export the private binding
```

- **Provider (`E0539`)**: `&callee` / `&Module::callee` selects a visible ordinary named Ril definition's verified named-state contract. Resolve names first: lexical absence `E0204`, absent module member `E0209`, private member `E0201`; then reject a wrong provider kind with `E0539`. Value aliases and callable parameters are not providers.
- **Position (`E0539`)**: Allowed only on ordinary named function definitions. Reject it on callable types, anonymous functions, effect operations, and bodyless foreign declarations.
- **Concrete Named Projection**: A reference denotes the provider's concrete global/captured source items and their verified access modes for its current invocation, including concrete named dependencies obtained through other calls. The bindings and lexical owners remain anchored to the provider's scope. It does not include effects, anonymous parameter permissions, standalone `&capture`/`&^mut`, symbolic callback dependencies, or a returned callable's future invocation obligations.
- **Coverage**: After local discharge, match inherited concrete named obligations by origin and permission. The caller need not invoke the provider by name. Direct storage/handler access and required parameter `&mut`/`&^mut` remain separate. Unrelated references leave `E0510`; unnecessary references remain `E0529`.
- **No Erasure**: Calling through an alias or higher-order helper preserves the concrete dependencies. A provider reference cannot turn them into unknown callback dependencies, discharge a conflicting loan, or prove a recursive dependency empty. An admitted higher-order `&{}` constrains the total state, including referenced state.
- **Declaration Identity**: A declaration import alias or re-export preserves its provider identity. `let action = callee` and a public callable-valued binding do not create provider declarations; references to such bindings are `E0539`. The built-in capability spellings keep their established meanings; a same-spelled function requires a qualified reference. Public callable values without a suitable visible provider do not acquire an implicit private-state permission.

```ril
-- Same-module fixture:
var count = 0
fn advance() &{mut count} { count += 1 }
fn other_advance() &{mut count} { count += 1 }
fn equivalent_contract() &advance { other_advance() } -- Same concrete inherited source and mode
fn no_state() {}
-- fn excessive() &no_state { no_state() } -- Error [E0529]: no concrete named state to declare
-- fn hidden_direct() &advance { count += 1; advance() }
-- Error [E0510]: the direct write still requires &{mut count}

eff Tick { tick() -> () }
-- fn hidden_handler() &advance {
--     with Tick::tick() -> { count += 1; resume () }
--     advance()
--     Tick::tick()
-- }                                  -- Error [E0510]: the direct handler write needs its own source group

let action = advance
-- fn invalid_provider() &action {}  -- Error [E0539]: action is a value binding
-- type InvalidContract = fn() -> () &advance -- Error [E0539]: reference form is not a callable-type annotation
-- fn closed(step: fn() -> ()) &{} { advance(); step() }
-- Error [E0534]: a closed higher-order definition cannot inherit this state
```

```ril
-- Counter is the ordinary module defined above.
use counter
-- fn private_reference() &Counter::private_advance {} -- Error [E0201]: private provider
-- fn unknown_reference() &Counter::missing {}         -- Error [E0209]: no such module member
-- let invalid = \-> &Counter::advance ()               -- Error [E0539]: anonymous annotation
-- eff Invalid { tick() &Counter::advance }              -- Error [E0539]: effect-operation annotation
-- In a declaration-unit fixture with the same visible Counter namespace:
-- pub fn invalid_foreign() &Counter::advance             -- Error [E0539]: bodyless declaration
```

```ril
type Cell = { mut count: int }
fn outer(mut cell: Cell) &mut {
    inner()
where
    fn inner() &{closure, mut cell} { cell.count += 1 }
}
-- inner's named capture is derived from outer's parameter loan.

let mut global_cell = Cell.{ count: 0 }
fn touch_global() &{mut global_cell} { global_cell.count += 1 }
fn parameter_and_ambient(mut cell: Cell) &mut &touch_global {
    cell.count += 1
    touch_global()
}
let mut local = Cell.{ count: 0 }
parameter_and_ambient(mut local)     -- OK: the two actual write origins are disjoint
-- parameter_and_ambient(mut global_cell) -- Error [E0523]: the independent ambient path overlaps the parameter loan
```

```ril
-- counter.ril: a separate effect-bearing operation on its private_count.
pub eff Log { write(str) -> () }
pub fn logged_advance() @Log &{mut private_count} {
    Log::write("advance")
    private_count += 1
}

-- client.ril
use counter
use counter::{Log, advance as bump}
fn imported_alias() &bump { bump() }  -- Declaration alias, not a value alias
fn logged_wrapper() @Log &Counter::logged_advance { Counter::logged_advance() }
-- fn missing_effect() &Counter::logged_advance { Counter::logged_advance() }
-- Error [E0612]: a state reference does not import Log
```

### Closure Capabilities and Handle Permissions

```ril
let mut counter = create_counter(0)
assert(counter() == 1)
-- let immutable = counter                -- Error [E0535]: live mutable environment cannot become immutable
let view observer = counter
-- observer()                          -- Error [E0520]: observing a mutable callable does not permit invocation
```

A callable that writes its persistent captured environment requires `let mut`, `var mut`, or a `mut`/`^mut` parameter at invocation. Plain `var` does not provide environment write permission. An observer callable that only reads permitted live origins can be invoked through `let view` or a read-only parameter. An immutable callable can be invoked through `let`.

An immutable callable may still have effects or named external-state obligations. Invocation checks those obligations and all transitive access sets, including handlers; `let` does not erase them. Declared external access alone does not create a named function's mutable environment.

### Law of Exclusivity and Cross-Argument Disjointness

A mutable loan's writes must not overlap another participant's reads/writes. Read/read overlap is allowed. Check actual possible storage origins, not field names or indices; unknown overlap is `E0523` or `E0524`.

Use through the borrowed formal belongs to that loan. Independent arguments, captures, and ambient origins are other participants. Nested forwarding suspends the caller's access until return; inactive aliases do not prohibit sequential sharing.

A call-local closure that captures a borrowed formal retains that formal's loan provenance and cannot extend its lifetime. Access through this derived path belongs to the loan. An independently obtained ambient or captured path does not become part of the loan merely because its object identity matches the formal's.

```ril
type Cell = { mut count: int }
fn swap(mut a: Cell, mut b: Cell) &mut {
    let saved = a.count
    a.count = b.count
    b.count = saved
}
let mut cells = [Cell.{ count: 1 }, Cell.{ count: 2 }]
swap(mut cells[0], mut cells[1])        -- OK: distinct allocations, not merely distinct indices
-- swap(mut cells[0], mut cells[0])    -- Error [E0523]: same writable origin

let immutable_cell = Cell.{ count: 0 }
let repeated = (immutable_cell, immutable_cell)
let mut copied = ^mut clone(repeated)
copied.0.count += 1
assert(copied.1.count == 1)             -- clone preserves internal aliases
-- swap(mut copied.0, mut copied.1)    -- Error [E0523]: distinct projections reach the same copied object
```

An explicit `^mut` publication permits sequential sharing, not overlapping exclusive loans or races. Mutations through any alias invalidate affected live refinements. Immutable references are exempt from such invalidation because no writable origin remains.

### Monotonic Permission Degradation and Anti-Laundering Matrix

Apply [provenance propagation](#complete-provenance-and-optional-annotations) at every access path. The following cases distinguish permission failures from immutable-publication failures; clone and derive retain their explicit fresh-data contracts.

```ril
type Cell = { mut count: int }
let mut box = .{ child: Cell.{ count: 0 } }
var cursor = box
-- let mut stolen = ^mut cursor.child -- Error [E0520]: projection cannot escape the read-only path
box.child.count += 1
assert(cursor.child.count == 1)        -- The independent writer remains valid
cursor = .{ child: Cell.{ count: 9 } }

fn project(box: { child: Cell }) -> Cell { box.child }
-- let mut stolen = project(box)      -- Error [E0528]: ordinary parameter and return preserve read-only access
```

Plain `var`, views, and read-only parameters restrict every data/environment path reached through them; they neither freeze the object nor revoke an independent writer. A callable's named external-state obligations are checked separately from access through its data handle.

[Fresh storage reception](#fresh-values-in-storage-calls) precedes read-only binding or parameter passage; it cannot recover authority after either boundary.

```ril
type Cell = { mut count: int }
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
-- clone(active)                     -- Error [E0530]: mutable captured environment cannot be cloned
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

eff BufferIo { read_into(mut buf: []u8) -> int &mut }

eff State<S> {
    get() -> S,
    put(val: S) -> (),
}

eff Context<T> { ask() -> T }

eff AppEffects { Console, State<int> } -- Combined effect set
```

```ril
-- Context has the preceding declaration.
fn read_context() -> int @Context<int> { Context::ask() }
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
EffectOpDecl     ::= SnakeCase "(" [ ParameterTypeList ] ")" [ "->" TypeExpression ] [ StateAnnot ]
EffectAnnot      ::= "@" ( EffectRow | "{" "}" )
EffectRow        ::= EffectIdentifier { "+" EffectIdentifier }
EffectIdentifier ::= QualifiedName [ GenericArgs ]
EffectOperationRef ::= EffectIdentifier "::" SnakeCase
```

Effect identifiers resolve to PascalCase effect declarations. Operation signatures use the ordinary parameter-mode and capability rules; a declared operation may request read-only, temporary writable, or retained writable access.

```ril
-- Console and BufferIo have the declarations above.
-- Effectful computation: invokes print twice and read_line once
fn hello() -> () @Console {
    Console::print("Enter name:")      -- First intercepted operation
    let name = Console::read_line()     -- Second intercepted operation
    Console::print("Hello, {name}")  -- Third intercepted operation (deep handler re-entered)
}

-- Effectful computation invoking capability-bearing BufferIo:
fn fill_header(mut target: []u8) -> int @BufferIo &mut {
    BufferIo::read_into(mut target)    -- OK: &mut capability flows through caller to operation
}
```

### Effect Handlers

```ril
eff Console { print(str) -> (), read_line() -> str }
fn hello() @Console {
    Console::print("Name?")
    let name = Console::read_line()
    Console::print("Hello, {name}")
}
fn run_console() {
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

A leading `mut`/`^mut` on a handler parameter is its operation-parameter mode, before pattern interpretation. The remaining pattern must be irrefutable and contains no binding modifiers: `var` is `E0403`, and nested `mut`/`^mut` is `E0406`. The mode must exactly match the operation's declared parameter mode (`E0406`); omission does not infer writable or retained authority. Ordinary names in handler-target position remain grammatically admitted so non-operation targets receive `E0621`.

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

type Cell = { mut count: int }
eff Edit { apply(mut Cell) -> () &mut }
fn edit_once(mut cell: Cell) -> int &mut {
    with Edit::apply(mut target) -> {
        target.count += 1
        let saved = target.count
        let answer = resume ()
        -- target.count += 1            -- Error [E0540]: this operation loan has ended
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
type Cell = { mut count: int }
eff Store { keep(^mut cell: Cell) -> () &^mut }
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
| Read-only | Plain pattern | Read-only; scalars copy, references preserve immutable/live facts |
| `mut` | `mut pattern` | Temporary operation loan, ending when resumption starts |
| `^mut` | `^mut pattern` | Retained writable authority; actual retention remains tracked |

Destructured reference bindings receive no more than the mode and every source path permit; scalar constituents remain independent read-only copies. A `^mut` handler parameter still must exercise its authority under `E0527`. Resumption does not revoke lawful retained authority, but neither the handler mode nor the operation declaration extends a scoped lifetime or suspends exclusivity checks on independent origins.

| Operation's ordinary `mut` loan | Arm's permission |
| :--- | :--- |
| Before `resume`, including evaluation of its value | Access through the matching parameter |
| Continuation starts | Return the loan; end all arm access through the parameter and derived aliases (`E0540`) |
| `resume` returns | No restoration; copied scalars, independent data, and lawful retained `^mut` authority remain usable |

Outer function/callback loans stay active. Independent captures and ambient aliases remain separate exclusivity participants. Neither resumption nor `^mut` extends a borrowed or scoped lifetime.

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

Escape alone is valid. Retention preserves dispatch, required outer definitions, and access/sharing/escape facts for provenance diagnostics, without extra capture syntax. Effect discharge never removes state, capture, live-view, or mutable-environment obligations.

```ril
type Button = { label: str, on_click: fn() -> () &closure }
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
type Reader = fn() -> int &closure
fn make_reader() -> Reader &capture {
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
type Reader = fn() -> int &closure
type Deferred = fn() -> int @Read
fn ask_read() -> int @Read { Read::get() }
fn read_without_state(action: Deferred) -> int @Read &{} { action() }
fn make_indirect_reader() -> Reader &capture {
    with Read::get() -> resume 7
    \-> ask_read()                    -- Captures the handler for the helper's residual Read operation
}
fn make_deferred() -> Deferred { \-> Read::get() }
fn make_chained_reader() -> Reader &capture {
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
    fn helper() -> int @Read { Read::get() }
}
fn nested_block_helper() -> Reader &capture {
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
-- Deferred omits its state row, so it preserves each actual value's environment.
-- The zero-state requirement belongs to read_without_state's higher-order signature.
```

```ril
eff Tick { tick() -> () }
fn handled_write(mut cell: Cell) &mut {
    with Tick::tick() -> { cell.count += 1; resume () }
    Tick::tick()
}
-- fn hidden_write(mut cell: Cell) {
--     with Tick::tick() -> { cell.count += 1; resume () }
--     Tick::tick()
-- }                                   -- Error [E0510]: handling Tick does not discharge the parameter write
```

The earlier `make_button` body has no captured variables or retained outer handler. Adding `&capture` to it is excessive (`E0529`). A capturing version is:

```ril
fn make_label_button(label: str) -> Button &capture {
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
fn supply_config(value: int, action: fn() -> int) -> int {
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

`resume` without an enclosing effect-operation arm is `E0623`. Capturing an enclosing arm's resumption across a prohibited callable boundary remains `E0611`; a second use remains `E0610`. Access through an operation's ended temporary loan, including a derived alias after resumption begins, is `E0540`. This does not revoke an independent lawful retained authority.

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
fn bad_escaping_resume() -> (fn() -> int) &capture {
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

fn guarded_workflow(mut audit: AuditLog) -> str @Auth &mut {
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

fn test_early_abort() {
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
fn handled_yield() {
    with Fiber::yield() -> resume ()
    Fiber::yield()                     -- No residual Fiber request
}
fn read_name(path: str) -> Result<str, str> @Fiber {
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
fn read_socket_chunk(fd: int) -> []u8 @Fiber {
    Socket::read_chunk(fd)             -- Fixture contract: waits for this socket and returns immutable data, @Fiber
}

-- Functions declared @Fiber cannot invoke structured concurrency primitives:
fn bad_leaf_fork(fd: int) -> []u8 @Fiber {
    -- scope(\mut s -> {               -- Error [E0612]: function declares '@Fiber' but invokes unhandled '@Concurrent' primitive 'scope'
    --     s.fork(\-> Socket::read_chunk(fd))
    -- })
    read_socket_chunk(fd)
}

-- Compound Asynchronous Workflow (@Async = {Fiber, Concurrent}):
fn fetch_pipeline(url: str) -> Result<str, TaskFault> @Async {
    let raw = read_socket_chunk(80)    -- Inherits @Fiber
    scope(\mut s -> {                  -- Requires @Concurrent (present in @Async)
        let worker = s.fork(\-> parse(raw))
        let parsed = worker.join()?
        Ok(parsed)
    })
}

-- Cooperative Fiber Yielding (@Fiber):
fn cooperative_worker(count: int) -> () @Fiber {
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

fn range_stream(start: int, max: int) @Yield<int> {
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
        if len(collected) >= 3 {
            -- Delimited early abort: returning without 'resume' cleanly terminates generator
            return collected
        }
        resume ()                      -- Resumes generator execution within lexical handler
    }
    range_stream(0, 100)
    collected
}

-- (b) Independent Composition: Suspendable Async Generator:
fn stream_remote_chunks(fd: int) -> () @Yield<[]u8> + Fiber {
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
-- Div::budget<T>(limit: int, action: fn() -> T) -> T @Div

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
fn finite_attempt() -> int @Div { Div::budget(10_000, spin) }
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
fn isolated_value() -> Result<int, TaskFault> @Concurrent {
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
halt fn square_all(numbers: Immut<[]f64>) -> []f64 {
    numbers |> Parallel::map(\x -> x * x)
}
-- @Parallel is not an effect annotation (E0620).
```

Parallel invocation requires no residual effects and independently established finite computation; empty effect rows alone are insufficient (`E0820`). Outside mutable/live/resource dependencies, including those hidden in handlers or cleanup, are rejected (`E0605`), except the explicitly lent disjoint regions admitted by a concrete library operation. Overlapping or unproved-disjoint write/read or write/write regions are `E0619`. Checks are transitive; a distinct name, index, or copied graph path is not evidence of independence. Handling Div exhaustion alone does not establish finiteness. No live authority may escape the invocation.

An ordinary read-only parameter such as `numbers: []f64` can denote live data; it does not establish `Immut<[]f64>`. Pure parallel collection inputs require the immutable view declared above or an explicitly detached immutable copy.

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
TypeFunctionExpr ::= "\" TypeFnParam { "," TypeFnParam } "->" Expression
TypeFnParam      ::= StaticKeyParamDecl
                  | PascalCase [ ":" TypeSort ] [ "=" TypeExpression ]
                  | SnakeCase ":" TypeExpression [ "=" Expression ]
```

- **Declarative Contexts**: Top-level type declarations and type annotations use direct type syntax without `type<...>`:

```ril
type User = { id: int }
let a: int = 10
let b: typeof a = 20                   -- OK: direct 'typeof' in type annotation
```

`typeof e` checks names, types, and permissions without evaluating e: no effects, writes, or environment creation.

- **Expression Contexts**: A type used as a static type value must be enclosed in `type<...>`. A bare nominal constructor or nullary tag in a value expression denotes its callable/value meaning, not its type. The following let bindings are in a symbolic type-computation fixture; type tokens do not become ordinary run-time data:

```ril
let t_int = type<int>                  -- OK: all types enclosed in type<...>
let t_inferred = type<typeof (1 + 2)>  -- OK: 'typeof' enclosed in type<...> in expression position
-- let bad_t = int                     -- Error [E0319]: bare type 'int' used in expression context; wrap in 'type<int>'
-- let bad_inferred = typeof (1 + 2)   -- Error [E0319]: bare 'typeof' operator used in expression context; wrap in 'type<typeof (1 + 2)>'
```

- **Strict Phase Distinction & Runtime Quotation Prohibition (`E0816`)**: `type<...>` is strictly a compile-time static quotation permitted exclusively in static evaluation scopes (`meta let`, `meta fn`, pure `type` functions, and const generic arguments). In non-meta runtime expressions, using `type<...>` as a value operand is statically rejected under `E0816: RuntimeTypeQuotationProhibitedError`. Runtime invocations supply type arguments via angle brackets (`f<T>(x)`) or contextual bidirectional inference (`let x: T = f(x)`). Types are completely erased during AOT compilation; runtime execution passes no type tokens, witness tables, or phantom values.

```ril
fn json_decode<T>(raw: str) -> Result<T, str> { ... }

fn runtime_client(raw: str) {
    -- let bad = json_decode(type<User>, raw)   -- Error [E0816]: 'type<...>' quotation prohibited in runtime context; use 'json_decode<User>(raw)' or contextual inference
    let explicit = json_decode<User>(raw)       -- OK: explicit generic type argument
    let inferred: Result<User, str> = json_decode(raw) -- OK: contextual bidirectional inference
}
```

- **Type Functions & Invocation**: Unannotated type function parameters default to sort `Type` (`\T -> ...`). Type function application uses generic angle brackets `<...>`:

```ril
type Nullable = \T -> type<?T>
type PairOf = \T, U -> type<{ first: T, second: U }>

-- Applying type functions via '<...>':
type IntNullable = Nullable<int>          -- Resolves to ?int
type StringIntPair = PairOf<str, int>     -- Resolves to { first: str, second: int }

let value: IntNullable = Some(42)         -- OK: used as concrete type annotation
let pair: StringIntPair = .{ first: "id", second: 101 }
```

### Pure Type Functions and Type Return Privilege

```ril
halt type SafeRecord = \T ->
    if type<T> == type<int> { type<{ val: int, valid: bool }> }
    else { type<{ val: T, valid: bool }> }
type IntRecord = SafeRecord<int>
```

```ril
halt type Identity = \T -> type<T>              -- OK: type-producing function
meta fn size_of<T>(t: type<T>) -> int { byte_size(t) } -- OK: reflection produces a value
halt fn checked_increment(n: int) -> int { n + 1 } -- May panic at int's maximum
-- halt fn yield_once() @Fiber { Fiber::yield() } -- Error [E0821]: halt requires outward purity
-- halt fn forever() { loop {} }                  -- Error [E0820]: uncertified local loop
-- meta let BAD_SUM = 127i8 + 1i8                 -- Error [E0831]: panic during static evaluation
```

| Static definition | Result / restriction |
| :--- | :--- |
| Type declaration/function | May synthesize and return types; effects/capabilities forbidden (`E0335`) |
| `meta fn` | Returns values, never `Type`/`type<...>` (`E0812`); effect/state annotations forbidden (`E0813`) |
| `type<T>` input to `meta fn` | Immutable, non-generative reflection token; cannot synthesize or mutate types |

Both run with empty effect/capability domains. Local `let`, `if`, `match`, pure meta helpers/combinators, and recursion are supported.

Apply [Termination and halt Contracts](#termination-and-halt-contracts) to symbolic computation as well. All meta/type functions retain finite or possibly non-terminating judgments even though their effect and capability domains are empty. `halt type` requires finite symbolic computation, including every reached helper; invalid input or static defects may still fail. Uncertified `halt` computation is `E0820`; type/meta annotation prohibitions retain `E0335`/`E0813`.

Unmarked static loops and recursion remain admissible subject to the static-evaluation budget. Exhaustion rejects that evaluation (`E0811`); it does not certify the underlying definition as terminating. Certified static computations consume the same budget. The run-time `Div` effect is not involved, and `with Div::exhausted()` cannot intercept a static-evaluation diagnostic.

| Static evaluation | Budget / failure |
| :--- | :--- |
| Each root evaluation | Configured positive budget, including certified computations |
| Meta/type function entry, static callback entry, loop iteration | Consume one unit each |
| Next charged step with no budget | `E0811` |
| Alias cycle | Separate `E0313` check |
| Failed `assert` / other panic | Static `E0830` / `E0831` |

- **Custom Diagnostics and Static Panic (`panic`, `E0831`)**: Type functions, pipeline guards, and meta evaluation blocks may emit developer-specified compile-time diagnostics by calling `panic(message)`. Because `panic` returns `never` ($\bot$), it conforms to any expected branch return type sort (including `type<T>`). When evaluated at compile time, `panic(message)` immediately terminates symbolic evaluation and emits diagnostic `E0831: StaticEvaluationPanicError`, presenting `message` as the primary diagnostic description without unwinding noise, attributed to the triggering instantiation site.

```ril
-- Custom diagnostic in pure type function via static panic:
type SizedRecord = \T -> match type<T> {
    type<{ id: int, ..let _ }> -> type<T>,
    _ -> panic("SizedRecord requires a record containing an 'id: int' field"),
}
-- type BadRecord = SizedRecord<str> -- Error [E0831]: panic during static evaluation: SizedRecord requires a record containing an 'id: int' field
-- Meta helper function: value domain computation only (returns int, not type<T>)
meta fn pad_align(size: int, align: int) -> int {
    assert(size >= 0 && align > 0 && (align & (align - 1)) == 0)
    (size + align - 1) & ~(align - 1)
}

-- Meta predicate consuming read-only type token (parametric generic, strictly no 'any'):
meta fn is_compact<T>(t: type<T>) -> bool {
    byte_size(t) <= 16                         -- OK: inspects shape, returns value bool
}

-- Pure type function: monopolizes construction of type<T>
halt type PaddedBuffer = \raw_size: int, T -> {
    let actual_size = pad_align(raw_size, 8)   -- OK: consumes meta fn value output
    if is_compact(type<T>) {                   -- OK: consumes meta predicate
        type<{ inline_data: []T, len: int }>   -- OK: constructs shape
    } else {
        type<{ heap_ptr: int, cap: int }>      -- OK: constructs shape
    }
}

type FastBuf = PaddedBuffer<64, u8>            -- Resolves to { inline_data: []u8, len: int }

-- Static Rejection of Violations:
-- meta fn bad_type_gen() -> type<int> {       -- Error [E0812]: 'meta fn' cannot return 'type<...>'; monopolized by type functions
--     type<int>
-- }
-- halt type BadEffect = \T -> type<T> @Async  -- Error [E0335]: type functions cannot declare algebraic effects
-- meta fn bad_eff() -> int @Io { 0 }          -- Error [E0813]: 'meta fn' cannot declare algebraic effects
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
fn logged_worker(x: int) -> int @Audit { Audit::write("work"); x }

type DispatchMode { Run, Bypass }

fn dispatch_worker<mode: DispatchMode>(f: fn(int) -> int, val: int) -> int {
    match mode {
        DispatchMode::Run    -> f(val),
        DispatchMode::Bypass -> val,
    }
}

fn test_specialization(runtime_mode: DispatchMode) {
    assert(dispatch_worker<DispatchMode::Bypass>(logged_worker, 10) == 10) -- OK: callback is not invoked
    -- dispatch_worker<runtime_mode>(logged_worker, 10)      -- Error [E0814]: a static value is required
}
fn run_logged() -> int @Audit { dispatch_worker<DispatchMode::Run>(logged_worker, 10) }
-- fn hidden_log() -> int { dispatch_worker<DispatchMode::Run>(logged_worker, 10) } -- Error [E0612]
```

| Call family | Permitted calls |
| :--- | :--- |
| Type function | Other type functions and `meta fn`; no run-time `fn` (`E0810`) |
| Run-time function | No type-function invocation (`E0810`) |
| Both phases | Pure arithmetic/comparison, `len`, `assert`, and library operations explicitly declared dual-phase |

Static callbacks capture symbolic constants. Mutable resources, handlers, and ordinary run-time calls have no phase-polymorphic exception. Static budget exhaustion is `E0811`.

| Condition | Invocation effects, state, escape, authority use |
| :--- | :--- |
| Static condition (boolean or pattern arm) | Selected branch only |
| Run-time condition | Both branches' possible obligations |

Both branches still obey syntax, name resolution, and ordinary type compatibility. Type tokens expose no callable-value effects/provenance; no built-in `is_pure` exists.
### Unified Tripartite Introspection

Ril unifies compile-time introspection across all three composite data forms (Records, Sum Types, Tuples) under a single operator pair: `keyof T` and constituent projection `T.(K)`.

```ebnf
MappedRecordType ::= "{" [ "mut" ] "[" PascalCase "in" Expression "]" ":" TypeExpression "}"
MappedTupleType  ::= "(" "[" PascalCase "in" Expression "]" ":" TypeExpression ")"
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
fn dynamic_key(user: User, key: str) {
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
- Fields are read-only unless written `{ mut [K in Expr]: TypeExpr }`; projecting a field type does not copy its mut marker. Records and sums use the same mapping form:
  ```ril
  -- Generic visitor / handler table valid for BOTH records and sum types:
  type SchemaTable = \T -> type<{
      [K in keyof T]: T.(K)
  }>
  ```
- **Mapped Tuples (`( [I in Expr]: TypeExpr )`)**: `Expr` MUST evaluate to compile-time `[]int`. Supplying `[]str` triggers `E0342: InvalidTupleKeySortError`.
- **Single-Element Tuple Prohibition (`E0343`)**: A mapped tuple comprehension evaluated over an index array of length 1 is statically rejected at compile time, preserving the invariant that Ril has no 1-tuples.

```ril
-- Records:
type User = { id: int, name: str, active: bool }
meta let USER_KEYS: []str = keyof User         -- ["active", "id", "name"] (UTF-8 sorted)
type UserId = User.id                          -- int
type UserName = User.("name")                  -- str

type Pick = \T, included: []str -> {
    let valid_keys = keyof T |> Array::filter(\k -> included |> Array::contains(k))
    type<{ [K in valid_keys]: T.(K) }>
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

type EventHandlerTable = \T, R -> type<{
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
    type<(
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

Type functions match quoted types using type-specific products. Bare literals are permitted only in const-argument positions:

```ebnf
TypeMatchExpr    ::= "match" "type" "<" TypeExpression ">" "{" [ TypeMatchArm { "," TypeMatchArm } [ "," ] ] "}"
TypeMatchArm     ::= TypePattern { "|" TypePattern } [ "if" Expression ] "->" Expression
TypePattern      ::= "type" "<" TypePatternInner ">" | "_"
TypePatternInner ::= RigidNominalPattern | TypeTuplePattern | TypeRecordPattern
                   | ArrayPattern | MapPattern | PrimitivePattern | LiteralPattern | Wildcard | "let" ( PascalCase | Wildcard )
RigidNominalPattern ::= QualifiedName [ "<" TypePatternInner { "," TypePatternInner } [ "," ] ">" ]
PrimitivePattern ::= PrimitiveType
ArrayPattern    ::= "[" [ Expression ] "]" TypePatternInner
MapPattern      ::= "[" TypePatternInner ":" TypePatternInner "]"
TypeRecordPattern ::= "{" [ TypePatternField { "," TypePatternField } [ "," TypeRestPattern ] [ "," ] ] "}"
TypePatternField ::= [ "mut" ] FieldLabel ":" TypePatternInner
TypeTuplePattern ::= "(" ")" | "(" TypePatternInner "," ( TypeRestPattern | TypePatternInner { "," TypePatternInner } [ "," TypeRestPattern ] [ "," ] ) ")"
TypeRestPattern ::= ".." "let" PascalCase
```

- **Scoped Pattern Variables (`let U`)**: A `let U` binder inside `type<P>` introduces an immutable type variable scoped strictly to the arm's guard and RHS expression. `U` MUST be `PascalCase` (`E0101`).
- **Linearity Invariant**: Pattern variables MUST be linear; repeating the same identifier within a pattern branch is statically rejected (`E0347: DuplicatePatternBindingError`). Multi-position equality is asserted via explicit guards (`if type<A> == type<B>`).
- **Tuple Rest**: A type-pattern rest is a tuple type of the remaining components; an empty rest is unit. A one-component rest cannot form a tuple and fails that pattern, allowing the next arm to match. It is not silently coerced to its component type.
- **Rigid Application Head (`E0306`)**: Require a known rigid type constructor; no head binding or inverse type-function matching. Transparent aliases may expand. Primitive/structural patterns and whole-type `_`/`let U` remain legal.

```ril
-- Deep Recursive Unwrapping of Container / Fallible Types:
type UnwrapAll = \T -> match type<T> {
    type<Result<let OkVal, let _>> -> UnwrapAll<OkVal>,
    type<Option<let SomeVal>>      -> UnwrapAll<SomeVal>,
    _                              -> type<T>,
}

-- Element Extraction from Collections:
halt type ElementOf = \T -> match type<T> {
    type<[]let E>        -> type<E>,
    type<Set<let E>>     -> type<E>,
    type<[let _: let V]> -> type<V>,
    _                    -> type<never>,
}

-- Tuple Destructuring:
halt type DeconstructTuple = \T -> match type<T> {
    type<(let Head, ..let Tail)> -> type<{ head: Head, tail: Tail }>,
    _                            -> type<never>,
}

type Nested = Option<Result<int, str>>
type Unwrapped = UnwrapAll<Nested>             -- int
-- UnwrapAll uses the evaluation budget: recursive type graphs need not have a finite wrapper depth.
type Elem = ElementOf<[]str>                   -- str
type HeadTail = DeconstructTuple<(u8, i32, f64)>-- { head: u8, tail: (i32, f64) }

-- Rejection of Non-Rigid Type Patterns (E0306):
-- type BadPattern = \T -> match type<T> {
--     type<(let M)<let U>> -> type<U>,         -- Error [E0306]: rigid type pattern cannot bind constructor '(let M)' as a higher-kinded pattern variable
--     _                    -> type<never>,
-- }
```

### Static Parameter Sorts and Adaptation Rules

Type functions accept the following parameter sorts and constraints:

- **Bare Types (`\T` or `\T: Type`)**: Accepts static type expressions. Unannotated parameters default to sort `Type`.
- **Const Values (`\param: ValueType`)**: Accepts compile-time known constants (literals, `meta let`, statically foldable expressions). Passing runtime variables raises `E0814`.
- **Bounded Structural Types (`\T: { id: int, ..R }`) and Static Keys (`\K: keyof T`)**: Structural bounds constrain types; keyof bounds constrain static key values. These are distinct sorts even though both use PascalCase binders.
- **Higher-Kinded Constructors (`\M: Type -> Type`)**: Enforces constructor kind arity (`E0306`).
- **Default Sort Arguments**: Type function parameters support default expressions conforming to their sort: `\T = u8`, `\cap: int = 1024`. Default arguments follow the Telescopic scoping and trailing rules ([Generic Parameters, Defaults, and Value Sorts](#generic-parameters-defaults-and-value-sorts)).

```ril
type SchemaV1 = { id: int, name: str }
type SchemaV2 = { id: int, name: str, email: str }

type VersionedSchema = \version: int -> match version {
    1 -> type<SchemaV1>,
    2 -> type<SchemaV2>,
    _ -> type<never>,
}

type ActivePayload = VersionedSchema<2>        -- SchemaV2

type PickField = \T: { ..R }, K: keyof T -> type<T.(K)>
type UserName = PickField<SchemaV1, "name">    -- str

type Wrapper = \M: Type -> Type, T -> type<M<T>>
type OptInt = Wrapper<Option, int>             -- Option<int>
```

### Compile-Time Execution and Layout Cooperation

```ebnf
MetaLetDecl      ::= "meta" "let" ( ScreamingSnakeCase | "_" ) [ ":" TypeExpression ] "=" Expression
MetaFnDecl       ::= [ "pub" ] "meta" "fn" SnakeCase [ GenericParams ] "(" [ ParameterList ] ")" ReturnType Block
```

`meta let` and `meta fn` evaluate in the pure static domain. Results can be used as immutable run-time constants. Type functions can consume these values to select shapes. Arithmetic on sizes follows the ordinary integer rules.

A run-time value-expression read of a module-level meta constant retains its named source obligation under [External State Tracking](#external-state-tracking). Static/type-domain reads have no such run-time obligation.

```ril
meta let ANSWER = 42
fn answer() -> int &{ANSWER} { ANSWER }
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
        type<{ inline_data: []u8, len: int }>
    } else {
        type<{ heap_ptr: int, capacity: int, len: int }>
    }
meta let CAPACITY = align_to(60, 16)
type Buffer = BufferShape<CAPACITY>
meta let _ = assert(CAPACITY == 64)
-- meta let _ = assert(CAPACITY == 32) -- Error [E0830]: failed static assertion
```

Shape declarations promise no packed order, offsets, pointer size, or external binary layout.

```ril
-- Language-defined static declaration exposed by the prelude:
-- meta fn byte_size<T>(value: type<T>) -> int
meta let BYTE_SIZE = byte_size(type<u8>)
meta let _ = assert(BYTE_SIZE == 1)
-- let runtime_size = byte_size(type<u8>) -- Error [E0810]: query requires static evaluation
```

| `byte_size` contract | Rule |
| :--- | :--- |
| Result | Nonnegative `int` size of T's value/handle on the selected abstract target; not its reachable graph |
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

pub fn circle_area(radius: f64) -> f64 &{PI} {
    PI * radius * radius                -- OK: internal access to private 'PI'
}

-- In file: platform/fs.d.ril (External Interface Declaration Unit)
pub type FileHandle                     -- OK: opaque nominal external type
pub fn read_file(path: str) -> Result<[]u8, str> @Fiber -- OK: bodyless leaf-I/O signature

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
fn calculate() {
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
fn start_worker() &{mut active_workers} { active_workers += 1 }

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
pub fn helper() {}                    -- Error [E0903]: executable program lacks its root main
```

An executable program without its required root `main` declaration is `E0903`. A present declaration that does not satisfy the entry contract is `E0904`. An ordinary library module is not required to declare `main`. Duplicate declarations of root `main` retain `E0203`.

Executable programs define one root `main` function. The examples below are alternatives, not two definitions in one program. Prelude print/println have `@Fiber`, and file-I/O examples use the corresponding leaf-I/O contract:

```ril
pub fn main() -> () @Fiber {
    println("Hello, Ril!")
}

-- Alternative complete fallible executable root:
use ril/file
pub fn main() -> Result<(), str> @Fiber {
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
-- fn main() {}                        -- Error [E0904]: entry must be public
-- pub fn main(value: int) {}          -- Error [E0904]: entry has a parameter
-- pub fn main<T>() {}                 -- Error [E0904]: entry has a generic parameter
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
assert(original == [1, 2, 3] && len(detached) == 4)
let snapshot: Immut<[]int> = clone_immut(detached)
let revised = .{ theme: "dark" } |> derive \mut draft -> {
    draft.theme = "light"
}
assert(revised.theme == "light" && len(snapshot) == 4)
let count = len([1, 2, 3])
println("Count: {count}")
```

The prelude is an ambient lexical scope enclosing every Ril compilation unit. Its declarations are accessible without explicit import statements. Local declarations may shadow prelude names; within the same scope, duplicate declarations remain `E0203`. Shadowing does not alter built-in syntax, compiler intrinsics, or declaration identities required by language-defined operators.

Primitive type spellings (`int`, `str`, `bool`, etc.), `?T`, collection type syntax (`[]T`, `[K: V]`), and built-in system effect identities (`Fiber`, `Concurrent`, `Async`, `Div`) are language constructs, not imported prelude declarations.

#### Built-in Foundational Operations

Ril defines the following built-in foundational operations directly in the language prelude:

| Operation | Signature | Effects | Phase | Complexity | Contract |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `len` | `len(value) -> int` | Pure | Dual-phase | $O(1)$ / $O(n)$ text | Count of elements, entries, bytes, or Unicode scalars |
| `inner` | `inner(wrapper) -> T` | Pure | Runtime | $O(1)$ | Unwraps a nominal wrapper to its underlying payload; unit nominal yields `()` |
| `clone` | `clone(value) -> T` | Pure | Runtime | $O(\text{graph})$ | Deep isolated ordinary graph copy; preserves internal aliases and cycles |
| `clone_immut` | `clone_immut(value) -> Immut<T>` | Pure | Runtime | $O(\text{graph})$ | Independent deeply immutable snapshot |
| `derive` | `derive(base, recipe) -> T` | Forwards recipe | Runtime | $O(\text{affected})$ | Functional update on immutable value via confined mutable draft |
| `byte_size` | `meta fn byte_size<T>(value: type<T>) -> int` | Pure | Static only | $O(1)$ | Size in bytes of $T$'s value/handle on abstract target |
| `type_name` | `meta fn type_name<T>(value: type<T>) -> str` | Pure | Static only | $O(\text{len})$ | Canonical string representation of $T$ for static diagnostics |
| `panic` | `panic(message: str) -> never` | Defect | Dual-phase | Finite | Initiates panic unwinding at runtime; halts compile-time evaluation with E0831 |
| `assert` | `assert(condition: bool, message: str = "assertion failed") -> ()` | Defect | Dual-phase | $O(1)$ | Panics on false condition; compile-time failure is `E0830` |
| `print` | `print(text: str) -> () @Fiber` | `@Fiber` | Runtime | $O(\text{len})$ | Writes UTF-8 text to standard output without trailing newline |
| `println` | `println(text: str) -> () @Fiber` | `@Fiber` | Runtime | $O(\text{len})$ | Writes UTF-8 text followed by one LF byte (`\n`) to standard output |

#### Normative Rules for Built-in Operations

- **Length Invariant (`len`)**:
  - `len` is a pure, dual-phase built-in operation admitted in both runtime and static contexts.
  - For `str`, returns the total number of Unicode scalar values (code points), matching `s[a..b]` scalar indexing.
  - For `bytes`, returns the byte count in $O(1)$ time.
  - For arrays (`[]T`), returns the element count in $O(1)$ time.
  - For maps (`[K: V]`), returns the number of key-value pairs in $O(1)$ time.
  - For sets (`Set<T>`), returns the number of unique elements in $O(1)$ time.
- **Unwrapping Invariant (`inner`)**:
  - Unwraps nominal type wrappers to their underlying declared representation ([Nominal Type Wrappers](#nominal-type-wrappers)).
  - Single-payload nominal wrapper `type UserId(int)` unwraps to its payload (`int`). Unit nominal wrapper `type Marker` unwraps to `()`.
  - Nominal abstraction boundaries remain sealed across modules; `inner` cannot bypass opaque module access restrictions.
- **Graph Isolation Invariants (`clone`, `clone_immut`)**:
  - `clone` creates an independent, isolated copy of an ordinary reachable graph, severing writable storage from the source while preserving internal aliases, shared references, and cyclic structures ([Deep Immutability](#deep-immutability)).
  - `clone_immut` creates an independent, deeply immutable `Immut<T>` snapshot from an eligible value or view.
  - Non-clonable entities (retained closure environments, live tasks, unique receivers, and scoped resources) cannot be cloned through views or wrappers (`E0530`).
  - Cloning a channel `Sender` obeys the channel endpoint resource contract and requires `@Fiber`.
  - Copying costs $O(\text{graph})$ for the reachable ordinary graph inspected and copied; no storage-sharing guarantee is made for mutable copies.
- **Functional Update Invariant (`derive`)**:
  - Confines mutation to a temporary draft within the recipe closure (`\mut draft -> ...`), returning a new immutable value of the same type and qualifier ([Functional Updates via Derive](#functional-updates-via-derive)).
  - Rejects non-immutable input targets (`E0536`).
  - Traps escaping draft references (`E0607`).
  - Forwards recipe algebraic effects and external state obligations; discharges draft-local writes.
- **Static Layout Query (`byte_size`)**:
  - `meta fn byte_size<T>(value: type<T>) -> int` queries the non-negative size in bytes of $T$'s value or handle representation on the selected abstract target ([Compile-Time Execution and Layout Cooperation](#compile-time-execution-and-layout-cooperation)).
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
  - Lexical declarations in inner scopes may shadow prelude names. A local binding named `clone`, `len`, `assert`, etc., shadows the prelude identifier.
  - A locally defined function named `clone` does not acquire the prelude's freshness and copying guarantees (`E0522`).

### Mandatory Inspection of Fallible Results

```ril
fn save_profile(user_id: int) -> Result<(), str> {
    if user_id <= 0 { Err("invalid id") } else { Ok() }
}

fn process_request(id: int) -> Result<(), str> @Fiber {
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
| **`E0306`** | [`KindMismatchError`](#structural-type-pattern-matching) |
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
| **`E0401`** | [`ValueTypeMutableBorrowError`](#parameter-modes-caller-obligations-and-defaults) |
| **`E0402`** | [`ValueTypePinnedMutError`](#value-types) |
| **`E0403`** | [`VarParameterProhibitedError`](#parameter-modes-caller-obligations-and-defaults); [Effect Handlers](#effect-handlers) |
| **`E0404`** | [`MutableParameterDefaultProhibitedError`](#default-parameters-and-named-arguments) |
| **`E0405`** | [`MissingMutableArgumentMarkerError`](#parameter-modes-caller-obligations-and-defaults) |
| **`E0406`** | [`InvalidArgumentModeError`](#parameter-modes-caller-obligations-and-defaults); [Effect Handlers](#effect-handlers) |
| **`E0407`** | [`CallableParameterModeMismatchError`](#parameter-modes-caller-obligations-and-defaults) |
| **`E0408`** | [`InvalidDefaultParameterReferenceError`](#default-parameters-and-named-arguments) |
| **`E0409`** | [`ImpureParameterDefaultError`](#default-parameters-and-named-arguments) |
| **`E0410`** | [`InvalidMutableArgumentTargetError`](#parameter-modes-caller-obligations-and-defaults) |

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
| **`E0530`** | [`IllegalCapabilityCloneImmutError`](#deep-immutability) |
| **`E0531`** | [`ImmutableTargetViewError`](#live-view-bindings) |
| **`E0532`** | [`ReassignableScopedResourceError`](#scoped-resource-bindings) |
| **`E0533`** | [`AliasedNarrowingHazardError`](#flow-sensitive-type-narrowing) |
| **`E0534`** | [`HazardErasureProhibitedError`](#callable-contracts); [Closures, Factory Signatures, and Lexical Environments](#closures-factory-signatures-and-lexical-environments) |
| **`E0535`** | [`NonImmutableBindingError`](#immutable-bindings) |
| **`E0536`** | [`NonImmutableDeriveInputError`](#functional-updates-via-derive) |
| **`E0537`** | [`LiveSliceInvalidationError`](#range-and-slicing-expressions) |
| **`E0538`** | [`InvalidStateSourceGroupError`](#state-groups-and-captured-layers) |
| **`E0539`** | [`InvalidStateContractReferenceError`](#named-function-state-contract-references) |
| **`E0540`** | [`EndedOperationLoanAccessError`](#effect-handlers) |
| **`E0541`** | [`InvalidScopedCleanupContractError`](#scoped-resource-bindings) |
| **`E0542`** | [`NonHigherOrderEmptyRowError`](#callable-contracts) |

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
| **`E0816`** | [`RuntimeTypeQuotationProhibitedError`](#static-type-values-and-type-quotation) |
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

## Advisory Warnings

```ril
fn example(unused_parameter: int) -> int { -- Warning [W0001]: parameter is never used
    let unused_local = 1              -- Warning [W0001]: local binding is never used
    let _intentional = 2              -- OK: intentionally unused
    0
}
```

```ril
-- Complete library module; push is neither used nor re-exported.
use ril/array::{push}                  -- Warning [W0002]: unused private import
pub fn answer() -> int { 42 }
```

```ril
fn finish() {
    return
    let _unreachable = 2              -- Warning [W0003]: preceding return cannot complete normally
}
```

| Code | Diagnostic Name | Advisory Condition |
| :---: | :--- | :--- |
| **`W0001`** | `UnusedReadOnlyBindingWarning` | Read-only local binding or parameter has no use in its scope |
| **`W0002`** | `UnusedPrivateImportWarning` | A privately imported binding is neither referenced nor publicly re-exported |
| **`W0003`** | `UnreachableStatementWarning` | Sequential executable statement follows an unconditional control transfer or an expression of type never in the same statement sequence |

Implementations MAY report these conditions; absence of a warning is not a conformance failure. Warnings do not reject otherwise valid programs, discharge semantic obligations, or suppress static errors. Their names and conditions distinguish them from the mandatory `E` diagnostics; presentation and wording remain unspecified. This section adds no warning-control syntax.

- `W0001` excludes `_` discards, names beginning with the permitted suppressing underscore, mutable authorities, and scoped resources used by implicit cleanup. Reads, captures, and passing a value are uses; unused-result duties remain independent. Only local bindings and parameters are covered, not externally usable public declarations.
- `W0002` applies to the actual imported binding, including aliases or namespace bindings. A reference through its imported name counts as use. Public re-exports are excluded. For a private glob import, a diagnostic may identify unused imported bindings without declaring the module itself inaccessible.
- `W0003` describes sequential unreachability after `return`, `last`, `next`, or another expression of type `never`. Resumption is not unconditionally terminating in general. An unreachable statement still obeys applicable static rules. This warning does not change static-boolean branch pruning or the exhaustive-pattern rules, and does not require proving arbitrary conditions constant.
- Unexercised mutable authority remains `E0527`, abandoned fallible results remain `E0720`, and unreachable match arms remain `E0304`. A warning cannot replace any of these errors.
